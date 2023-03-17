module Typechecker (typecheck) where

import Control.Monad (when, zipWithM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT, mapExceptT, runExceptT, throwE)
import Control.Monad.Trans.Reader (Reader, asks, local, runReader)
import Control.Monad.Trans.State.Strict (StateT, get, mapStateT, put, runStateT)
import Data.Bifunctor (first)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.Traversable (for)

import Core qualified
import Syntax

data Error
  = UnboundVariable Name
  | UnificationError Type' Type
  | WrongArity !Int !Int
  | StatementInExpression
  | ToplevelReturn
  | InvalidAssignmentTarget
  | InvalidCompoundAssignment BinOp
  deriving stock (Show)

data Type'
  = Type Type
  | UnknownArray
  | UnknownFunction [Type]
  | UnknownObject Field
  | UnknownNumber
  deriving stock (Show)

data Env = Env
  { types :: HashMap Name Type
  , terms :: HashMap Name (Either Core.Intrinsic Core.Name, Type)
  }

instance Semigroup Env where
  Env xs ys <> Env xs' ys' = Env (xs <> xs') (ys <> ys')

instance Monoid Env where
  mempty = Env mempty mempty

terms :: [(Name, (Core.Name, Type))] -> Env
terms ts =
  Env
    { types = HashMap.empty
    , terms = HashMap.fromList (fmap (first Right) <$> ts)
    }

types :: [(Name, Type)] -> Env
types ts =
  Env
    { types = HashMap.fromList ts
    , terms = HashMap.empty
    }

data Context = Context
  { env :: Env
  , return :: Maybe Type
  }

newtype Check a = Check (ExceptT Error (StateT Core.Name (Reader Context)) a)
  deriving newtype (Functor, Applicative, Monad)

runCheck :: Context -> Int -> Check a -> (Either Error a, Int)
runCheck ctx k (Check x) = runReader (runStateT (runExceptT x) k) ctx

typeError :: Error -> Check a
typeError = Check . throwE

unify :: Type -> Type -> Check ()
unify expected actual | expected == actual = pure ()
unify expected actual = typeError (UnificationError (Type expected) actual)

withEnv :: Env -> Check a -> Check a
withEnv env (Check x) = Check (mapExceptT (mapStateT (local go)) x)
  where
    go ctx = ctx {env = env <> ctx.env}

withReturn :: Type -> Check a -> Check a
withReturn ty (Check x) = Check (mapExceptT (mapStateT (local go)) x)
  where
    go ctx = ctx {return = Just ty}

expectedReturn :: Check (Maybe Type)
expectedReturn = Check (lift (lift (asks (.return))))

getVar :: Name -> Check (Either Core.Intrinsic Core.Name, Type)
getVar name = do
  env <- Check (lift (lift (asks (.env.terms))))
  case HashMap.lookup name env of
    Nothing -> typeError (UnboundVariable name)
    Just ty -> pure ty

nextName :: Check Core.Name
nextName = Check do
  x <- lift get
  lift (put (x + 1))
  pure x

typecheck :: [Expr] -> (Either Error [Core.Expr], Int)
typecheck xs = runCheck ctx 0 do
  (ss, x, _) <- block xs
  pure (ss ++ [x])
  where
    intrinsics =
      [ ("lengthInt", (Left (Core.ArrayLength TInt), TFunction [TArray TString] TInt))
      , ("toString", (Left (Core.ToString TInt), TFunction [TInt] TString))
      , ("print", (Left Core.WriteStdout, TFunction [TString] TUnit))
      , ("readLine", (Left Core.ReadStdinLine, TFunction [] TUnit))
      ]
    ctx =
      Context
        { env = Env {terms = HashMap.fromList intrinsics, types = HashMap.empty}
        , return = Nothing
        }

block :: [Expr] -> Check ([Core.Expr], Core.Expr, Type)
block = \case
  [] -> pure ([], Core.Unit, TUnit)
  [s] -> do
    (s', r) <- stmt s
    pure case r of
      Left _ -> ([s'], Core.Unit, TUnit)
      Right ty -> ([], s', ty)
  s : ss -> do
    (s', r) <- stmt s
    (ss', x, ty) <- case r of
      Left env -> withEnv env (block ss)
      Right _ -> block ss
    pure (s' : ss', x, ty)

stmt :: Expr -> Check (Core.Expr, Either Env Type)
stmt = \case
  Return retVal -> do
    retTy <- expectedReturn
    ret <- case retTy of
      Nothing -> typeError ToplevelReturn
      Just ty
        | Just val <- retVal -> check ty val
        | TUnit <- ty -> pure (Core.Return Core.Unit)
        | otherwise -> typeError (UnificationError (Type ty) TUnit)
    pure (ret, Left mempty)
  While cond body -> do
    cond' <- check TBool cond
    (body', _) <- infer body
    let loop = case body' of
          Core.Block ss x -> ss ++ [x]
          _ -> [body']
    pure (Core.While cond' loop, Left mempty)
  For name ty arr body -> do
    arr' <- check (TArray ty) arr
    ix <- nextName
    arr'' <- nextName
    len <- nextName
    el <- nextName
    (body', _) <- withEnv (terms [(name, (el, ty))]) (infer body)
    let prelude =
          [ Core.Decl ix (Core.Int 0)
          , Core.Bind arr'' arr'
          , Core.Bind len (Core.Call (Core.Intrinsic (Core.ArrayLength ty)) [Core.Val arr''])
          ]
        header =
          [ Core.Decl el (Core.Call (Core.Intrinsic (Core.ReadArray ty)) [Core.Val arr'', Core.Var ix])
          , Core.Assign ix (Core.Call (Core.Intrinsic (Core.Arith Core.Plus Core.NInt)) [Core.Var ix, Core.Int 1])
          ]
        loop = case body' of
          Core.Block ss x -> header ++ ss ++ [x]
          _ -> header ++ [body']
        cond = Core.Call (Core.Intrinsic (Core.Compare Core.Lt Core.NInt)) [Core.Var ix, Core.Val len]
    let while = Core.Block (prelude ++ [Core.While cond loop]) Core.Unit
    pure (while, Left mempty)
  Decl name ty body -> do
    body' <- check ty body
    name' <- nextName
    pure (Core.Decl name' body', Left (terms [(name, (name', ty))]))
  Fun name params retTy body -> do
    let ty = TFunction (snd <$> params) retTy
    name' <- nextName
    let env = terms [(name, (name', ty))]
    (f, _) <- withEnv env (fun params retTy body)
    pure (Core.Decl name' f, Left env)
  Alias _name _body -> _aliasNotImplemented
  Assign mop target value -> do
    tgt <- assignable target
    (assign, ty) <- case tgt of
      NonAssignable -> typeError InvalidAssignmentTarget
      Reassign ty n -> pure (Left n, ty)
      MutateArray ty arr ix ->
        pure
          ( Right
              ( arr
              , \x -> Core.Call (Core.Intrinsic (Core.ReadArray ty)) [x, ix]
              , \x v -> Core.Call (Core.Intrinsic (Core.WriteArray ty)) [x, ix, v]
              )
          , ty
          )
      MutateObject ty obj field ->
        pure
          ( Right
              ( obj
              , \x -> Core.Call (Core.Intrinsic (Core.ReadObject field)) [x]
              , \x v -> Core.Call (Core.Intrinsic (Core.WriteObject field)) [x, v]
              )
          , ty
          )
    value' <- check ty value
    s <- case mop of
      Nothing -> case assign of
        Left n -> pure (Core.Assign n value')
        Right (obj, _, setVal) -> do
          r <- nextName
          let ss =
                [ Core.Bind r obj
                , setVal (Core.Val r) value'
                ]
          pure (Core.Block ss Core.Unit)
      Just op -> do
        intrinsic <- case op of
          Plus -> arithIntrinsic Core.Plus ty
          Minus -> arithIntrinsic Core.Minus ty
          Times -> arithIntrinsic Core.Times ty
          Divide -> arithIntrinsic Core.Divide ty
          Mod
            | TInt <- ty -> pure Core.Modulo
            | otherwise -> typeError (UnificationError (Type TInt) ty)
          _ -> typeError (InvalidCompoundAssignment op)
        let combine x y = Core.Call (Core.Intrinsic intrinsic) [x, y]
        ss <- case assign of
          Left n -> do
            r <- nextName
            pure
              [ Core.Bind r (Core.Var n)
              , Core.Assign n (combine (Core.Val r) value')
              ]
          Right (obj, getVal, setVal) -> do
            r <- nextName
            pure
              [ Core.Bind r obj
              , setVal (Core.Val r) (combine (getVal (Core.Val r)) value')
              ]
        pure (Core.Block ss Core.Unit)
    pure (s, Left mempty)
  s -> fmap Right <$> infer s

arithIntrinsic :: Core.Arith -> Type -> Check Core.Intrinsic
arithIntrinsic op ty = do
  n <- case ty of
    TInt -> pure Core.NInt
    TFloat -> pure Core.NFloat
    _ -> typeError (UnificationError UnknownNumber ty)
  pure (Core.Arith op n)

infer :: Expr -> Check (Core.Expr, Type)
infer = \case
  Return {} -> typeError StatementInExpression
  Decl {} -> typeError StatementInExpression
  Fun {} -> typeError StatementInExpression
  Alias {} -> typeError StatementInExpression
  Assign {} -> typeError StatementInExpression
  While {} -> typeError StatementInExpression
  For {} -> typeError StatementInExpression
  Unit -> pure (Core.Unit, TUnit)
  Bool b -> pure (Core.Bool b, TBool)
  Int x -> pure (Core.Int x, TInt)
  Float x -> pure (Core.Float x, TFloat)
  String s -> pure (Core.String s, TString)
  Array xs -> do
    (xs', ty) <- go xs
    arr <- nextName
    let fill x ix = Core.Call (Core.Intrinsic (Core.WriteArray ty)) [Core.Val arr, Core.Int ix, x]
        fills = zipWith fill xs' [0 ..]
        alloc = Core.Bind arr (Core.Call (Core.Intrinsic (Core.NewArray ty)) [Core.Int (length xs)])
    pure (Core.Block (alloc : fills) (Core.Val arr), TArray ty)
    where
      go [] = pure ([], TUnit)
      go (y : ys) = do
        (y', ty) <- infer y
        ys' <- traverse (check ty) ys
        pure (y' : ys', ty)
  Object fields -> do
    (fields', fieldTypes) <- go fields
    obj <- nextName
    let insert (field, value) = Core.Call (Core.Intrinsic (Core.WriteObject field)) [Core.Val obj, value]
        inserts = insert <$> fields'
        alloc = Core.Bind obj (Core.Call (Core.Intrinsic Core.NewObject) [])
    pure (Core.Block (alloc : inserts) (Core.Val obj), TObject fieldTypes)
    where
      go [] = pure ([], [])
      go ((name, value) : fs) = do
        (value', ty) <- infer value
        (fs', ts) <- go fs
        pure ((name, value') : fs', (name, ty) : ts)
  Lambda params retTy body -> fun params retTy body
  Var name -> do
    (name', ty) <- getVar name
    let var = case name' of
          Left x -> Core.Intrinsic x
          Right n -> Core.Var n
    pure (var, ty)
  Call f args -> do
    (f', ty) <- infer f
    case ty of
      TFunction params retTy -> do
        let paramCount = length params
            argCount = length args
        when (paramCount /= argCount) do
          typeError (WrongArity paramCount argCount)
        args' <- zipWithM check params args
        pure (Core.Call f' args', retTy)
      _ -> do
        argTys <- fmap snd <$> traverse infer args
        typeError (UnificationError (UnknownFunction argTys) ty)
  Subscript arr ix -> do
    ix' <- check TInt ix
    (arr', arrTy) <- infer arr
    case arrTy of
      TArray elemTy -> pure (Core.Call (Core.Intrinsic (Core.ReadArray elemTy)) [arr', ix'], elemTy)
      _ -> typeError (UnificationError UnknownArray arrTy)
  Access obj field -> do
    (obj', objTy) <- infer obj
    case objTy of
      TObject fields
        | Just fieldTy <- lookup field fields ->
            pure (Core.Call (Core.Intrinsic (Core.ReadObject field)) [obj'], fieldTy)
      _ -> typeError (UnificationError (UnknownObject field) objTy)
  BinOp op x y -> case op of
    Plus -> arithOp Core.Plus x y
    Minus -> arithOp Core.Minus x y
    Times -> arithOp Core.Times x y
    Divide -> arithOp Core.Divide x y
    Mod -> compareOp Core.Lt x y
    Lt -> compareOp Core.Lt x y
    Lte -> compareOp Core.Lte x y
    Neq -> compareOp Core.Neq x y
    Eq -> compareOp Core.Eq x y
    Gte -> compareOp Core.Gte x y
    Gt -> compareOp Core.Gt x y
    And -> logicOp Core.And x y
    Or -> logicOp Core.Or x y
    Append -> do
      (x', tx) <- infer x
      unify tx TString
      (y', ty) <- infer y
      unify ty TString
      pure (Core.Call (Core.Intrinsic Core.StringAppend) [x', y'], TString)
  Cond cond true mfalse -> do
    cond' <- check TBool cond
    case mfalse of
      Nothing -> do
        true' <- check TUnit true
        pure (Core.Cond cond' true' Core.Unit, TUnit)
      Just false -> do
        (true', ty) <- infer true
        false' <- check ty false
        pure (Core.Cond cond' true' false', ty)
  Block xs -> do
    (ss, x, ty) <- block xs
    pure (Core.Block ss x, ty)

numOp :: (Core.Number -> Core.Intrinsic) -> Expr -> Expr -> Check (Core.Expr, Type)
numOp f x y = do
  x' <- infer x
  y' <- infer y
  (x'', y'', t) <- weakUnify x' y'
  n <- case t of
    TInt -> pure Core.NInt
    TFloat -> pure Core.NFloat
    _ -> typeError (UnificationError UnknownNumber t)
  pure (Core.Call (Core.Intrinsic (f n)) [x'', y''], t)

arithOp :: Core.Arith -> Expr -> Expr -> Check (Core.Expr, Type)
arithOp op = numOp (Core.Arith op)

compareOp :: Core.Comparison -> Expr -> Expr -> Check (Core.Expr, Type)
compareOp cmp x y = fmap (const TBool) <$> numOp (Core.Compare cmp) x y

logicOp :: Core.Logic -> Expr -> Expr -> Check (Core.Expr, Type)
logicOp op x y = do
  (x', tx) <- infer x
  (y', ty) <- infer y
  unify tx TBool
  unify ty TBool
  pure (Core.Call (Core.Intrinsic (Core.Logic op)) [x', y'], TBool)

weakUnify :: (Core.Expr, Type) -> (Core.Expr, Type) -> Check (Core.Expr, Core.Expr, Type)
weakUnify (x, tx) (y, ty) = case (tx, ty) of
  (TInt, TFloat) -> pure (Core.Call (Core.Intrinsic (Core.Cast Core.NInt Core.NFloat)) [x], y, TFloat)
  (TFloat, TInt) -> pure (x, Core.Call (Core.Intrinsic (Core.Cast Core.NInt Core.NFloat)) [y], TFloat)
  _ -> do
    unify tx ty
    pure (x, y, tx)

check :: Type -> Expr -> Check Core.Expr
check expected = \case
  Int x | TFloat <- expected -> pure (Core.Float (fromIntegral x))
  Array [] -> pure (Core.Call (Core.Intrinsic (Core.NewArray expected)) [Core.Int 0])
  x -> do
    (x', actual) <- infer x
    case (expected, actual) of
      (TFloat, TInt) -> pure (Core.Call (Core.Intrinsic (Core.Cast Core.NInt Core.NFloat)) [x'])
      _ -> do
        unify expected actual
        pure x'

fun :: [(Name, Type)] -> Type -> Expr -> Check (Core.Expr, Type)
fun params retTy body = do
  params' <- for params \(param, ty) -> do
    name <- nextName
    pure (param, (name, ty))
  let env = terms ((\(s, (t, ty)) -> (s, (t, ty))) <$> params')
  body' <- withReturn retTy (withEnv env (check retTy body))
  let params'' = (\(_, (n, _)) -> n) <$> params'
      ty = TFunction (snd . snd <$> params') retTy
  paramVars <- for params'' \p -> do
    name <- nextName
    pure (name, Core.Decl p (Core.Val name))
  let (paramVals, decls) = unzip paramVars
      body'' = case body' of
        Core.Block ss x -> Core.Block (decls <> ss) x
        _ -> Core.Block decls body'
  pure (Core.Lambda paramVals body'', ty)

data Target
  = NonAssignable
  | Reassign Type !Core.Name
  | MutateArray Type Core.Expr Core.Expr
  | MutateObject Type Core.Expr Core.Field

assignable :: Expr -> Check Target
assignable = \case
  Var name -> do
    (name', ty) <- getVar name
    pure case name' of
      Left _ -> NonAssignable
      Right n -> Reassign ty n
  Subscript arr ix -> do
    ix' <- check TInt ix
    (arr', arrTy) <- infer arr
    case arrTy of
      TArray ty -> pure (MutateArray ty arr' ix')
      _ -> typeError (UnificationError UnknownArray arrTy)
  Access obj field -> do
    (obj', objTy) <- infer obj
    case objTy of
      TObject fields | Just ty <- lookup field fields -> pure (MutateObject ty obj' field)
      _ -> typeError (UnificationError (UnknownObject field) objTy)
  _ -> pure NonAssignable
