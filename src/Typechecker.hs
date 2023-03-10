module Typechecker (typecheck) where

import Control.Monad (when, zipWithM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT, mapExceptT, runExceptT, throwE)
import Control.Monad.Trans.Reader (Reader, asks, local, runReader)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, mapStateT, put)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
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
  , terms :: HashMap Name (Core.Name, Type)
  }

instance Semigroup Env where
  Env xs ys <> Env xs' ys' = Env (xs <> xs') (ys <> ys')

instance Monoid Env where
  mempty = Env mempty mempty

terms :: [(Name, (Core.Name, Type))] -> Env
terms ts =
  Env
    { types = HashMap.empty
    , terms = HashMap.fromList ts
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

newtype Check a = Check (ExceptT Error (StateT Core.Tag (Reader Context)) a)
  deriving newtype (Functor, Applicative, Monad)

runCheck :: Context -> Core.Tag -> Check a -> Either Error a
runCheck ctx tag (Check x) = runReader (evalStateT (runExceptT x) tag) ctx

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

getVar :: Name -> Check (Core.Name, Type)
getVar name = do
  env <- Check (lift (lift (asks (.env.terms))))
  case HashMap.lookup name env of
    Nothing -> typeError (UnboundVariable name)
    Just ty -> pure ty

nextName :: Check Core.Tag
nextName = Check do
  x <- lift get
  lift (put (Core.incTag x))
  pure x

typecheck :: [Expr] -> Either Error [Core.Expr]
typecheck xs = runCheck ctx Core.zeroTag do
  (ss, x, _) <- block xs
  pure (ss ++ [x])
  where
    ctx =
      Context
        { env =
            terms
              [ ("lengthInt", (Core.Intrinsic (Core.ArrayLength TInt), TFunction [TArray TString] TInt))
              , ("toString", (Core.Intrinsic (Core.ToString TInt), TFunction [TInt] TString))
              , ("print", (Core.Intrinsic Core.WriteStdout, TFunction [TString] TUnit))
              , ("readLine", (Core.Intrinsic Core.ReadStdinLine, TFunction [] TUnit))
              ]
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
    pure (Core.Loop cond' loop, Left mempty)
  For name ty arr body -> do
    arr' <- check (TArray ty) arr
    ix <- nextName
    arr'' <- nextName
    len <- nextName
    el <- nextName
    (body', _) <- withEnv (terms [(name, (Core.Name el, ty))]) (infer body)
    let prelude =
          [ Core.Decl ix (Core.Int 0)
          , Core.Decl arr'' arr'
          , Core.Decl len (Core.Call (Core.Var (Core.Intrinsic (Core.ArrayLength ty))) [var arr''])
          ]
        header =
          [ Core.Decl el (Core.Call (Core.Var (Core.Intrinsic (Core.ReadArray ty))) [var arr'', var ix])
          , Core.Assign ix (Core.Call (Core.Var (Core.Intrinsic (Core.Arith Core.Plus Core.NInt))) [var ix, Core.Int 1])
          ]
        loop = case body' of
          Core.Block ss x -> header ++ ss ++ [x]
          _ -> header ++ [body']
        cond = Core.Call (Core.Var (Core.Intrinsic (Core.Compare Core.Lt Core.NInt))) [var ix, var len]
    let while = Core.Block (prelude ++ [Core.Loop cond loop]) Core.Unit
    pure (while, Left mempty)
  Decl name ty body -> do
    body' <- check ty body
    name' <- nextName
    pure (Core.Decl name' body', Left (terms [(name, (Core.Name name', ty))]))
  Fun name params retTy body -> do
    let ty = TFunction (snd <$> params) retTy
    name' <- nextName
    let env = terms [(name, (Core.Name name', ty))]
    (f, _) <- withEnv env (fun params retTy body)
    pure (Core.Decl name' f, Left env)
  Alias _name _body -> _aliasNotImplemented
  Assign mop target value -> do
    tgt <- assignable target
    (assign, ty) <- case tgt of
      NonAssignable -> typeError InvalidAssignmentTarget
      Reassign ty n -> pure $ (Left n, ty)
      MutateArray ty arr ix ->
        pure
          ( Right
              ( arr
              , \x -> Core.Call (Core.Var (Core.Intrinsic (Core.ReadArray ty))) [x, ix]
              , \x v -> Core.Call (Core.Var (Core.Intrinsic (Core.WriteArray ty))) [x, ix, v]
              )
          , ty
          )
      MutateObject ty obj field ->
        pure
          ( Right
              ( obj
              , \x -> Core.Call (Core.Var (Core.Intrinsic (Core.ReadObject field))) [x]
              , \x v -> Core.Call (Core.Var (Core.Intrinsic (Core.WriteObject field))) [x, v]
              )
          , ty
          )
    value' <- check ty value
    s <- case mop of
      Nothing -> case assign of
        Left n -> pure (Core.Assign n value')
        Right (obj, _, setVal) -> do
          r <- nextName
          let ss = [Core.Decl r obj, setVal (var r) value']
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
        let combine x y = Core.Call (Core.Var (Core.Intrinsic intrinsic)) [x, y]
        ss <- case assign of
          Left n -> do
            r <- nextName
            pure [Core.Decl r (var n), Core.Assign n (combine (var r) value')]
          Right (obj, getVal, setVal) -> do
            r0 <- nextName
            r1 <- nextName
            pure [Core.Decl r0 obj, Core.Decl r1 (getVal (var r0)), setVal (var r0) (combine (var r1) value')]
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
    pure (Core.Array ty xs', TArray ty)
    where
      go [] = pure ([], TUnit)
      go (y : ys) = do
        (y', ty) <- infer y
        ys' <- traverse (check ty) ys
        pure (y' : ys', ty)
  Object fields -> do
    (fields', fieldTypes) <- go fields
    let ty = TObject fieldTypes
    pure (Core.Object fields', ty)
    where
      go [] = pure ([], [])
      go ((name, value) : fs) = do
        (value', ty) <- infer value
        (fs', ts) <- go fs
        pure ((name, value') : fs', (name, ty) : ts)
  Lambda params retTy body -> fun params retTy body
  Var name -> do
    (name', ty) <- getVar name
    pure (Core.Var name', ty)
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
      TArray elemTy -> pure (Core.Call (Core.Var (Core.Intrinsic (Core.ReadArray elemTy))) [arr', ix'], elemTy)
      _ -> typeError (UnificationError UnknownArray arrTy)
  Access obj field -> do
    (obj', objTy) <- infer obj
    case objTy of
      TObject fields
        | Just fieldTy <- lookup field fields ->
            pure (Core.Call (Core.Var (Core.Intrinsic (Core.ReadObject field))) [obj'], fieldTy)
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
      pure (Core.Call (Core.Var (Core.Intrinsic Core.StringAppend)) [x', y'], TString)
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
  pure (Core.Call (Core.Var (Core.Intrinsic (f n))) [x'', y''], t)

arithOp :: Core.Arith -> Expr -> Expr -> Check (Core.Expr, Type)
arithOp op = numOp (Core.Arith op)

compareOp :: Core.Comparison -> Expr -> Expr -> Check (Core.Expr, Type)
compareOp cmp = numOp (Core.Compare cmp)

logicOp :: Core.Logic -> Expr -> Expr -> Check (Core.Expr, Type)
logicOp op x y = do
  (x', tx) <- infer x
  (y', ty) <- infer y
  unify tx TBool
  unify ty TBool
  pure (Core.Call (Core.Var (Core.Intrinsic (Core.Logic op))) [x', y'], TBool)

weakUnify :: (Core.Expr, Type) -> (Core.Expr, Type) -> Check (Core.Expr, Core.Expr, Type)
weakUnify (x, tx) (y, ty) = case (tx, ty) of
  (TInt, TFloat) -> pure (Core.Call (Core.Var (Core.Intrinsic (Core.Cast Core.NInt Core.NFloat))) [x], y, TFloat)
  (TFloat, TInt) -> pure (x, Core.Call (Core.Var (Core.Intrinsic (Core.Cast Core.NInt Core.NFloat))) [y], TFloat)
  _ -> do
    unify tx ty
    pure (x, y, tx)

check :: Type -> Expr -> Check Core.Expr
check expected = \case
  Int x | TFloat <- expected -> pure (Core.Float (fromIntegral x))
  Array [] -> pure (Core.Array expected [])
  x -> do
    (x', actual) <- infer x
    case (expected, actual) of
      (TFloat, TInt) -> pure (Core.Call (Core.Var (Core.Intrinsic (Core.Cast Core.NInt Core.NFloat))) [x'])
      _ -> do
        unify expected actual
        pure x'

fun :: [(Name, Type)] -> Type -> Expr -> Check (Core.Expr, Type)
fun params retTy body = do
  params' <- for params \(param, ty) -> do
    name <- nextName
    pure (param, (name, ty))
  let env = terms ((\(s, (t, ty)) -> (s, (Core.Name t, ty))) <$> params')
  body' <- withReturn retTy (withEnv env (check retTy body))
  let captures = Core.Tag <$> IntSet.toList (free body' IntSet.\\ IntSet.fromList ((\(Core.Tag x) -> x) <$> params''))
      params'' = (\(_, (n, _)) -> n) <$> params'
      ty = TFunction (snd . snd <$> params') retTy
  pure (Core.Lambda captures params'' body', ty)

free :: Core.Expr -> IntSet
free = \case
  Core.Array _ elems -> foldMap free elems
  Core.Object fields -> foldMap (foldMap free) fields
  Core.Var (Core.Name (Core.Tag k)) -> IntSet.singleton k
  Core.Call f args -> free f <> foldMap free args
  Core.Cond cond true false -> free cond <> free true <> free false
  Core.Loop cond body -> free cond <> go Core.Unit body
  Core.Return value -> free value
  Core.Assign (Core.Tag k) value -> IntSet.insert k (free value)
  Core.Block ss x -> go x ss
  _ -> IntSet.empty
  where
    go x = \case
      [] -> free x
      Core.Decl (Core.Tag k) value : ss -> free value <> IntSet.delete k (go x ss)
      s : ss -> free s <> go x ss

data Target
  = NonAssignable
  | Reassign Type !Core.Tag
  | MutateArray Type Core.Expr Core.Expr
  | MutateObject Type Core.Expr Core.Field

assignable :: Expr -> Check Target
assignable = \case
  Var name -> do
    (name', ty) <- getVar name
    pure case name' of
      Core.Intrinsic {} -> NonAssignable
      Core.Name n -> Reassign ty n
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

var :: Core.Tag -> Core.Expr
var = Core.Var . Core.Name
