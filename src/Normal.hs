module Normal (
  Name,
  Atom (..),
  Core.Intrinsic (..),
  Expr (..),
  Fun (..),
  Block (..),
  normalize,
) where

import Control.Monad (replicateM)
import Control.Monad.Trans.Accum (AccumT, add, look, runAccumT)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Cont (ContT (..), mapContT)
import Control.Monad.Trans.State.Strict (State, evalState, get, put)
import Control.Monad.Trans.Writer.CPS (runWriterT, tell)
import Data.Foldable (traverse_)
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Prettyprinter (Pretty (..), (<+>))
import Prettyprinter qualified as PP

import Core (Name)
import Core qualified

data Atom
  = Var !Name
  | Unit
  | Bool Bool
  | Int !Int
  | Float !Double
  | String Text

data Expr
  = Lambda !Name [Name] Expr Expr
  | Join !Name (Maybe Name) Expr Expr
  | Closure !Name !Name [Name] Expr
  | Call !Name Atom [Atom] Expr
  | Intrinsic !Name Core.Intrinsic [Atom] Expr
  | Decl !Name Atom Expr
  | Assign !Name Atom Expr
  | Deref !Name !Name Expr
  | Cond Atom Expr Expr
  | Branch Atom !Name !Name
  | Jump !Name (Maybe Atom)
  | Return Atom
  | Halt

type Norm r = ContT r (AccumT (Map Core.Intrinsic Name) (State Int))

newName :: State Int Name
newName = do
  name <- get
  put (name + 1)
  pure name

normalize :: Int -> [Core.Expr] -> NonEmpty Fun
normalize n ss = evalState go n
  where
    go = do
      (x, intrinsics) <- runAccumT (runContT (traverse_ norm ss) (\_ -> pure Halt)) Map.empty
      intrinsicFuns <- traverse (uncurry intrinsic) (Map.toList intrinsics)
      funs <- hoist x
      pure (funs `NE.appendList` intrinsicFuns)

norm :: Core.Expr -> Norm Expr Atom
norm = \case
  Core.Unit -> pure Unit
  Core.Bool b -> pure (Bool b)
  Core.Int x -> pure (Int x)
  Core.Float x -> pure (Float x)
  Core.String s -> pure (String s)
  Core.Lambda params body -> do
    name <- newName'
    with (Var name) \k -> do
      body' <- runContT (norm body) (pure . Return)
      pure (Lambda name params body' k)
  Core.Intrinsic x -> do
    c <- newName'
    intrinsics <- lift look
    f <- case Map.lookup x intrinsics of
      Just name -> pure name
      Nothing -> do
        name <- newName'
        lift (add (Map.singleton x name))
        pure name
    with (Var c) \k -> pure (Closure c f [] k)
  Core.Val name -> pure (Var name)
  Core.Var name -> do
    x <- newName'
    with (Var x) \k -> pure (Deref x name k)
  Core.Call (Core.Intrinsic x) args -> do
    args' <- traverse norm args
    result <- newName'
    with (Var result) \k -> pure (Intrinsic result x args' k)
  Core.Call f args -> do
    f' <- norm f
    args' <- traverse norm args
    result <- newName'
    with (Var result) \k -> pure (Call result f' args' k)
  Core.Cond cond true false -> do
    cond' <- norm cond
    slot <- newName'
    with (Var slot) \k -> do
      join <- lift newName
      let jump v = pure (Jump join (Just v))
      true' <- runContT (norm true) jump
      false' <- runContT (norm false) jump
      pure (Join join (Just slot) (Cond cond' true' false') k)
  Core.While cond body -> do
    loop <- newName'
    with Unit \k -> do
      body' <- runContT (traverse_ norm body) \_ -> pure (Jump loop Nothing)
      entry <- runContT (norm cond) \b -> pure (Cond b body' k)
      pure (Join loop Nothing (Jump loop Nothing) entry)
  Core.Return value -> do
    value' <- norm value
    with Unit \_ -> pure (Return value')
  Core.Bind name value -> do
    value' <- norm value
    with value' (pure . bind name value')
  Core.Decl name value -> do
    value' <- norm value
    with (Var name) \k -> pure (Decl name value' k)
  Core.Assign name value -> do
    value' <- norm value
    with Unit \k -> pure (Assign name value' k)
  Core.Block ss x -> do
    traverse_ norm ss
    norm x
  where
    newName' = lift (lift newName)
    with x f = mapContT (>>= f) (pure x)
    bindA name value = \case
      Var n | n == name -> value
      x -> x
    bind n v = \case
      Lambda name params body k -> Lambda name params (bind n v body) (bind n v k)
      Join name slot body k -> Join name slot (bind n v body) (bind n v k)
      Closure name f captures k -> Closure name f captures (bind n v k)
      Call name c args k -> Call name (bindA n v c) (bindA n v <$> args) (bind n v k)
      Intrinsic name x args k -> Intrinsic name x (bindA n v <$> args) (bind n v k)
      Decl name value k -> Decl name (bindA n v value) (bind n v k)
      Assign name value k -> Assign name (bindA n v value) (bind n v k)
      Deref name var k -> Deref name var (bind n v k)
      Cond cond true false -> Cond (bindA n v cond) (bind n v true) (bind n v false)
      Branch cond true false -> Branch (bindA n v cond) true false
      Jump join arg -> Jump join (bindA n v <$> arg)
      Return value -> Return (bindA n v value)
      Halt -> Halt

free :: Expr -> IntSet
free = \case
  Lambda name params body k -> bindAll params (free body) <> bind name (free k)
  Closure name _ captures k -> IntSet.fromList captures <> bind name (free k)
  Call name f args k -> freeA f <> foldMap freeA args <> bind name (free k)
  Intrinsic name _ args k -> foldMap freeA args <> bind name (free k)
  Cond cond true false -> freeA cond <> free true <> free false
  Branch cond _ _ -> freeA cond
  Decl name value k -> freeA value <> bind name (free k)
  Assign name value k -> IntSet.insert name (freeA value) <> free k
  Deref name var k -> IntSet.insert var (bind name (free k))
  Join _ Nothing body k -> free body <> free k
  Join _ (Just name) body k -> free body <> bind name (free k)
  Jump _ arg -> foldMap freeA arg
  Return value -> freeA value
  Halt -> mempty
  where
    bind = IntSet.delete
    bindAll names xs = xs IntSet.\\ IntSet.fromList names
    freeA = \case
      Var name -> IntSet.singleton name
      _ -> mempty

data Fun = Fun
  { name :: !Name
  , captures :: [Name]
  , params :: [Name]
  , blocks :: NonEmpty Block
  }

data Block = Block
  { name :: !Name
  , slot :: Maybe Name
  , body :: Expr
  }

hoist :: Expr -> State Int (NonEmpty Fun)
hoist e = do
  (e', (blocks, funs)) <- runWriterT (go e)
  entryName <- newName
  let entry = Block entryName Nothing e'
  mainName <- newName
  let main = Fun mainName [] [] (entry :| blocks)
  pure (main :| funs)
  where
    fun f = tell ([], [f])
    block b = tell ([b], [])
    go = \case
      l@(Lambda name params body k) -> do
        let captures = IntSet.toList (free l)
        (x, (blocks, funs)) <- lift $ runWriterT (go body)
        tell (mempty, funs)
        entryName <- lift newName
        funName <- lift newName
        let entry = Block entryName Nothing x
        fun (Fun funName captures params (entry :| blocks))
        k' <- go k
        pure (Closure name funName captures k')
      Join name slot body k -> do
        k' <- go k
        block (Block name slot k')
        go body
      Cond cond true false -> do
        true' <- go true
        jTrue <- lift newName
        block (Block jTrue Nothing true')
        false' <- go false
        jFalse <- lift newName
        block (Block jFalse Nothing false')
        pure (Branch cond jTrue jFalse)
      Closure name f captures k -> do
        k' <- go k
        pure (Closure name f captures k')
      Call name f args k -> do
        k' <- go k
        pure (Call name f args k')
      Intrinsic name x args k -> do
        k' <- go k
        pure (Intrinsic name x args k')
      Decl name value k -> do
        k' <- go k
        pure (Decl name value k')
      Assign name value k -> do
        k' <- go k
        pure (Assign name value k')
      Deref name var k -> do
        k' <- go k
        pure (Deref name var k')
      brch@Branch {} -> pure brch
      jmp@Jump {} -> pure jmp
      ret@Return {} -> pure ret
      hlt@Halt -> pure hlt

intrinsic :: Core.Intrinsic -> Name -> State Int Fun
intrinsic intr name = do
  let ary = arity intr
  params <- replicateM ary newName
  rs <- replicateM ary newName
  let derefs = foldr (.) id (zipWith Deref rs params)
  entryName <- newName
  res <- newName
  let body = derefs $ Intrinsic res intr (Var <$> rs) $ Return (Var res)
      entry = Block {name = entryName, slot = Nothing, body}
      blocks = NE.singleton entry
  pure Fun {name, params, captures, blocks}
  where
    captures = []
    arity = \case
      Core.Arith {} -> 2
      Core.Modulo {} -> 2
      Core.Cast {} -> 1
      Core.Compare {} -> 2
      Core.Logic {} -> 2
      Core.StringAppend {} -> 2
      Core.NewArray {} -> 1
      Core.ArrayLength {} -> 1
      Core.ReadArray {} -> 2
      Core.WriteArray {} -> 3
      Core.NewObject {} -> 0
      Core.ReadObject {} -> 1
      Core.WriteObject {} -> 2
      Core.ToString {} -> 1
      Core.WriteStdout {} -> 1
      Core.ReadStdinLine {} -> 0

instance Pretty Expr where
  pretty = \case
    Lambda name params body k ->
      PP.vsep
        [ PP.nest 2 $ "fun" <+> "x" <> pretty name <> PP.parens (sep "x" params) <> PP.line <> pretty body
        , pretty k
        ]
    Closure name f captures k ->
      PP.vsep
        [ PP.hsep ["const", "x" <> pretty name, "=", "f" <> pretty f, PP.brackets (sep "x" captures)]
        , pretty k
        ]
    Call name f args k ->
      PP.vsep
        [ PP.nest 2 $ PP.hsep ["const", "x" <> pretty name, "=", pretty f <> PP.parens (sep "" args)]
        , pretty k
        ]
    Intrinsic name x args k ->
      PP.vsep
        [ PP.nest 2 $ PP.hsep ["const", "x" <> pretty name, "=", pretty x <> PP.parens (sep "" args)]
        , pretty k
        ]
    Branch cond true false ->
      PP.hsep ["cond", pretty cond, "j" <> pretty true, "j" <> pretty false]
    Cond cond true false ->
      PP.nest 2 ("if" <+> pretty cond <> PP.line <> pretty true)
        <> PP.line
        <> PP.nest 2 ("else" <> PP.line <> pretty false)
    Decl name value k -> PP.vsep [PP.hsep ["const", "x" <> pretty name, "=", "var", pretty value], pretty k]
    Assign name value k -> PP.vsep ["*x" <> pretty name <+> "=" <+> pretty value, pretty k]
    Deref name var k -> PP.vsep [PP.hsep ["const", "x" <> pretty name, "=", "*x" <> pretty var], pretty k]
    Join name slot body k ->
      PP.nest 2 (PP.vsep ["join" <+> "j" <> pretty name <> PP.parens (foldMap pretty slot), pretty k])
        <> PP.line
        <> pretty body
    Jump join arg -> "jump" <+> "j" <> pretty join <> PP.parens (foldMap pretty arg)
    Return value -> "return" <+> pretty value
    Halt -> "halt"

sep :: Pretty a => PP.Doc ann -> [a] -> PP.Doc ann
sep s xs = PP.hsep (PP.punctuate "," ((s <>) . pretty <$> xs))

instance Pretty Atom where
  pretty = \case
    Var name -> "x" <> pretty name
    Unit -> "()"
    Bool False -> "false"
    Bool True -> "true"
    Int x -> pretty x
    Float x -> pretty x
    String s -> pretty (show (Text.unpack s))

instance Pretty Fun where
  pretty Fun {name, params, captures, blocks} =
    "f"
      <> pretty name
      <> PP.parens (sep "x" params)
      <> PP.brackets (sep "x" captures)
      <> PP.line
      <> PP.vsep (pretty <$> NE.toList blocks)
      <> PP.line

instance Pretty Block where
  pretty Block {name, slot, body} =
    PP.nest 2 $ "j" <> pretty name <> PP.parens (foldMap pretty slot) <> PP.line <> pretty body
