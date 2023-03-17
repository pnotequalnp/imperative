{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImplicitParams #-}

module Interpreter (interpret) where

import Control.Exception (Exception, catch, throwIO)
import Data.Functor (void)
import Data.HashMap.Strict qualified as HashMap
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List.NonEmpty (NonEmpty (..))
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Vector.Mutable qualified as MVector
import Data.Vector.Unboxed qualified as UVector
import Data.Vector.Unboxed.Mutable qualified as UMVector
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)

import Core (Arith (..), Comparison (..), Logic (..), Number (..), Type (..), Field)
import Normal

interpret :: NonEmpty Fun -> IO ()
interpret (main :| funs) = do
  let functions = preprocess (main : funs)
      main' = functions IntMap.! main.name
      closure = MkClosure {function = main', captures = []}

  env <- newIORef IntMap.empty

  let ?env = env
      ?functions = functions

  void (call main' closure []) `catch` \Done -> pure ()

data Done = Done
  deriving stock (Show)

instance Exception Done

newtype Value = MkValue Any

pattern Value :: forall a. a -> Value
pattern Value x <- (unsafeCoerce -> x)
  where
    Value = MkValue . unsafeCoerce
{-# COMPLETE Value #-}

extract :: forall a. Value -> a
extract (Value x) = x

data Closure = MkClosure
  { function :: Function
  , captures :: [Value]
  }

data Function = Function
  { params :: [Name]
  , captures :: [Name]
  , entry :: Expr
  , blocks :: IntMap Block
  }

type Functions = ?functions :: IntMap Function
type Blocks = ?blocks :: IntMap Block
type Env = ?env :: IORef (IntMap Value)
type Eval = (Functions, Blocks, Env)

preprocess :: [Fun] -> IntMap Function
preprocess =
  IntMap.fromList . fmap \Fun {name, captures, params, blocks = entry :| blocks} ->
    (name, Function {params, captures, entry = entry.body, blocks = processBlocks (entry : blocks)})
  where
    processBlocks = IntMap.fromList . fmap \block -> (block.name, block)

data Unhoisted = Unhoisted
  deriving stock (Show)

instance Exception Unhoisted

call :: (Functions, Env) => Function -> Closure -> [Value] -> IO Value
call Function {params, captures, entry, blocks} closure args = do
  let captureVals = zip captures closure.captures
      argVals = zip params args
      initialEnv = IntMap.fromList (captureVals <> argVals)
  env <- readIORef ?env
  writeIORef ?env initialEnv
  r <-
    let ?blocks = blocks
     in eval entry
  writeIORef ?env env
  pure r

eval :: Eval => Expr -> IO Value
eval = \case
  Closure name f captureNames k -> do
    captures <- traverse getName captureNames
    let fun = ?functions IntMap.! f
        closure = MkClosure {function = fun, captures}
    bind name (Value closure)
    eval k
  Call name f args k -> do
    Value closure <- immediate f
    args' <- traverse immediate args
    r <- call closure.function closure args'
    bind name r
    eval k
  Intrinsic name x args k -> do
    args' <- traverse immediate args
    r <- intrinsic args' x
    bind name r
    eval k
  Decl name value k -> do
    v <- immediate value
    var <- newIORef v
    bind name (Value var)
    eval k
  Assign name value k -> do
    v <- immediate value
    Value var <- getName name
    writeIORef var v
    eval k
  Deref name v k -> do
    Value var <- getName v
    r <- readIORef var
    bind name r
    eval k
  Branch cond true false -> do
    Value b <- immediate cond
    let block = ?blocks IntMap.! if b then true else false
    eval block.body
  Jump block arg -> do
    let Block {slot, body} = ?blocks IntMap.! block
    case (arg, slot) of
      (Just value, Just name) -> do
        v <- immediate value
        bind name v
      _ -> pure ()
    eval body
  Return value -> immediate value
  Halt -> throwIO Done
  Lambda {} -> throwIO Unhoisted
  Join {} -> throwIO Unhoisted
  Cond {} -> throwIO Unhoisted

immediate :: Env => Atom -> IO Value
immediate = \case
  Var name -> getName name
  Unit -> pure (Value ())
  Bool b -> pure (Value b)
  Int x -> pure (Value x)
  Float x -> pure (Value x)
  String s -> pure (Value s)

getName :: Env => Name -> IO Value
getName name = (IntMap.! name) <$> readIORef ?env

bind :: Env => Name -> Value -> IO ()
bind name value = modifyIORef' ?env (IntMap.insert name value)

data IntrinsicArity = IntrinsicArity
  deriving stock (Show)

instance Exception IntrinsicArity

intrinsic :: [Value] -> Intrinsic -> IO Value
intrinsic args = \case
  Arith Plus NInt | [x, y] <- args -> arith ((+) @Int) x y
  Arith Minus NInt | [x, y] <- args -> arith ((-) @Int) x y
  Arith Times NInt | [x, y] <- args -> arith ((*) @Int) x y
  Arith Divide NInt | [x, y] <- args -> arith (div @Int) x y
  Arith Plus NFloat | [x, y] <- args -> arith ((+) @Double) x y
  Arith Minus NFloat | [x, y] <- args -> arith ((-) @Double) x y
  Arith Times NFloat | [x, y] <- args -> arith ((*) @Double) x y
  Arith Divide NFloat | [x, y] <- args -> arith (div @Int) x y
  Modulo | [x, y] <- args -> arith (mod @Int) x y
  Cast NInt NInt | [x] <- args -> cast (id @Int) x
  Cast NInt NFloat | [x] <- args -> cast (fromIntegral @Int @Double) x
  Cast NFloat NInt | [x] <- args -> cast (round @Double @Int) x
  Cast NFloat NFloat | [x] <- args -> cast (id @Double) x
  Compare Lt NInt | [x, y] <- args -> comp ((<) @Int) x y
  Compare Lte NInt | [x, y] <- args -> comp ((<=) @Int) x y
  Compare Eq NInt | [x, y] <- args -> comp ((==) @Int) x y
  Compare Neq NInt | [x, y] <- args -> comp ((/=) @Int) x y
  Compare Gte NInt | [x, y] <- args -> comp ((>=) @Int) x y
  Compare Gt NInt | [x, y] <- args -> comp ((>) @Int) x y
  Compare Lt NFloat | [x, y] <- args -> comp ((<) @Double) x y
  Compare Lte NFloat | [x, y] <- args -> comp ((<=) @Double) x y
  Compare Eq NFloat | [x, y] <- args -> comp ((==) @Double) x y
  Compare Neq NFloat | [x, y] <- args -> comp ((/=) @Double) x y
  Compare Gte NFloat | [x, y] <- args -> comp ((>=) @Double) x y
  Compare Gt NFloat | [x, y] <- args -> comp ((>) @Double) x y
  Logic And | [x, y] <- args -> logic (&&) x y
  Logic Or | [x, y] <- args -> logic (||) x y
  StringAppend | [x, y] <- args -> pure (Value (extract x `Text.append` extract y))
  NewArray TUnit | [len] <- args -> makeArray @() len
  NewArray TBool | [len] <- args -> makeArray @Bool len
  NewArray TInt | [len] <- args -> makeArray @Int len
  NewArray TFloat | [len] <- args -> makeArray @Double len
  NewArray _ | [len] <- args -> Value <$> MVector.unsafeNew (extract len)
  ArrayLength TUnit | [xs] <- args -> arrayLength @() xs
  ArrayLength TBool | [xs] <- args -> arrayLength @Bool xs
  ArrayLength TInt | [xs] <- args -> arrayLength @Int xs
  ArrayLength TFloat | [xs] <- args -> arrayLength @Double xs
  ArrayLength _ | [xs] <- args -> pure (Value (MVector.length (extract xs)))
  ReadArray TUnit | [xs, ix] <- args -> readArray @() xs ix
  ReadArray TBool | [xs, ix] <- args -> readArray @Bool xs ix
  ReadArray TInt | [xs, ix] <- args -> readArray @Int xs ix
  ReadArray TFloat | [xs, ix] <- args -> readArray @Double xs ix
  ReadArray _ | [xs, ix] <- args -> Value <$> MVector.unsafeRead (extract xs) (extract ix)
  WriteArray TUnit | [xs, ix, v] <- args -> writeArray @() xs ix v
  WriteArray TBool | [xs, ix, v] <- args -> writeArray @Bool xs ix v
  WriteArray TInt | [xs, ix, v] <- args -> writeArray @Int xs ix v
  WriteArray TFloat | [xs, ix, v] <- args -> writeArray @Double xs ix v
  WriteArray _ | [xs, ix, v] <- args -> Value () <$ MVector.unsafeWrite (extract xs) (extract ix) (extract v)
  NewObject | [] <- args -> Value <$> newIORef (HashMap.empty @Field @Value)
  ReadObject field | [obj] <- args -> (HashMap.! field) <$> readIORef (extract obj)
  WriteObject field | [obj, v] <- args -> Value () <$ modifyIORef' (extract obj) (HashMap.insert field v)
  ToString TInt | [x] <- args -> (pure . Value . Text.pack . show @Int . extract) x
  WriteStdout | [s] <- args -> Value () <$ Text.putStr (extract s)
  ReadStdinLine | [] <- args -> Value <$> Text.getLine
  _ -> throwIO IntrinsicArity
  where
    arith :: (a -> a -> a) -> Value -> Value -> IO Value
    arith op (Value x) (Value y) = pure (Value (x `op` y))
    cast :: (a -> b) -> Value -> IO Value
    cast f (Value x) = pure (Value (f x))
    comp :: (a -> a -> Bool) -> Value -> Value -> IO Value
    comp cmp (Value x) (Value y) = pure (Value (x `cmp` y))
    logic :: (Bool -> Bool -> Bool) -> Value -> Value -> IO Value
    logic op (Value x) (Value y) = pure (Value (x `op` y))
    makeArray :: forall a. UVector.Unbox a => Value -> IO Value
    makeArray (Value len) = Value <$> UMVector.unsafeNew @_ @a len
    arrayLength :: forall a. UVector.Unbox a => Value -> IO Value
    arrayLength (Value v) = pure (Value (UMVector.length @a v))
    readArray :: forall a. UVector.Unbox a => Value -> Value -> IO Value
    readArray (Value v) (Value ix) = Value <$> UMVector.unsafeRead @_ @a v ix
    writeArray :: forall a. UVector.Unbox a => Value -> Value -> Value -> IO Value
    writeArray (Value v) (Value ix) (Value x) = Value () <$ UMVector.unsafeWrite @_ @a v ix x
