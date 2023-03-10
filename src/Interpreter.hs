{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImplicitParams #-}

module Interpreter (interpret) where

import Control.Exception (Exception, catch, throwIO)
import Data.Bitraversable (bitraverse)
import Data.Foldable (traverse_)
import Data.Functor ((<&>))
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.IORef (IORef, modifyIORef, newIORef, readIORef, writeIORef)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Vector qualified as Vector
import Data.Vector.Mutable qualified as MVector
import Data.Vector.Unboxed qualified as UVector
import Data.Vector.Unboxed.Mutable qualified as UMVector
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)

import Core

interpret :: [Expr] -> IO ()
interpret ss = do
  env <- newIORef IntMap.empty
  let ?env = env
  traverse_ eval ss

newtype Value = MkValue Any

pattern Value :: forall a. a -> Value
pattern Value x <- (unsafeCoerce -> x)
  where
    Value = MkValue . unsafeCoerce
{-# COMPLETE Value #-}

extract :: forall a. Value -> a
extract (Value x) = x

type Array = MVector.IOVector Value

type Object = IORef (HashMap Field Value)

type Env = ?env :: IORef (IntMap (IORef Value))

makeArray :: forall a. UVector.Unbox a => [Value] -> IO Value
makeArray xs = do
  let v = UVector.fromList (extract @a <$> xs)
  mv <- UVector.thaw v
  pure (Value mv)

makeBoxedArray :: [Value] -> IO Value
makeBoxedArray = fmap Value . Vector.thaw . Vector.fromList

makeVar :: Env => Tag -> Value -> IO ()
makeVar (Tag k) v = do
  var <- newIORef v
  modifyIORef ?env (IntMap.insert k var)

makeVars :: Env => [(Tag, Value)] -> IO ()
makeVars vals = do
  vars <- traverse (bitraverse (\(Tag k) -> pure k) newIORef) vals
  modifyIORef ?env (IntMap.fromList vars <>)

newtype Return = Ret Value

instance Show Return where
  show _ = "<return>"

instance Exception Return

eval :: Env => Expr -> IO Value
eval = \case
  Unit -> pure (Value ())
  Bool b -> pure (Value b)
  Int x -> pure (Value x)
  Float x -> pure (Value x)
  String s -> pure (Value s)
  Array t xs -> do
    xs' <- traverse eval xs
    case t of
      TUnit -> makeArray @() xs'
      TBool -> makeArray @Bool xs'
      TFloat -> makeArray @Double xs'
      TInt -> makeArray @Int xs'
      _ -> makeBoxedArray xs'
  Object fields -> do
    fields' <- traverse (traverse eval) fields
    obj <- newIORef (HashMap.fromList fields')
    pure (Value obj)
  Lambda captures params body -> do
    env <- readIORef ?env
    let captured = captures <&> \(Tag k) -> (k, env IntMap.! k)
    local <- newIORef (IntMap.fromList captured)
    let close =
          let ?env = local
           in let make args [] = Value do makeVars args; eval body
                  make args (p : ps) = Value \v -> extract (make ((p, v) : args) ps)
               in make []
    pure (close params)
  Var (Name (Tag k)) -> do
    env <- readIORef ?env
    -- putStrLn ""
    -- print k
    -- print (IntMap.keys env)
    readIORef (env IntMap.! k)
  Var (Intrinsic x) -> pure (intrinsic x)
  Call f args -> do
    f' <- eval f
    args' <- traverse eval args
    call f' args' `catch` \(Ret v) -> pure v
    where
      call g [] = extract g
      call g (x : xs) = call (extract g x) xs
  Cond cond true false -> do
    Value b <- eval cond
    if b
      then eval true
      else eval false
  Loop cond body -> loop
    where
      loop = do
        Value b <- eval cond
        if b
          then do traverse_ eval body; loop
          else pure (Value ())
  Return x -> do
    v <- eval x
    throwIO (Ret v)
  Decl tag body -> do
    v <- eval body
    makeVar tag v
    pure (Value ())
  Assign (Tag k) x -> do
    env <- readIORef ?env
    let var = env IntMap.! k
    v <- eval x
    writeIORef var v
    pure (Value ())
  Block ss x -> do
    env <- readIORef ?env
    traverse_ eval ss
    v <- eval x
    writeIORef ?env env
    pure v

intrinsic :: Intrinsic -> Value
intrinsic = \case
  Arith Plus NInt -> Value (arith ((+) @Int))
  Arith Minus NInt -> Value (arith ((-) @Int))
  Arith Times NInt -> Value (arith ((*) @Int))
  Arith Divide NInt -> Value (arith (div @Int))
  Arith Plus NFloat -> Value (arith ((+) @Double))
  Arith Minus NFloat -> Value (arith ((-) @Double))
  Arith Times NFloat -> Value (arith ((*) @Double))
  Arith Divide NFloat -> Value (arith ((/) @Double))
  Modulo -> Value (arith (mod @Int))
  Cast NInt NInt -> Value (cast (id @Int))
  Cast NInt NFloat -> Value (cast (fromIntegral @Int @Double))
  Cast NFloat NInt -> Value (cast (floor @Double @Int))
  Cast NFloat NFloat -> Value (cast (id @Double))
  Compare Lt NInt -> Value (comp ((<) @Int))
  Compare Lte NInt -> Value (comp ((<=) @Int))
  Compare Eq NInt -> Value (comp ((==) @Int))
  Compare Neq NInt -> Value (comp ((/=) @Int))
  Compare Gte NInt -> Value (comp ((>=) @Int))
  Compare Gt NInt -> Value (comp ((>) @Int))
  Compare Lt NFloat -> Value (comp ((<) @Double))
  Compare Lte NFloat -> Value (comp ((<=) @Double))
  Compare Eq NFloat -> Value (comp ((==) @Double))
  Compare Neq NFloat -> Value (comp ((/=) @Double))
  Compare Gte NFloat -> Value (comp ((>=) @Double))
  Compare Gt NFloat -> Value (comp ((>) @Double))
  Logic And -> Value (logic (&&))
  Logic Or -> Value (logic (||))
  StringAppend -> Value \x y -> pure @IO (extract @Text x <> extract @Text y)
  ArrayLength TUnit -> Value (arrayLength @())
  ArrayLength TBool -> Value (arrayLength @Bool)
  ArrayLength TInt -> Value (arrayLength @Int)
  ArrayLength TFloat -> Value (arrayLength @Double)
  ArrayLength _ -> Value \(Value v) -> pure @IO (Value (MVector.length v))
  ReadArray TUnit -> Value (readArray @())
  ReadArray TBool -> Value (readArray @Bool)
  ReadArray TInt -> Value (readArray @Int)
  ReadArray TFloat -> Value (readArray @Double)
  ReadArray _ -> Value \(Value v) (Value ix) -> MVector.read @IO v ix
  WriteArray TUnit -> Value (writeArray @())
  WriteArray TBool -> Value (writeArray @Bool)
  WriteArray TInt -> Value (writeArray @Int)
  WriteArray TFloat -> Value (writeArray @Double)
  WriteArray _ -> Value \(Value v) (Value ix) (Value x) -> Value () <$ MVector.write @IO v ix x
  ToString TInt -> Value \(Value (x :: Int)) -> pure @IO (Text.pack (show x))
  ToString _ -> _toString
  WriteStdout -> Value \(Value s) -> Value () <$ Text.putStrLn s
  ReadStdinLine -> Value (Value <$> Text.getLine)
  ReadObject field -> Value \(Value (obj :: Object)) -> (HashMap.! field) <$> readIORef obj
  WriteObject field -> Value \(Value obj) (x :: Value) -> Value () <$ modifyIORef obj (HashMap.insert field x)
  where
    arith :: (a -> a -> a) -> Value -> Value -> IO Value
    arith op (Value x) (Value y) = pure (Value (x `op` y))
    cast :: (a -> b) -> Value -> IO Value
    cast f (Value x) = pure (Value (f x))
    comp :: (a -> a -> Bool) -> Value -> Value -> IO Value
    comp cmp (Value x) (Value y) = pure (Value (x `cmp` y))
    logic :: (Bool -> Bool -> Bool) -> Value -> Value -> IO Value
    logic op (Value x) (Value y) = pure (Value (x `op` y))
    arrayLength :: forall a. UVector.Unbox a => Value -> IO Value
    arrayLength (Value v) = pure (Value (UMVector.length @a v))
    readArray :: forall a. UVector.Unbox a => Value -> Value -> IO Value
    readArray (Value v) (Value ix) = Value <$> UMVector.read @_ @a v ix
    writeArray :: forall a. UVector.Unbox a => Value -> Value -> Value -> IO Value
    writeArray (Value v) (Value ix) (Value x) = Value () <$ UMVector.write @_ @a v ix x
