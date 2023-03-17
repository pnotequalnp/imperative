module Main where

import Data.ByteString.Lazy qualified as ByteString
import Data.Foldable (traverse_)
import Prettyprinter (pretty)
import System.Environment (getArgs)
import System.Exit (die)

import Interpreter (interpret)
import Normal (normalize)
import Parser (parse)
import Typechecker (typecheck)

main :: IO ()
main = do
  args <- getArgs

  fp <- case args of
    [fp] -> pure fp
    _ -> die "source file not provided"

  src <- ByteString.readFile fp

  prog <- case parse fp src of
    Left err -> die err
    Right xs -> pure xs

  let (res, x) = typecheck prog
  core <- case res of
    Left err -> die (show err)
    Right core -> pure core

  putStrLn "===== Core ====="
  traverse_ (print . pretty) core
  putStrLn "================\n"

  let funs = normalize x core

  putStrLn "==== Normal ===="
  traverse_ (print . pretty) funs
  putStrLn "================\n"

  interpret funs
