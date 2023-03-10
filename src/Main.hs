module Main where

import Data.ByteString.Lazy qualified as ByteString
import Data.Foldable (traverse_)
import Prettyprinter (pretty)
import System.Environment (getArgs)
import System.Exit (die)

import Interpreter (interpret)
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

  core <- case typecheck prog of
    Left err -> die (show err)
    Right core -> pure core

  putStrLn "=== Core ==="
  traverse_ (print . pretty) core
  putStrLn "============"

  interpret core
