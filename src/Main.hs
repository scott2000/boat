module Main where

import AST
import Parser

import System.FilePath
import System.Directory
import System.IO (hFlush, stdout, readFile)
import System.Exit (exitFailure)
import System.Environment (getArgs)

import Text.Megaparsec (runParserT, errorBundlePretty)
import Control.Monad.State.Strict

main :: IO ()
main = do
  args <- getArgs
  file <- readFile (args !! 0)
  let
    parserT = runCustomParser parser
    parseResult = runParserT parserT "" file 
    compilerState = CompilerState { anonTypes = 0 }
  case evalState parseResult compilerState of
    Left err -> putStr (errorBundlePretty err)
    Right x -> do
      putStrLn ("Parsed expr:\n" ++ show x ++ "\n")
      putStrLn ("De Bruijn:\n" ++ show (toDeBruijn x) ++ "\n")

