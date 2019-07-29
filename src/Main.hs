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
main = evalStateT startCompile defaultCompileState

startCompile :: CompileIO ()
startCompile = do
  args <- lift $ getArgs
  mapM_ parseSingleFile args
  exitIfErrors

exitIfErrors :: CompileIO ()
exitIfErrors = do
  s <- get
  when (compileFailed s) $ do
    forM_ (compileErrors s) $ \err ->
      lift $ putStrLn $ show err
    lift exitFailure

parseSingleFile :: FilePath -> CompileIO File
parseSingleFile path = do
  let file = defaultFile path
  contents <- lift $ readFile path
  let parserT = runCustomParser $ parseFile file
  runParserT parserT path contents >>= \case
    Left err -> lift $ do
      putStr (errorBundlePretty err)
      exitFailure
    Right file -> do
      lift $ putStrLn $ show file
      return file
  
