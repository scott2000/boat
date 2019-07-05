module Main where

import AST
import Parser

import Text.Megaparsec (runParserT, errorBundlePretty)
import Control.Monad.State.Strict

main :: IO ()
main =
  let
    parserT = runCustomParser parser
    parseResult = runParserT parserT "" "fun\n  _ Empty -> Empty\n  f (Cons x xs) -> Cons (f x) (map f xs)"
    compilerState = CompilerState { anonTypes = 0 }
  in
    case evalState parseResult compilerState of
      Left err -> putStr (errorBundlePretty err)
      Right x -> do
        putStrLn ("Parsed expr:\n" ++ show x ++ "\n")
        putStrLn ("De Bruijn:\n" ++ show (toDeBruijn x) ++ "\n")
 