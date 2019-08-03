module Main where

import AST
import Parser

import System.FilePath
import System.Directory
import System.IO (hFlush, stdout, readFile)
import System.Exit (exitSuccess, exitFailure)
import System.Environment (getArgs)

import Data.Maybe (maybe, listToMaybe)
import Data.List (sort)
import Data.Semigroup
import Text.Megaparsec (runParserT, errorBundlePretty)
import Control.Monad.State.Strict
import Options.Applicative as Opt

main :: IO ()
main =
  getCurrentDirectory
  >>= parseArgs
  >>= (evalStateT startCompile . compileStateFromOptions)
  where
    parseArgs currentDirectory =
      execParser $ info (parseOptions <**> helper) mempty
      where
        parsePath :: String -> Either String FilePath
        parsePath path =
          if not $ isValid path then
            Left ("invalid path: " ++ path)
          else
            Right $ makeRelative currentDirectory $ normalise path
        
        parseOptions = CompileOptions
          <$> argument (eitherReader parsePath)
            (  metavar "TARGET"
            <> action "directory"
            <> help "The path to a single .boat source file or a directory containing source files")
          <*> Opt.option (eitherReader parsePackageName)
            (  value "Main"
            <> showDefault
            <> short 'n'
            <> long "name"
            <> metavar "PACKAGE_NAME"
            <> help "The name which will appear as the base of every path in this package")

startCompile :: CompileIO ()
startCompile = do
  fullModule <- do
    path <- gets (compileTarget . compileOptions)
    isDir <- lift $ doesDirectoryExist path
    if isDir then
      parseDirectory path
    else do
      isFile <- lift $ doesFileExist path
      if isFile then
        case takeExtension path of
          ".boat" ->
            parseSingleFile path defaultModule
          other -> lift $ do
            let ext = if null other then "no extension" else other
            putStrLn ("Error: expected extension of .boat for file, found " ++ ext)
            exitFailure
      else lift $ do
        putStrLn ("Error: cannot find file or directory at `" ++ path ++ "`")
        exitFailure
  exitIfErrors
  lift $ print fullModule
  printErrors

exitIfErrors :: CompileIO ()
exitIfErrors = do
  s <- get
  when (compileFailed s) printErrors

printErrors :: CompileIO ()
printErrors = do
  s <- get
  lift $ do
    forM_ (compileErrors s) print
    if compileFailed s then
      exitFailure
    else
      exitSuccess

isBoatExtension :: FilePath -> Bool
isBoatExtension = (".boat" ==) . takeExtension

containsBoatFiles :: FilePath -> IO Bool
containsBoatFiles path = do
  files <- listDirectory path
  checkAll files
  where
    checkAll [] = return False
    checkAll (file:rest) =
      if isBoatExtension file then do
        isFile <- doesFileExist (path </> file)
        if isFile then
          return True
        else
          checkAll rest
      else
        checkAll rest

parseAll :: FilePath -> Module -> CompileIO Module
parseAll path m = do
  isDir <- lift $ doesDirectoryExist path
  if isDir then
    case parseModuleName $ takeFileName path of
      Right name ->
        parseDirectory path <&> \sub ->
          modAddSub name sub m
      Left err -> do
        shouldWarn <- lift $ containsBoatFiles path
        when shouldWarn $
          addError CompileError
            { errorFile = Just path
            , errorSpan = Nothing
            , errorKind = Warning
            , errorMessage = "folder contains .boat files but isn't a valid module name" }
        return m
  else if isBoatExtension path then
    parseSingleFile path m
  else
    return m

parseDirectory :: FilePath -> CompileIO Module
parseDirectory path = do
  files <- lift $ sort <$> listDirectory path
  parseEach files defaultModule
  where
    parseEach []          m = return m
    parseEach (file:rest) m =
      parseAll (path </> file) m >>= parseEach rest

-- TODO: consider whether all files in a folder being grouped together into
-- a single module without any separation at all is a bug or a feature

parseSingleFile :: FilePath -> Module -> CompileIO Module
parseSingleFile path m = do
  lift $ putStrLn ("{- parsing: " ++ path ++ " -}")
  file <- lift $ readFile path
  let parserT = runCustomParser $ parseFile path m
  runParserT parserT path file >>= \case
    Left err -> lift $ do
      putStr (errorBundlePretty err)
      exitFailure
    Right m ->
      return m

