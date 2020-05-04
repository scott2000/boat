module Main where

import Utility.Basics
import Utility.ErrorPrint
import Utility.Program
import Utility.Parser
import Pass.Parser
import Pass.NameResolve
import Pass.AssocOps

import System.FilePath
import System.Directory
import System.IO (readFile)
import System.Exit (exitFailure)

import Data.List (sort, intercalate)
import Text.Megaparsec (runParserT)
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
          if isValid path then
            Right $ makeRelative currentDirectory $ normalise path
          else
            Left ("invalid path: " ++ path)

        parseOptions = CompileOptions
          <$> argument (eitherReader parsePath)
            (  metavar "TARGET"
            <> action "file"
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
  mods <- do
    path <- gets (compileTarget . compileOptions)
    isDir <- lift $ doesDirectoryExist path
    if isDir then
      parseDirectory path
    else do
      isFile <- lift $ doesFileExist path
      if isFile then
        case takeExtension path of
          ".boat" ->
            parseSingleFile path <&> \case
              Just mod -> [mod]
              Nothing  -> []
          other -> lift $ do
            let ext = if null other then "no extension" else other
            putStrLn ("Error: expected extension of .boat for file, found " ++ ext)
            exitFailure
      else lift $ do
        putStrLn ("Error: cannot find file or directory at `" ++ path ++ "`")
        exitFailure
  exitIfErrors
  lift $ putStrLn ("\n" ++ intercalate "\n" (map show mods))

  allDecls <- nameResolve mods
  exitIfErrors

  allDecls <- assocOps allDecls
  exitIfErrors
  lift $ putStrLn $ "\nFully resolved and associated:\n\n" ++ show allDecls

  finishAndCheckErrors

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

parseAll :: FilePath -> CompileIO (Maybe Module)
parseAll path = do
  isDir <- lift $ doesDirectoryExist path
  if isDir then
    case parseModuleName $ takeFileName path of
      Right name ->
        Just . moduleFromSubs name <$> parseDirectory path
      Left err -> do
        shouldWarn <- lift $ containsBoatFiles path
        when shouldWarn $
          addError CompileError
            { errorFile = Just path
            , errorSpan = Nothing
            , errorKind = Warning
            , errorMessage =
              "folder contains .boat files but doesn't have a valid module name"
              ++ "\n(" ++ err ++ ")" }
        return Nothing
  else if isBoatExtension path then
    parseSingleFile path
  else
    return Nothing

parseDirectory :: FilePath -> CompileIO [Module]
parseDirectory path = do
  files <- lift $ sort <$> listDirectory path
  forEach files []
  where
    forEach []          mods = return mods
    forEach (file:rest) mods = do
      parseAll (path </> file) >>= \case
        Just mod ->
          forEach rest (mod:mods)
        Nothing ->
          forEach rest mods

parseSingleFile :: FilePath -> CompileIO (Maybe Module)
parseSingleFile path = do
  lift $ putStrLn ("{- parsing: " ++ path ++ " -}")
  file <- lift $ readFile path
  let parserT = runCustomParser $ parseFile path
  runParserT parserT path file >>= \case
    Left err -> do
      convertParseErrors err
      return Nothing
    Right m ->
      return $ Just m

