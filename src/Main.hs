module Main where

import Utility.Basics
import Utility.ErrorPrint
import Utility.AST
import Utility.Program
import Utility.Parser
import Pass.Parser
import Pass.NameResolve
import Pass.AssocOps
import Pass.InferVariance

import System.FilePath
import System.Directory
import System.IO (readFile)
import System.Exit (exitFailure)

import Data.List (sort, intercalate)
import Data.IORef
import Text.Megaparsec (runParserT)
import Control.Monad.State.Strict
import Control.Exception
import Options.Applicative as Opt

data Phase
  = PhaseInit
  | PhaseParser
  | PhaseNameResolve
  | PhaseAssocOps
  | PhaseInferVariance

main :: IO ()
main = do
  phase <- newIORef PhaseInit
  catch (start phase) $ \(e :: SomeException) -> do
    phaseMsg <- readIORef phase <&> \case
      PhaseInit -> "initialization"
      PhaseParser -> "parsing"
      PhaseNameResolve -> "name resolution"
      PhaseAssocOps -> "operator association"
      PhaseInferVariance -> "variance inference"
    compilerBugRawIO $ "unexpected crash during " ++ phaseMsg ++ ":" ++ indent (show e)

start :: IORef Phase -> IO ()
start phase = do
  currentDirectory <- getCurrentDirectory
  options <- parseArgs currentDirectory
  evalStateT (startCompile phase) $ compileStateFromOptions options
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

setPhase :: IORef Phase -> Phase -> CompileIO ()
setPhase phase newPhase =
  lift $ writeIORef phase newPhase

startCompile :: IORef Phase -> CompileIO ()
startCompile phase = do
  setPhase phase PhaseParser
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
            parseSingleFile path <&> prependModule []
          other -> lift $ do
            let ext = if null other then "no extension" else other
            putStrLn ("Error: expected extension of .boat for file, found " ++ ext)
            exitFailure
      else lift $ do
        putStrLn ("Error: cannot find file or directory at `" ++ path ++ "`")
        exitFailure
  exitIfErrors
  lift $ putStrLn ("\n" ++ intercalate "\n" (map show mods))

  when (null mods) $
    addError CompileError
      { errorFile = Nothing
      , errorSpan = Nothing
      , errorKind = Warning
      , errorMessage = "no code found in source files" }

  setPhase phase PhaseNameResolve
  allDecls <- nameResolve mods
  exitIfErrors

  setPhase phase PhaseAssocOps
  allDecls <- assocOps allDecls
  exitIfErrors
  lift $ putStrLn $ "\nFully resolved and associated:\n\n" ++ show allDecls

  setPhase phase PhaseInferVariance
  allDecls <- inferVariance allDecls

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

prependModule :: [Module] -> Module -> [Module]
prependModule mods mod
  | modIsEmpty mod = mods
  | otherwise      = mod : mods

parseAll :: FilePath -> CompileIO Module
parseAll path = do
  isDir <- lift $ doesDirectoryExist path
  if isDir then
    case parseModuleName $ takeFileName path of
      Right name ->
        moduleFromSubs name <$> parseDirectory path
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
        return defaultModule
  else if isBoatExtension path then
    parseSingleFile path
  else
    return defaultModule

parseDirectory :: FilePath -> CompileIO [Module]
parseDirectory path = do
  files <- lift $ sort <$> listDirectory path
  forEach files []
  where
    forEach []          mods = return mods
    forEach (file:rest) mods =
      parseAll (path </> file) >>= forEach rest . prependModule mods

parseSingleFile :: FilePath -> CompileIO Module
parseSingleFile path = do
  lift $ putStrLn ("{- parsing: " ++ path ++ " -}")
  file <- lift $ readFile path
  let parserT = runCustomParser $ parseFile path
  runParserT parserT path file >>= \case
    Left err -> do
      convertParseErrors err
      return defaultModule
    Right m ->
      return m

