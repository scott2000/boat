-- | Parses command-line arguments and then runs every pass in order
module Main where

import Utility
import Parse
import Analyze

import System.FilePath
import System.Directory
import System.Exit (ExitCode)

import Data.List (intercalate)
import Data.IORef
import Control.Monad.State.Strict
import Control.Exception
import Options.Applicative as Opt

import qualified Data.HashMap.Strict as HashMap

import Control.Monad.Reader

-- | The entry point of the compiler, parses arguments and then calls 'startCompile'
main :: IO ()
main = do
  currentDirectory <- getCurrentDirectory
  options <- parseArgs currentDirectory
  stateRef <- newIORef initialCompileState
  runReaderT (runCompileIO startCompile) (options, stateRef) `catches`
    [ Handler \(e :: ExitCode) -> throwIO e
    , Handler \(e :: SomeException) -> do
        state <- readIORef stateRef
        let
          phaseMsg =
            case compilePhase state of
              PhaseInit -> "initialization"
              PhaseParser -> "parsing"
              PhaseNameResolve -> "name resolution"
              PhaseAssocOps -> "operator association"
              PhaseInferVariance -> "variance inference"
              PhaseInferTypes -> "type inference"
        compilerBugRawIO state $ "unexpected crash during " ++ phaseMsg ++ ":" ++ indent (show e) ]
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
            (  value (Identifier "Main")
            <> showDefault
            <> short 'n'
            <> long "name"
            <> metavar "PACKAGE_NAME"
            <> help "The name which will appear as the base of every path in this package")
          <*> switch
            (  long "explain-errors"
            <> help "Enables extended explanations for certain compile errors")

-- | Starts the compilation process by running each pass in order
startCompile :: CompileIO ()
startCompile = do
  setPhase PhaseParser
  mods <- parse
  exitIfErrors
  liftIO $ putStrLn ("\n" ++ intercalate "\n" (map show mods))

  when (null mods) $
    addError compileError
      { errorKind = Warning
      , errorMessage = "no code found in source files" }

  setPhase PhaseNameResolve
  allDecls <- nameResolve mods
  exitIfErrors

  setPhase PhaseAssocOps
  allDecls <- assocOps allDecls
  exitIfErrors
  liftIO $ putStrLn $ "\nFully resolved and associated:\n\n" ++ show allDecls

  setPhase PhaseInferVariance
  allDecls <- inferVariance allDecls
  -- Errors here shouldn't stop compilation until after the kinds of type ascriptions are checked

  liftIO $ putStrLn $ "\nInferred variances:\n"
  liftIO $ forM_ (HashMap.toList $ allDatas allDecls) $
    \(name, DataDecl { dataSig } :&: _) -> putStrLn $
      showWithName (show name) $ dataSigToTypeKind dataSig

  setPhase PhaseInferTypes
  _allDecls <- inferTypes allDecls
  exitIfErrors

  finishAndCheckErrors
  where
    setPhase phase = compileModify \s ->
      s { compilePhase = phase }


