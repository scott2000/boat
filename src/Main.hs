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

-- | A phase of compilation (see "Parse" and "Analyze")
data Phase
  -- | Any initialization in "Main" that occurs before parsing begins
  = PhaseInit
  -- | The parsing phase defined in "Parse" ('parse')
  | PhaseParser
  -- | The name resolution phase defined in "Analyze.NameResolve" ('nameResolve')
  | PhaseNameResolve
  -- | The operator association phase defined in "Analyze.AssocOps" ('assocOps')
  | PhaseAssocOps
  -- | The variance inference phase defined in "Analyze.InferVariance" ('inferVariance')
  | PhaseInferVariance
  -- | The type inference phase defined in "Analyze.InferTypes" ('inferTypes')
  | PhaseInferTypes

-- | The entry point of the compiler, parses arguments and then calls 'startCompile'
main :: IO ()
main = do
  currentDirectory <- getCurrentDirectory
  options <- parseArgs currentDirectory
  phase <- newIORef PhaseInit
  evalStateT (runCompileIO $ startCompile phase) (compileStateFromOptions options) `catches`
    [ Handler \(e :: ExitCode) -> throwIO e
    , Handler \(e :: SomeException) -> do
        phaseMsg <- readIORef phase <&> \case
          PhaseInit -> "initialization"
          PhaseParser -> "parsing"
          PhaseNameResolve -> "name resolution"
          PhaseAssocOps -> "operator association"
          PhaseInferVariance -> "variance inference"
          PhaseInferTypes -> "type inference"
        compilerBugRawIO $ "unexpected crash during " ++ phaseMsg ++ ":" ++ indent (show e) ]
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
startCompile :: IORef Phase -> CompileIO ()
startCompile phase = do
  setPhase phase PhaseParser
  mods <- parse
  exitIfErrors
  liftIO $ putStrLn ("\n" ++ intercalate "\n" (map show mods))

  when (null mods) $
    addError compileError
      { errorKind = Warning
      , errorMessage = "no code found in source files" }

  setPhase phase PhaseNameResolve
  allDecls <- nameResolve mods
  exitIfErrors

  setPhase phase PhaseAssocOps
  allDecls <- assocOps allDecls
  exitIfErrors
  liftIO $ putStrLn $ "\nFully resolved and associated:\n\n" ++ show allDecls

  setPhase phase PhaseInferVariance
  allDecls <- inferVariance allDecls
  -- Errors here shouldn't stop compilation until after the kinds of type ascriptions are checked

  liftIO $ putStrLn $ "\nInferred variances:\n"
  liftIO $ forM_ (HashMap.toList $ allDatas allDecls) $
    \(name, DataDecl { dataSig } :&: _) -> putStrLn $
      showWithName (show name) $ dataSigToTypeKind dataSig

  setPhase phase PhaseInferTypes
  _allDecls <- inferTypes allDecls
  exitIfErrors

  finishAndCheckErrors
  where
    setPhase :: IORef Phase -> Phase -> CompileIO ()
    setPhase phase newPhase =
      liftIO $ writeIORef phase newPhase

