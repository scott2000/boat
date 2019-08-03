module Main where

import AST
import Parser

import System.FilePath
import System.Directory
import System.IO (readFile)
import System.Exit (exitFailure)

import Data.List (sort, intercalate)
import Data.Semigroup
import Data.Set (Set)
import qualified Data.Set as Set
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
  lift $ putStrLn ("\n" ++ show fullModule)
  finishAndCheckErrors

exitIfErrors :: CompileIO ()
exitIfErrors = do
  count <- gets compileErrorCount
  when (errorCount count /= 0) $ do
    addError CompileError
      { errorFile = Nothing
      , errorSpan = Nothing
      , errorKind = Error
      , errorMessage = "stopping due to " ++ show count }
    printErrors
    lift $ exitFailure

finishAndCheckErrors :: CompileIO ()
finishAndCheckErrors = do
  exitIfErrors
  count <- gets compileErrorCount
  addError CompileError
    { errorFile = Nothing
    , errorSpan = Nothing
    , errorKind = Done
    , errorMessage = "compiled successfully with " ++ show count }
  printErrors

printErrors :: CompileIO ()
printErrors =
  gets compileErrors >>= lift . prettyCompileErrors

data PrettyErrorState = PrettyErrorState
  { peCurrentFile :: Maybe FilePath
  , peRestOfLines :: [String]
  , peLine :: !Int }

peDefault :: PrettyErrorState
peDefault = PrettyErrorState
  { peCurrentFile = Nothing
  , peRestOfLines = []
  , peLine = 0 }

peSeek :: Int -> PrettyErrorState -> PrettyErrorState
peSeek target s =
  let count = target - peLine s in
  if count < 0 then
    error "peSeek: cannot seek backwards!"
  else s
    { peRestOfLines = drop count $ peRestOfLines s
    , peLine = target }

prettyCompileErrors :: Set CompileError -> IO ()
prettyCompileErrors = go peDefault . Set.toList
  where
    go _ [] = return ()
    go s (e:es) = do
      let
        tag = "[" ++ show (errorKind e) ++ "] "
        messageLines = lines $ errorMessage e
        indented = intercalate ("\n" ++ replicate (length tag) ' ') messageLines
        errorSuffix = tag ++ indented
      case errorFile e of
        Just file ->
          case errorSpan e of
            Just Span { spanStart, spanEnd } -> do
              let
                startLineNumber = posLine spanStart
                seekTarget = startLineNumber - 1
              s <-
                if peCurrentFile s /= Just file then do
                  contents <- readFile file
                  return s
                    { peCurrentFile = Just file
                    , peRestOfLines = drop seekTarget $ lines contents
                    , peLine = seekTarget }
                else
                  return $ peSeek seekTarget s
              let
                endLineNumber = posLine spanEnd
                endLineNumberStr = show endLineNumber
                numLen = length endLineNumberStr
                lineSeparator = " |"
                blankLinePrefix = replicate numLen ' ' ++ lineSeparator
                lineCount = endLineNumber - startLineNumber + 1
              if lineCount == 1 then do
                let
                  line = head $ peRestOfLines s
                  startColumn = posColumn spanStart
                  endColumn = posColumn spanEnd
                  count = endColumn - startColumn
                  underline = replicate startColumn ' ' ++ replicate count '^' 
                putStrLn $ intercalate "\n"
                  [ "\n" ++ file ++ ":" ++ show spanStart ++ ":"
                  , blankLinePrefix
                  , endLineNumberStr ++ lineSeparator ++ " " ++ line
                  , blankLinePrefix ++ underline
                  , errorSuffix ]
              else do
                let
                  lines = take lineCount $ peRestOfLines s
                  lineStrs = zipWith showLine [startLineNumber..] lines
                  showLine n l =
                    let
                      str = show n
                      padding = replicate (length str - numLen) ' '
                    in
                      str ++ padding ++ lineSeparator ++ " " ++ l
                putStrLn $ intercalate "\n" $
                  [ "\n" ++ file ++ ":" ++ show spanStart ++ ":"
                  , blankLinePrefix ]
                  ++ lineStrs ++
                  [ blankLinePrefix
                  , errorSuffix ]
              go s es
            Nothing -> do
              when (peLine s /= -1 || peCurrentFile s /= Just file) $
                putStrLn ("\n" ++ file ++ ": ")
              putStrLn errorSuffix
              go PrettyErrorState
                { peCurrentFile = Just file
                , peRestOfLines = undefined
                , peLine = -1 } es
        Nothing -> do
          putStrLn ("\n" ++ errorSuffix)
          go undefined es

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
            , errorMessage =
              "folder contains .boat files but doesn't have a valid module name"
              ++ "\n(" ++ err ++ ")" }
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

