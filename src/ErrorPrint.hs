module ErrorPrint where

import AST

import System.IO (readFile)
import System.Exit (exitFailure)

import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict

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

addFatal :: CompileError -> CompileIO ()
addFatal e = do
  addError e
  exitIfErrors

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

