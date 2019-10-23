module ErrorPrint where

import Basics

import System.IO (readFile)
import System.Exit (exitFailure)

import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict

import System.Console.ANSI

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
        kindStr = show $ errorKind e
        color = errorColor $ errorKind e
        boldColor color =
          setSGRCode [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid color]
        colorize str =
          boldColor color
          ++ str ++ setSGRCode [Reset]
        tag = colorize ("[" ++ kindStr ++ "]") ++ " "
        messageLines = lines $ errorMessage e
        indented = intercalate ("\n" ++ replicate (length kindStr + 3) ' ') messageLines
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
                startColumn = posColumn spanStart
                endColumn = posColumn spanEnd
                numLen = length endLineNumberStr
                lineNumberColor = boldColor Blue
                lineSeparator = " |" ++ setSGRCode [Reset]
                blankLinePrefix = lineNumberColor ++ replicate numLen ' ' ++ lineSeparator
                lineCount = endLineNumber - startLineNumber + 1
              if lineCount == 1 then do
                let
                  line =
                    case peRestOfLines s of
                      [] -> "<end of file>"
                      (line:_) -> line
                  count = endColumn - startColumn
                  underline = replicate startColumn ' ' ++ colorize (replicate count '^')
                putStrLn $ intercalate "\n"
                  [ "\n" ++ file ++ ":" ++ show spanStart ++ ":"
                  , blankLinePrefix
                  , lineNumberColor ++ endLineNumberStr ++ lineSeparator ++ " " ++ line
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
                      colorizedLine
                        | n == startLineNumber =
                          let (a, b) = splitAt (startColumn - 1) l in
                          a ++ colorize b
                        | n == endLineNumber =
                          let (a, b) = splitAt (endColumn - 1) l in
                          colorize a ++ b
                        | otherwise = colorize l
                    in
                      lineNumberColor ++ str ++ padding ++ lineSeparator
                      ++ " " ++ colorize ">" ++ " " ++ colorizedLine
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

