-- | Utilities for checking for errors and for formatting error messages
module Utility.ErrorPrint
  ( CompileError (..)
  , addError
  , addFatal
  , exitIfErrors
  , finishAndCheckErrors
  , compilerBug
  , compilerBugRawIO
  ) where

import Utility.Basics

import System.IO (readFile)
import System.Exit (exitFailure)

import Data.Maybe (fromMaybe)
import Data.List (intercalate)
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict

import System.Console.ANSI

-- | Add a fatal error (like 'addError', but never returns)
addFatal :: CompileError -> CompileIO a
addFatal e = do
  addError e
  exitIfErrors
  compilerBug "addFatal did not exit!"

-- | If any errors occurred, print them and exit with failure
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

-- | Print any errors generated during compilation
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

-- | Header printed before an error message for a compiler bug
compilerBugBaseMessage :: String
compilerBugBaseMessage =
  "something went wrong when compiling your code! (please report this compiler bug)\n"

-- | Prints an error message and exits (for use in code that should be unreachable)
compilerBug :: String -> CompileIO a
compilerBug msg = do
  addError CompileError
    { errorFile = Nothing
    , errorSpan = Nothing
    , errorKind = Error
    , errorMessage = compilerBugBaseMessage ++ "error message: " ++ msg }
  printErrors
  lift $ exitFailure

-- | Like 'compilerBug', but doesn't require 'CompileIO' and prints a raw message
compilerBugRawIO :: String -> IO a
compilerBugRawIO err = do
  prettyCompileErrors $ Set.singleton CompileError
    { errorFile = Nothing
    , errorSpan = Nothing
    , errorKind = Error
    , errorMessage = compilerBugBaseMessage ++ err }
  exitFailure

-- | Prints all errors that have been generated
printErrors :: CompileIO ()
printErrors =
  gets compileErrors >>= lift . prettyCompileErrors

-- | Describes how a line of text should be printed in an error message
data LineStyle
  -- | Does no highlighting
  = Plain
  -- | Skips a certain number of lines with the given separator
  | Skip !Int
  -- | Starts a multiline highlight block
  | MultilineStart
    { hlStart :: !Int }
  -- | Continues a multiline highlight block
  | MultilineContinue
  -- | Ends a multiline highlight block
  | MultilineEnd
    { hlEnd :: !Int}
  -- | Underlines a certain section of the line
  | Underline
    { hlStart :: !Int
    , hlEnd :: !Int }

-- | A styled line is a line and the style to be used to print it
type StyledLine = (LineStyle, String)

-- | Prints the escape sequence to set a certain color
setColor :: Color -> IO ()
setColor color =
  setSGR [SetColor Foreground Vivid color]

-- | Prints the escape sequence to set a certain color, but makes it bold
setBoldColor :: Color -> IO ()
setBoldColor color =
  setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid color]

-- | Prints the escape sequence to reset the color back to the terminal's default
resetColor :: IO ()
resetColor = setSGR [Reset]

-- | The separator used for skipped lines
breakSeparator :: String
breakSeparator = "..."

-- | Prints all of the styled lines with a certain color starting from a certain line number
prettyLines :: Color -> Int -> [StyledLine] -> IO ()
prettyLines color firstLine lines = do
  printBlank
  printAll True firstLine lines
  where
    numberLength :: Int
    numberLength =
      length $ show $ firstLine + length lines

    hasMultiline :: Bool
    hasMultiline = any isMultilineStart lines
      where
        isMultilineStart (MultilineStart _, _) = True
        isMultilineStart _                     = False

    printBlank :: IO ()
    printBlank = do
      setBoldColor Blue
      putStr (replicate numberLength ' ' ++ " |")
      resetColor
      putStrLn ""

    printLineHeader :: String -> Bool -> IO ()
    printLineHeader str isMultiline = do
      setBoldColor Blue
      putStr (str ++ replicate (numberLength - length str) ' ' ++ " | ")
      if hasMultiline then
        if isMultiline then do
          setColor color
          putStr "> "
        else do
          putStr "  "
          resetColor
      else
        resetColor

    printAll :: Bool -> Int -> [StyledLine] -> IO ()
    printAll blankLast _ [] =
      if blankLast then
        return ()
      else
        printBlank
    printAll blankLast lineNumber ((style, line):rest) =
      case style of
        Plain -> do
          printLineHeader (show lineNumber) False
          putStrLn line
          printAll False (lineNumber+1) rest
        Skip n -> do
          when (not blankLast) $ do
            setBoldColor Blue
            putStr line
            resetColor
            putStrLn ""
          printAll True (lineNumber+n) rest
        MultilineStart { hlStart } -> do
          printLineHeader (show lineNumber) True
          resetColor
          let (a, b) = splitAt (hlStart-1) line
          putStr a
          setBoldColor color
          putStr b
          resetColor
          putStrLn ""
          printAll False (lineNumber+1) rest
        MultilineContinue -> do
          printLineHeader (show lineNumber) True
          putStr line
          resetColor
          putStrLn ""
          printAll False (lineNumber+1) rest
        MultilineEnd { hlEnd } -> do
          printLineHeader (show lineNumber) True
          let (a, b) = splitAt (hlEnd-1) line
          putStr a
          resetColor
          putStrLn b
          printAll False (lineNumber+1) rest
        Underline { hlStart, hlEnd } -> do
          printLineHeader (show lineNumber) False
          let (a, bc) = splitAt (hlStart-1) line
          putStr a
          setBoldColor color
          let (b, c) = splitAt (hlEnd-hlStart) bc
          putStr b
          resetColor
          putStrLn c
          printLineHeader "" False
          putStr (replicate (hlStart-1) ' ')
          setBoldColor color
          putStr (replicate (hlEnd-hlStart) '^')
          resetColor
          putStrLn ""
          printAll True (lineNumber+1) rest

-- | Checks if a line contains only spaces
isBlank :: String -> Bool
isBlank [] = True
isBlank (' ':xs) = isBlank xs
isBlank _ = False

-- Makes initial blank lines be skipped when printing them
trimLines :: [StyledLine] -> [StyledLine]
trimLines [] = []
trimLines (styledLine@(style, line) : rest) =
  if isOptional style && isBlank line then
    (Skip 1, breakSeparator) : rest
  else
    styledLine : trimLines rest
  where
    isOptional = \case
      Plain -> True
      MultilineContinue -> True
      _ -> False

-- | Finds the first column without spaces in a line
firstColumn :: String -> Maybe Int
firstColumn str = go 1 str
  where
    go n = \case
      ' ':rest ->
        go (n+1) rest
      [] -> Nothing
      _ -> Just n

-- | Finds the first column without spaces in a line, or 1 if the line is blank
firstColumnOr1 :: String -> Int
firstColumnOr1 = fromMaybe 1 . firstColumn

-- | Stores the state of a file as it is being traversed
data PrettyErrorState = PrettyErrorState
  { -- | The file that is currently loaded
    peCurrentFile :: !(Maybe FilePath)
    -- | Any lines that occurred before the current position, in reverse order
  , peBefore :: ![String]
    -- | Any remaining lines in the current file (requires a loaded file)
  , peAfter :: [String]
    -- | The current line number of the cursor in the file
  , peLine :: !Int }

-- | Default state with no file loaded
peDefault :: PrettyErrorState
peDefault = PrettyErrorState
  { peCurrentFile = Nothing
  , peBefore = []
  , peAfter = error "peAfter accessed uninitialized"
  , peLine = 0 }

-- | Makes sure the requested file has been loaded
setFile :: FilePath -> StateT PrettyErrorState IO ()
setFile file = do
  s <- get
  when (peCurrentFile s /= Just file) $ do
    contents <- lift $ readFile file
    put PrettyErrorState
      { peCurrentFile = Just file
      , peBefore = []
      , peAfter = lines contents
      , peLine = 1 }

-- | Advances to the requested line in the current file
advanceToLine :: Int -> StateT PrettyErrorState IO ()
advanceToLine startLine = do
  s <- get
  let
    currentLine = peLine s
    lineDifference = startLine - currentLine
  put $ go lineDifference s
  where
    go 0 s = s
    go n s =
      go (n-1) s
        { peBefore = before : peBefore s
        , peAfter = after
        , peLine = peLine s + 1 }
      where
        (before, after) =
          case peAfter s of
            []     -> ("", [])
            (x:xs) -> (x, xs)

-- | Given a starting and ending position, finds the context lines and highlighted lines
getLineRangeAndContext :: Position -> Position -> StateT PrettyErrorState IO ([String], [String])
getLineRangeAndContext spanStart spanEnd = do
  advanceToLine startLine
  s <- get
  let
    lines =
      case take lineCount $ peAfter s of
        [] -> ["<end of file>"]
        lines -> lines
    targetColumn =
      firstColumnOr1 $ head lines
    context _ [] = []
    context acc (line:rest) =
      case firstColumn line of
        Just column | column < targetColumn ->
          line : acc
        _ ->
          context (line:acc) rest
    contextLines
      | targetColumn == 1 = []
      | otherwise =
        context [] $ peBefore s
  return (contextLines, lines)
  where
    startLine = posLine spanStart
    lineCount = posLine spanEnd - startLine + 1

-- | Takes the first and last items of a list of 2 or more items
takeEnds :: [a] -> (a, [a], a)
takeEnds (first:rest) = go [] rest
  where
    go acc [last] =
      (first, reverse acc, last)
    go acc (next:rest) =
      go (next:acc) rest
    go _ [] = error "takeEnds called with singleton list"
takeEnds [] = error "takeEnds called with empty list"

-- | Styles the context lines, removing any unnecessary lines
createContextLines :: Bool -> [String] -> [StyledLine]
createContextLines hlAtStart context =
  if len <= 3 then
    mapPlain context
  else if hlAtStart then
    [ (Plain, head context)
    , (Skip (len-2), breakSeparator)
    , (Plain, last context) ]
    -- Include the previous line before the error if the error is at the start of the line
  else
    mapPlain (take 2 context) ++
    [(Skip (len-3), breakSeparator)]
  where
    len = length context
    mapPlain = map $ (,) Plain

-- | Styles the middle of a multiline seclection, skipping middle lines if it's too long
createMidSelection :: [String] -> [StyledLine]
createMidSelection lines =
  if len <= 5 then
    mapMulti lines
  else
    let
      (first, rest) = splitAt 2 lines
      last = last2 rest
    in
      mapMulti first
      ++ [(Skip (len-4), breakSeparator)]
      ++ mapMulti last
  where
    len = length lines
    mapMulti = map $ (,) MultilineContinue
    last2 bc@[_, _] = bc
    last2 (_:rest) = last2 rest

-- | Gets the color associated with an 'ErrorKind' for highlighting the code
errorColor :: ErrorKind -> Color
errorColor = \case
  Info    -> Blue
  Warning -> Yellow
  Error   -> Red
  Done    -> Green

-- | Formats and prints all compile errors in the set
prettyCompileErrors :: Set CompileError -> IO ()
prettyCompileErrors errs =
  evalStateT (go $ Set.toList errs) peDefault
  where
    go [] = return ()
    go (e:es) = do
      case errorFile e of
        Just file ->
          case errorSpan e of
            Just Span { spanStart, spanEnd } -> do
              lift $ putStrLn ("\n" ++ file ++ ":" ++ show spanStart ++ ":")
              setFile file
              let startLine = posLine spanStart
              (context, lines) <- getLineRangeAndContext spanStart spanEnd
              let
                startColumn = posColumn spanStart
                endColumn = posColumn spanEnd
                hlAtStart = startColumn <= firstColumnOr1 (head lines)
                contextStyledLines = createContextLines hlAtStart context
                contextStartLine = startLine - length context
                styledLines =
                  if length lines == 1 then
                    [(Underline startColumn endColumn, head lines)]
                  else
                    let (start, middle, end) = takeEnds lines in
                    [(MultilineStart startColumn, start)]
                    ++ createMidSelection middle
                    ++ [(MultilineEnd endColumn, end)]
              lift $ prettyLines color contextStartLine $
                trimLines $ contextStyledLines ++ styledLines
              printFooter
            Nothing -> do
              s <- get
              when (peLine s /= -1 || peCurrentFile s /= Just file) $
                lift $ putStrLn ("\n" ++ file ++ ": ")
              printFooter
              put peDefault
        Nothing -> do
          lift $ putStrLn ""
          printFooter
          put peDefault
      go es
      where
        color = errorColor $ errorKind e
        printFooter = lift $ do
          setBoldColor color
          let tag = "[" ++ show (errorKind e) ++ "]"
          putStr tag
          resetColor
          putStrLn (" " ++ intercalate ("\n " ++ replicate (length tag) ' ') (lines $ errorMessage e))

