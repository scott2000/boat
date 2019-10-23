module ErrorPrint (exitIfErrors, finishAndCheckErrors, addFatal) where

import Basics

import System.IO (readFile)
import System.Exit (exitFailure)

import Data.Maybe (fromMaybe)
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

addFatal :: CompileError -> CompileIO ()
addFatal e = do
  addError e
  exitIfErrors

printErrors :: CompileIO ()
printErrors =
  gets compileErrors >>= lift . prettyCompileErrors

data LineStyle
  -- Does no highlighting
  = Plain
  -- Skips a certain number of lines with the given separator
  | Skip !Int
  -- Multilines everything after hlStart
  | MultilineStart
    { hlStart :: !Int }
  -- Multilines entire line
  | MultilineContinue
  -- Multilines up until hlEnd
  | MultilineEnd
    { hlEnd :: !Int}
  -- Adds an underline after the line
  | Underline
    { hlStart :: !Int
    , hlEnd :: !Int }

type StyledLine = (LineStyle, String)

setColor :: Color -> IO ()
setColor color =
  setSGR [SetColor Foreground Vivid color]

setBoldColor :: Color -> IO ()
setBoldColor color =
  setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid color]

resetColor :: IO ()
resetColor = setSGR [Reset]

breakSeparator :: String
breakSeparator = "..."

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
      else do
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

data PrettyErrorState = PrettyErrorState
  { peCurrentFile :: !(Maybe FilePath)
  , peBefore :: ![String]
  , peAfter :: [String]
  , peLine :: !Int }

peDefault :: PrettyErrorState
peDefault = PrettyErrorState
  { peCurrentFile = Nothing
  , peBefore = []
  , peAfter = undefined
  , peLine = 0 }

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

firstColumn :: String -> Maybe Int
firstColumn str = go 1 str
  where
    go n = \case
      ' ':rest ->
        go (n+1) rest
      [] -> Nothing
      _ -> Just n

isBlank :: String -> Bool
isBlank [] = True
isBlank (' ':xs) = isBlank xs
isBlank _ = False

firstColumnOr1 :: String -> Int
firstColumnOr1 = fromMaybe 1 . firstColumn

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
    startColumn = posColumn spanStart
    endLine = posLine spanEnd
    lineCount = endLine - startLine + 1

takeEnds :: [a] -> (a, [a], a)
takeEnds (first:rest) = go [] rest
  where
    go acc [last] =
      (first, reverse acc, last)
    go acc (next:rest) =
      go (next:acc) rest

createContextLines :: Bool -> [String] -> [StyledLine]
createContextLines hlAtStart context =
  if len <= 3 then
    mapPlain context
  else if hlAtStart then
    [ (Plain, head context)
    , (Skip (len-2), breakSeparator)
    , (Plain, last context) ]
  else
    mapPlain (take 2 context) ++
    [(Skip (len-3), breakSeparator)]
  where
    len = length context
    mapPlain = map $ (,) Plain

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
              let
                startLine = posLine spanStart
                endLine = posLine spanEnd
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
