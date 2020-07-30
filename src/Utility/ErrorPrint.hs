-- | Utilities for checking for errors and for formatting error messages
module Utility.ErrorPrint
  ( -- * Basic Errors
    CompileError (..)
  , AddError
  , addError

    -- * Fatal Errors
  , AddFatal
  , addFatal
  , compilerBug
  , compilerBugRawIO

    -- * Error Printing
  , footerPrefix
  , exitIfErrors
  , finishAndCheckErrors
  ) where

import Utility.Basics

import System.IO (readFile)
import System.Exit (exitFailure)

import Data.Maybe (fromMaybe)
import Data.List (intercalate, stripPrefix)
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State.Strict
import Control.Exception

import System.Console.ANSI

-- | Constraint for a 'Monad' that supports adding fatal errors (e.g. 'CompileIO')
type AddFatal = MonadCompile

-- | Add a fatal error (like 'addError', but never returns)
addFatal :: AddFatal m => CompileError -> m a
addFatal e = do
  addError e
  exitIfErrors
  compilerBug "addFatal did not exit!"

-- | If any errors occurred, print them and exit with failure
exitIfErrors :: MonadCompile m => m ()
exitIfErrors = do
  CompileOptions { compileExplainErrors } <- compileOptions
  CompileState { compileErrorCount = count } <- compileState
  when (errorCount count /= 0) do
    addError compileError
      { errorMessage =
        footerPrefix ++ "stopping due to " ++ show count ++
        if not compileExplainErrors && hasExplainError count then
          "\n(try --explain-errors for more info)"
        else
          "" }
    printErrors
    liftIO exitFailure

-- | Print any errors generated during compilation
finishAndCheckErrors :: MonadCompile m => m ()
finishAndCheckErrors = do
  exitIfErrors
  count <- compileErrorCount <$> compileState
  addError compileError
    { errorKind = Done
    , errorMessage =
      footerPrefix ++ "compiled successfully with " ++ show count }
  printErrors

-- | Header printed before an error message for a compiler bug
compilerBugBaseMessage :: String
compilerBugBaseMessage =
  footerPrefix ++ "something went wrong when compiling your code! (please report this compiler bug)\n"

-- | Prints an error message and exits (for use in code that should be unreachable)
compilerBug :: AddFatal m => String -> m a
compilerBug msg = do
  addError compileError
    { errorMessage = compilerBugBaseMessage ++ "error message: " ++ msg }
  printErrors
  liftIO exitFailure

-- | Like 'compilerBug', but doesn't require 'CompileIO' and prints a raw message
compilerBugRawIO :: CompileState -> String -> IO a
compilerBugRawIO state err = do
  prettyCompileErrors False $ Set.insert compileError
    { errorMessage = compilerBugBaseMessage ++ err } $ compileErrors state
  exitFailure

-- | A prefix that indicates a message should be printed last in its file
footerPrefix :: String
footerPrefix = "~!~"

-- | Prints all errors that have been generated
printErrors :: MonadCompile m => m ()
printErrors = liftCompile do
  CompileOptions { compileExplainErrors } <- compileOptions
  CompileState { compileErrors } <- compileState
  liftIO $ prettyCompileErrors compileExplainErrors compileErrors

-- | Gets a printable explanation of an 'ErrorCategory'
getExplanation :: ErrorCategory -> String
getExplanation = \case
  ECAssocOps ->
    " Many programming languages have a predefined table of operators that describes the precedence" ++
    " of each operator relative to each other. This comes with the limitation that either custom" ++
    " operators must be assigned an arbitrary number to place them in the precedence table (like in" ++
    " Haskell), or that custom operators are not allowed to decide a precedence or are disallowed" ++
    " entirely. To avoid these issues, Boat allows operators to describe their precedence relation" ++
    " to other operators directly.\n\n" ++
    " In order to use two operators together without using explicit parentheses, Boat requires that" ++
    " both operators have been assigned an operator type, and that either one operator type is defined" ++
    " to have higher precedence than the other or, if they have the same operator type, that there" ++
    " is a defined associativity for the operators (left or right) and the associativities are the same.\n\n" ++
    " Because operators are done this way, it is entirely possible for two operators to have no" ++
    " precedence relation at all, requiring explicit parentheses. This is a good feature because it" ++
    " means that operators defined in separate packages will not interact in confusing or hard-to-predict" ++
    " ways, but instead will simply require explicit parentheses. It is also important to note that" ++
    " an operator does not always need to be given an operator type. In this case, it simply must always" ++
    " be parenthesized when used with other operators."
  ECVariance ->
    " Although Boat does not allow subtypes in general, it does allow subtypes for effects." ++
    " Because of this, the compiler must infer extra information about the variance of parameters" ++
    " for data types. To understand why, first notice that `a -> b` is a subtype of `a -|IO|> b`," ++
    " meaning it can be used wherever a function producing a side effect is expected. This is an example" ++
    " of covariance, since the types are related in the same way that their effects are related.\n\n" ++
    " But this is not always the case. Often, types are related in the *opposite* way such as in" ++
    " function inputs. The type `(a -|IO|> b) -> c` is actually a subtype of `(a -> b) -> c`." ++
    " This is because the first function is strictly more general; it can take all of the valid" ++
    " inputs to the second function (pure functions) as well as taking additional inputs (impure" ++
    " functions). Because this is reversed from the effects' relationship, it is called contravariance." ++
    " The final kind of variance is called invariance. This occurs when the effect is used in both" ++
    " ways, so it must always exactly match.\n\n" ++
    " In Boat, covariance is called output variance and contravariance is called input variance to" ++
    " make it easier to remember. These types of variance are represented by (+), (-), and _ respectively."

-- | Splits a line into chunks that can be split across lines
lineToChunks :: String -> [(Int, String)]
lineToChunks = split [] []
  where
    toChunk []     n w = (n, w)
    toChunk (c:cs) n w =
      toChunk cs (n + 1) (c:w)

    prepend []   text = text
    prepend word text =
      toChunk word 0 [] : text

    joinFirst2 ((n0, w0):(n1, w1):rest) =
      (n1 + 1 + n0, w1 ++ (' ' : w0)) : rest
    joinFirst2 other = other

    findBacktick initialWord initialRest =
      go initialWord initialRest
      where
        go word = \case
          [] ->
            (initialWord, initialRest)
          ('\n':_) ->
            (initialWord, initialRest)
          ('`':rest) ->
            ('`':word, rest)
          (next:rest) ->
            findBacktick (next:word) rest

    split word text = \case
      [] ->
        reverse $ joinFirst2 $ prepend word text
      (' ':rest) ->
        split [] (prepend word text) rest
      ('\n':rest) ->
        split "\n" (prepend word text) rest
      ('`':rest) ->
        let (word', rest') = findBacktick ('`':word) rest in
        split word' text rest'
      (next:rest) ->
        split (next:word) text rest

-- | Formats a paragraph to fit within a specified line width
formatLineWidth :: Int -> String -> String
formatLineWidth columns =
  intercalate "\n" . map (format 0 . lineToChunks) . lines
  where
    format _ [] = ""
    format width ((n, w):rest)
      | width == 0 = w ++ format (width + n) rest
      | width' <= columns = ' ' : (w ++ format width' rest)
      | otherwise = '\n' : (w ++ format n rest)
      where
        width' = width + 1 + n

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
prettyLines :: Color -> Int -> Int -> [StyledLine] -> IO ()
prettyLines color firstLine lastLine lines = do
  printBlank
  printAll True firstLine lines
  where
    numberLength :: Int
    numberLength =
      length $ show lastLine

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
      putStr (replicate (numberLength - length str) ' ' ++ str ++ " | ")
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
          when (not blankLast) do
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
    peCurrentFile :: !File
    -- | Any lines that occurred before the current position, in reverse order
  , peBefore :: ![String]
    -- | Any remaining lines in the current file (requires a loaded file)
  , peAfter :: [String]
    -- | The current line number of the cursor in the file
  , peLine :: !Int
    -- | Keeps track of which 'ErrorCategory' kinds have been seen
  , peCategoriesSeen :: !(Set ErrorCategory) }

-- | Default state with no file loaded
peDefault :: PrettyErrorState
peDefault = PrettyErrorState
  { peCurrentFile = NoFile
  , peBefore = []
  , peAfter = error "peAfter accessed uninitialized"
  , peLine = 0
  , peCategoriesSeen = Set.empty }

-- | Makes sure the requested file has been loaded
setFile :: File -> StateT PrettyErrorState IO ()
setFile file = do
  s <- get
  when (peCurrentFile s /= file) do
    contents <- lift do
      readFile (filePathString file) `catch` \(_ :: IOException) ->
        -- If there is an error reading the file, pretend it's empty so the error still gets displayed
        return $ unlines $ repeat "<file not found>"
    modify \s -> s
      { peCurrentFile = file
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

-- | Checks if an 'ErrorCategory' has not yet been seen
unseenCategory :: ErrorCategory -> StateT PrettyErrorState IO Bool
unseenCategory cat = do
  s <- get
  let seen = peCategoriesSeen s
  if not $ cat `Set.member` seen then do
    put s { peCategoriesSeen = Set.insert cat seen }
    return True
  else
    return False

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

    isSingleWordLine line =
      case splitWords line of
        (_:_:_) -> False
        _ -> True

    isWordChar ch =
      isIdentRest ch || isOperatorChar ch

    splitWords line =
      case dropWhile (not . isWordChar) line of
        [] -> []
        trimmed ->
          let (word, rest) = span isWordChar trimmed in
          word : splitWords rest

    -- Look for the previous line with a lower indentation and include up to it for context. If the line only contains
    -- one word, then try the line immediately before it. If that line also contains only one word (or is blank), don't
    -- give anny context. Otherwise, add it onto the context as well.
    getContext _ [] = []
    getContext acc (line:rest) =
      case firstColumn line of
        Just column | column < targetColumn ->
          case rest of
            (line':_) | isSingleWordLine line ->
              case firstColumn line' of
                Just column' | not (isSingleWordLine line'), column' < column ->
                  line' : line : acc
                _ ->
                  []
            _ ->
              line : acc
        _ ->
          getContext (line:acc) rest

    contextLines
      | targetColumn == 1 = []
      | otherwise =
        getContext [] $ peBefore s
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
    last2 _ = error "last2 called on a list with too few elements"

-- | Gets the color associated with an 'ErrorKind' for highlighting the code
errorColor :: ErrorKind -> Color
errorColor = \case
  Info      -> Blue
  Warning   -> Yellow
  Error     -> Red
  Done      -> Green
  Explain e -> errorColor e
  _         -> error "errorColor called with special error"

-- | Prints the footer part of an error message, auto-formatting it if it starts with @\' \'@
printMessageFooter :: ErrorKind -> String -> IO ()
printMessageFooter errorKind errorMessage = do
  setBoldColor $ errorColor errorKind
  putStr tag
  resetColor
  putStrLn (" " ++ intercalate ("\n " ++ replicate tagLength ' ') (lines formattedMessage))
  where
    tag = "[" ++ show errorKind ++ "]"
    tagLength = length tag

    formattedMessage =
      case
        case stripPrefix footerPrefix errorMessage of
          Nothing -> errorMessage
          Just rest -> rest
      of
        (' ':x:multiline) | x /= ' ' ->
          -- Only do multiline formatting if there is a single space character
          formatLineWidth (79 - tagLength) (x:multiline)
        other -> other

-- | Formats and prints all compile errors in the set
prettyCompileErrors :: Bool -> Set CompileError -> IO ()
prettyCompileErrors explainEnabled errs =
  evalStateT (mapM_ go $ Set.toAscList errs) peDefault
  where
    go CompileError
      { errorFile
      , errorSpan
      , errorKind
      , errorCategory
      , errorExplain
      , errorMessage } = do
        forM_ errorCategory \cat -> do
          unseen <- unseenCategory cat
          when (explainEnabled && unseen) $ lift do
            putStrLn ""
            printMessageFooter Info $ getExplanation cat
        if null $ filePathString errorFile then
          lift $ putStrLn ""
        else
          case errorSpan of
            NoSpan -> do
              s <- get
              when (peLine s /= -1 || peCurrentFile s /= errorFile) $
                lift $ putStrLn ("\n" ++ show errorFile ++ ": ")
            Span { spanStart, spanEnd } -> do
              lift $ putStrLn ("\n" ++ show errorFile ++ ":" ++ show spanStart ++ ":")
              setFile errorFile
              let startLine = posLine spanStart
              (context, lines) <- getLineRangeAndContext spanStart spanEnd
              let
                startColumn = posColumn spanStart
                endColumn = posColumn spanEnd
                endLine = posLine spanEnd
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
              lift $ prettyLines (errorColor errorKind) contextStartLine endLine $
                trimLines $ contextStyledLines ++ styledLines
        lift $ printMessageFooter errorKind errorMessage
        case errorExplain of
          Just explain | explainEnabled -> lift do
            putStrLn ""
            printMessageFooter (Explain errorKind) explain
          _ -> return ()

