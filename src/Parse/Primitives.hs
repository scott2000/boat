-- | Primitives for parsing source code
module Parse.Primitives
  ( -- * Parser Types
    Parser
  , ParserState
  , runCustomParser
  , InnerParser
  , CustomFail
  , convertParseErrors

    -- * Parser State
  , getFilePath
  , withBindings
  , findBindingFor
  , countBindings
  , bindingAtIndex

    -- * Positions and Spans
  , getPos
  , getSpan
  , parseMeta

    -- * Indentation and Whitespace
  , blockOf
  , trySpaces
  , spaces
  , nbsc
  , lineBreak
  , SpaceType (..)
  , isSpace
  , SpaceError (..)
  , spaceErrorBacktrack
  , spaceErrorSingleLine
  , spaceErrorRecoverable
  , spaceErrorFail

    -- * Identifiers
  , identifier
  , keyword

    -- * Operators
  , AnyOperator (..)
  , anyOperator
  , anySpecificOp
  , ReservedOp (..)
  , reservedOp
  , NonReservedOp (..)
  , nonReservedOp
  , SpecialOp (..)
  , specialOp
  , PlainOp
  , plainOp
  , unaryOp
  , plainOrArrowOp

    -- * Labels
  , parseLabel
  , expectLabel

    -- * Error Messages
  , addFail
  , expectStr
  , unexpectedStr

    -- * Basic Combinators
  , parseSomeSeparatedList
  , parseSomeCommaList
  , someBetweenLines
  , someUntil
  , manyUntil
  ) where

import Utility

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.List
import Data.Char hiding (isSpace)
import Control.Monad.Reader
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set

-- | Additional state containing indentation information and local variable bindings
data ParserState = ParserState
  { -- | The minimum indentation level of the current block
    minIndent :: !Int
    -- | Whether the block supports line breaks
  , multiline :: !Bool
    -- | A set of bindings in scope with an optional name for each
  , exprBindings :: [Maybe String] }

-- | The default state for the parser
defaultParserState :: ParserState
defaultParserState = ParserState
  { minIndent = 0
  , multiline = True
  , exprBindings = [] }

-- | A custom failure implementation that just adds a 'CompileError'
data CustomFail = CustomFail
  { customCompileError :: CompileError }
  deriving (Ord, Eq)

-- | The 'ParsecT' that will be used for parsing
type InnerParser = ParsecT CustomFail String CompileIO

-- | The main parser that also carries some state information
type Parser = ReaderT ParserState InnerParser

-- | Supplies the default parser state to a 'Parser', yielding the 'InnerParser'
runCustomParser :: Parser a -> InnerParser a
runCustomParser p = runReaderT (followedByEnd p) defaultParserState

-- | Asserts that a given parser is followed by the end of the file
followedByEnd :: Parser a -> Parser a
followedByEnd p = p <* label "end of file" (try $ many spaceAnyIndent >> eof)

instance ShowErrorComponent CustomFail where
  showErrorComponent (CustomFail CompileError { errorMessage }) = errorMessage

-- | Converts all parse errors into compile errors to be displayed at the end of parsing
convertParseErrors :: ParseErrorBundle String CustomFail -> CompileIO ()
convertParseErrors bundle =
  go initialPosState $ NonEmpty.toList $ bundleErrors bundle
  where
    initialPosState = bundlePosState bundle
    file = Just $ sourceName $ pstateSourcePos initialPosState
    go _ [] = return ()
    go posState (err:rest) =
      case customFail of
        Just err -> do
          addError err
          go posState rest
        Nothing -> do
          let
            o = errorOffset err
            posState' = reachOffsetNoLine o posState
            startPos = pstateSourcePos posState'
            errText = parseErrorTextPretty err
            endPos
              | errLen == 1 = startPos
              | otherwise = pstateSourcePos $ reachOffsetNoLine (o+errLen-1) posState'
          addError compileError
            { errorFile = file
            , errorSpan = Just $ Span
              (Position (unPos $ sourceLine startPos) (unPos $ sourceColumn startPos))
              (Position (unPos $ sourceLine endPos) (unPos (sourceColumn endPos) + 1))
            , errorMessage = errText }
          go posState' rest
      where
        customFail =
          case err of
            FancyError _ s ->
              case Set.toList s of
                [ErrorCustom (CustomFail err)] ->
                  Just err
                _ ->
                  Nothing
            _ ->
              Nothing

        errLen =
          case err of
            TrivialError _ (Just (Tokens ts)) _ ->
              NonEmpty.length ts
            _ -> 1

-- | Checks if a character is valid at the start of an identifier
isIdentFirst :: Char -> Bool
isIdentFirst x = (isAlpha x || x == '_') && isAscii x

-- | Checks if a character is valid after the first character of an identifier
isIdentRest :: Char -> Bool
isIdentRest  x = (isAlpha x || isDigit x || x == '_') && isAscii x

-- | Checks if a character is valid in an infix or unary operator
isOperatorChar :: Char -> Bool
isOperatorChar w = w `elem` ("+-*/%^!=<>:?|&~$." :: String)

-- | Gets the current position in the file being parsed
getPos :: Parser Position
getPos = do
  -- The current state's position may fall behind the true position, but
  -- we always update state in `spaces` whenever there's a newline so the
  -- drift can only occur in one column. Therefore, we can easily adjust
  -- for the drift by subtracting the current offset from the state's.
  pstate <- statePosState <$> getParserState
  offset <- getOffset
  let
    pos = pstateSourcePos pstate
    baseOffset = pstateOffset pstate
    columnDiff = offset - baseOffset
  return Position
    { posLine = unPos (sourceLine pos)
    , posColumn = unPos (sourceColumn pos) + columnDiff }

-- | Runs a parser and returns the result along with the 'Span' of the parsed value
getSpan :: Parser a -> Parser (Span, a)
getSpan p = andSpan <$> getPos <*> p <*> getPos
  where
    andSpan start res end = (Span start end, res)

-- | Runs a parser and wraps it with additional 'Span' metadata
parseMeta :: Parser a -> Parser (Meta a)
parseMeta p =
  uncurry metaWithSpan <$> getSpan p

-- | Starts a new indented block containing the given parser
blockOf :: Parser a -> Parser a
blockOf p = do
  offset <- getOffset
  newLine <- option False parseSomeNewlines
  ParserState { minIndent } <- ask
  if newLine then do
    level <- getLevel
    case level `compare` minIndent of
      LT ->
        fail ("expected indented block with indentation greater than " ++ show minIndent
          ++ ", found indent of " ++ show level ++ " instead")
      EQ -> do
        setOffset offset
        fail ("expected indented block with indentation greater than surrounding block, "
          ++ "did you forget to put something here?")
      GT ->
        local (\s -> s { minIndent = level, multiline = True }) p
  else
    local (\s -> s { multiline = False }) p

-- | Gets the current indentation level (not cheap, but necessary to advance parser state)
getLevel :: Parser Int
getLevel = subtract 1 . unPos <$> L.indentLevel

-- | Gets the current file being parsed
getFilePath :: Parser FilePath
getFilePath =
  sourceName . pstateSourcePos . statePosState <$> getParserState

-- | Adds new bindings for local variables to the parser to be run
withBindings :: [Maybe String] -> Parser a -> Parser a
withBindings bindings = local \s -> s { exprBindings = reverse bindings ++ exprBindings s }

-- | Looks up a local variable binding and returns an index if it was found
findBindingFor :: String -> Parser (Maybe Int)
findBindingFor name = do
  ParserState { exprBindings } <- ask
  return $ elemIndex (Just name) exprBindings

-- | Counts the number of local variable bindings in scope
countBindings :: Parser Int
countBindings = asks (length . exprBindings)

-- | Looks up the local variable binding at the given index
bindingAtIndex :: Int -> Parser (Maybe String)
bindingAtIndex index = asks ((!! index) . exprBindings)

-- | Parses a single line comment
lineCmnt :: Parser ()
lineCmnt = hidden $ L.skipLineComment "--"

-- | Parses a single block comment (supports nested comments)
blockCmnt :: Parser ()
blockCmnt = hidden $ L.skipBlockCommentNested "{-" "-}"

-- | Ignores indentation rules and parses any whitespace at all
spaceAnyIndent :: Parser ()
spaceAnyIndent = choice [plainWhitespace, void $ char '\n', lineCmnt, blockCmnt]

-- | Parses a single comment
comment :: Parser ()
comment = hidden $ skipMany $ choice [lineCmnt, blockCmnt]

-- | Parses spaces and carriage return characters
plainWhitespace :: Parser ()
plainWhitespace = void $ takeWhile1P Nothing isSpace
  where
    isSpace ' '  = True
    isSpace '\r' = True
    isSpace _    = False

-- | Parses spaces, newlines, and comments and returns whether a newline was seen
parseSomeNewlines :: Parser Bool
parseSomeNewlines = fmap or $ hidden $ some $ choice
  [ plainWhitespace >> return False
  , char '\n' >> return True
  , lineCmnt  >> return False
  , blockCmnt  >> return False ]

-- | A type of error that can occur when parsing whitespace
data SpaceError
  = UnexpectedEndOfIndentedBlock
  | UnexpectedEndOfLine
  | UnexpectedLineBreak
  | UnexpectedContinuation
  | ContinuationIndent Int

instance Show SpaceError where
  show = \case
    UnexpectedEndOfIndentedBlock ->
      "unexpected end of indented block"
    UnexpectedEndOfLine ->
      "unexpected end of line, are you missing something here?"
    UnexpectedLineBreak ->
      "line break not allowed unless directly inside indented block"
    UnexpectedContinuation ->
      "line continuation not allowed unless directly inside indented block"
    ContinuationIndent n ->
      "line continuation should be indented exactly 2 spaces more than its enclosing block (found " ++ show n ++ ")"

-- | Checks whether a 'SpaceError' should be emitted before the parsed whitespace
spaceErrorBacktrack :: SpaceError -> Bool
spaceErrorBacktrack = \case
  UnexpectedEndOfIndentedBlock -> True
  UnexpectedEndOfLine -> True
  _ -> False

-- | Checks whether a 'SpaceError' can only occur if inside an inline block
spaceErrorSingleLine :: SpaceError -> Bool
spaceErrorSingleLine = \case
  UnexpectedEndOfLine -> True
  UnexpectedLineBreak -> True
  UnexpectedContinuation -> True
  _ -> False

-- | Checks whether a 'SpaceError' may be valid for some enclosing block
spaceErrorRecoverable :: SpaceError -> Bool
spaceErrorRecoverable = \case
  ContinuationIndent _ -> False
  _ -> True

-- | Given an offset, fails with a given 'SpaceError'
spaceErrorFail :: Int -> SpaceError -> Parser a
spaceErrorFail offset err = do
  when (spaceErrorBacktrack err) $
    setOffset offset
  fail $ show err

-- | The types of spaces that may be parsed by 'trySpaces'
data SpaceType
  = NoSpace
  | Whitespace
  | LineBreak

-- | Tries to parse some spaces in the current indentation
trySpaces :: Parser (Either SpaceError SpaceType)
trySpaces =
  (parseSomeNewlines >>= ifSpaces) <|> return (Right NoSpace)
  where
    ifSpaces False =
      return $ Right Whitespace
    ifSpaces True = do
      ParserState { minIndent, multiline } <- ask
      -- Getting the level here ensures that getting the position in a span is safe
      level <- getLevel
      isEOF <- atEnd
      let
        adjustedLevel
          | isEOF = 0
          | otherwise = level
      if multiline then do
        case adjustedLevel - minIndent of
          0 ->
            return $ Right LineBreak
          2 ->
            return $ Right Whitespace
          n ->
            return $ Left $
              if n < 0 then
                UnexpectedEndOfIndentedBlock
              else
                ContinuationIndent n
      else
        return $ Left $
          case adjustedLevel `compare` minIndent of
            LT -> UnexpectedEndOfLine
            EQ -> UnexpectedLineBreak
            GT -> UnexpectedContinuation

-- | Parses some spaces and automatically fails on a 'SpaceError'
spaces :: Parser SpaceType
spaces = do
  offset <- getOffset
  trySpaces >>= \case
    Right space -> return space
    Left err -> spaceErrorFail offset err

-- | Parses any non-linebreak whitespace
nbsc :: Parser SpaceType
nbsc = do
  offset <- getOffset
  trySpaces >>= \case
    Right LineBreak -> do
      setOffset offset
      fail "unexpected line break"
    Right other ->
      return other
    Left err ->
      spaceErrorFail offset err

-- | Parses a line break
lineBreak :: Parser ()
lineBreak = do
  offset <- getOffset
  trySpaces >>= \case
    Right LineBreak ->
      return ()
    Right _ -> do
      setOffset offset
      fail "expected line break"
    Left err ->
      spaceErrorFail offset err

-- | Checks if any whitespace was parsed at all
isSpace :: SpaceType -> Bool
isSpace NoSpace = False
isSpace _ = True

-- | Parses a single word (an identifier or a keyword)
word :: Parser String
word = do
  first <- satisfy isIdentFirst
  rest <- takeWhileP Nothing isIdentRest
  return (first:rest)

-- | Parses a single identifier
identifier :: Parser String
identifier = label "identifier" do
  offset <- getOffset
  ident <- word
  if isKeyword ident then do
    setOffset offset
    unexpectedStr ident
  else
    return ident

-- | Parses an expected keyword
keyword :: String -> Parser ()
keyword expected =
  expectStr expected $ try do
    offset <- getOffset
    ident <- word
    if ident == expected then
      return ()
    else do
      setOffset offset
      unexpectedStr ident

-- | A reserved operator that may be used outside of infix positions
data ReservedOp
  = PathDot
  | QuestionMark
  | PipeSeparator
  deriving Eq

instance Show ReservedOp where
  show = \case
    PathDot       -> "."
    QuestionMark  -> "?"
    PipeSeparator -> "|"

-- | A special operator that may have special meanings in some or all contexts
data SpecialOp
  = Assignment
  | FunctionArrow
  | SplitArrow
  | TypeAscription
  deriving Eq

instance Show SpecialOp where
  show = \case
    Assignment     -> "="
    FunctionArrow  -> "->"
    SplitArrow     -> "-|"
    TypeAscription -> ":"

-- | A plain operator that can be defined by a user
type PlainOp = String

-- | Any kind of operator at all
data AnyOperator
  = ReservedOp ReservedOp
  | NonReservedOp NonReservedOp
  deriving Eq

instance Show AnyOperator where
  show = \case
    ReservedOp op    -> show op
    NonReservedOp op -> show op

-- | A non-reserved operator
data NonReservedOp
  = SpecialOp SpecialOp
  | PlainOp PlainOp
  deriving Eq

instance Show NonReservedOp where
  show = \case
    SpecialOp op -> show op
    PlainOp op   -> op

-- | Parses any kind of operator at all
anyOperator :: Parser AnyOperator
anyOperator = do
  op <- takeWhile1P Nothing isOperatorChar
  return $
    case op of
      "."  -> ReservedOp PathDot
      "?"  -> ReservedOp QuestionMark
      "|"  -> ReservedOp PipeSeparator
      "="  -> NonReservedOp $ SpecialOp Assignment
      "->" -> NonReservedOp $ SpecialOp FunctionArrow
      "-|" -> NonReservedOp $ SpecialOp SplitArrow
      ":"  -> NonReservedOp $ SpecialOp TypeAscription
      _    -> NonReservedOp $ PlainOp op

-- | Parses a specific requested operator
anySpecificOp :: AnyOperator -> Parser ()
anySpecificOp expected = label (show $ show expected) $ try do
  offset <- getOffset
  op <- anyOperator
  when (op /= expected) do
    setOffset offset
    unexpectedStr $ show op

-- | Parses a specific reserved operator
reservedOp :: ReservedOp -> Parser ()
reservedOp = anySpecificOp . ReservedOp

-- | Parses a specific special operator
specialOp :: SpecialOp -> Parser ()
specialOp = anySpecificOp . NonReservedOp . SpecialOp

-- | Parses a specific plain operator
plainOp :: PlainOp -> Parser ()
plainOp = anySpecificOp . NonReservedOp . PlainOp

-- | Parses any non-reserved operator
nonReservedOp :: Parser NonReservedOp
nonReservedOp = label "operator" $ try do
  offset <- getOffset
  anyOperator >>= \case
    ReservedOp op -> do
      setOffset offset
      unexpectedStr $ show op
    NonReservedOp op ->
      return op

-- | Parses a plain operator or a function arrow
plainOrArrowOp :: Parser PlainOp
plainOrArrowOp = label "operator" $ try do
  offset <- getOffset
  nonReservedOp >>= \case
    SpecialOp FunctionArrow ->
      return $ show FunctionArrow
    SpecialOp op -> do
      setOffset offset
      unexpectedStr $ show op
    PlainOp op ->
      return op

-- | Parses a unary operator which is also just a plain operator
unaryOp :: Parser PlainOp
unaryOp = label "unary operator" $ try do
  offset <- getOffset
  nonReservedOp >>= \case
    SpecialOp op -> do
      setOffset offset
      unexpectedStr $ show op
    PlainOp op ->
      return op

-- | Parses a single label
parseLabel :: Parser String
parseLabel = label "label" $
  char '<' *> word <* char '>'

-- | Parses a specific expected label
expectLabel :: String -> Parser ()
expectLabel str =
  void $ string ("<" ++ str ++ ">")

-- | Labels a parser as expecting a certain string
expectStr :: String -> Parser a -> Parser a
expectStr s = label $ show s

-- | Fails with an unexpected string that was encountered
unexpectedStr :: String -> Parser a
unexpectedStr = unexpected . Tokens . NonEmpty.fromList

-- | Fails with a certain error message at a given span
addFail :: Maybe Span -> String -> Parser a
addFail maybeSpan msg = do
  file <- getFilePath
  span <-
    case maybeSpan of
      Nothing ->
        pointSpan <$> getPos
      Just span ->
        return span
  customFailure $ CustomFail compileError
    { errorFile = Just file
    , errorSpan = Just span
    , errorMessage = msg }

-- | Parses a list of items separated by a character
parseSomeSeparatedList :: Char -> Parser a -> Parser [a]
parseSomeSeparatedList sep p =
  (:) <$> p <*> manyCommas
  where
    manyCommas = option [] do
      try (spaces >> char sep) >> spaces
      option [] ((:) <$> p <*> manyCommas)

-- | Parses a list of items separated by a comma
parseSomeCommaList :: Parser a -> Parser [a]
parseSomeCommaList = parseSomeSeparatedList ','

-- | Parses a list of items separated by line breaks
someBetweenLines :: Parser a -> Parser [a]
someBetweenLines p = (:) <$> p <*> many (try lineBreak >> p)

-- | Parses an item at least once until a given parser succeeds
someUntil :: Parser a -> Parser b -> Parser [b]
someUntil end p =
  (:) <$> p <*> manyUntil end p

-- | Parses an item any number of times until a given parser succeeds
manyUntil :: Parser a -> Parser b -> Parser [b]
manyUntil end p =
  spaces >> (([] <$ end) <|> someUntil end p)

