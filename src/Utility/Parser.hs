module Utility.Parser where

import Utility.Basics
import Utility.AST

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.List
import Data.Char
import Control.Monad.Reader
import qualified Data.List.NonEmpty as NonEmpty

data ParserState = ParserState
  { minIndent :: Int
  , multiline :: Bool
  , exprBindings :: [Maybe String] }

data SilentFail = SilentFail
  deriving (Show, Ord, Eq)

type InnerParser = ParsecT SilentFail String CompileIO
type Parser = ReaderT ParserState InnerParser

runCustomParser :: Parser a -> InnerParser a
runCustomParser p = runReaderT (followedByEnd p) defaultParserState

followedByEnd :: Parser a -> Parser a
followedByEnd p = p <* label "end of file" (try $ many spaceAnyIndent >> eof)

instance ShowErrorComponent SilentFail where
  showErrorComponent SilentFail = "<silent failure>"

convertParseErrors :: ParseErrorBundle String SilentFail -> CompileIO ()
convertParseErrors bundle =
  go initialPosState $ NonEmpty.toList $ bundleErrors bundle
  where
    initialPosState = bundlePosState bundle
    file = Just $ sourceName $ pstateSourcePos initialPosState
    go _ [] = return ()
    go posState (err:rest)
      | errLen == 0 = go posState rest
      | otherwise = do
        let
          o = errorOffset err
          posState' = reachOffsetNoLine o posState
          startPos = pstateSourcePos posState'
          errText = parseErrorTextPretty err
          endPos
            | errLen == 1 = startPos
            | otherwise = pstateSourcePos $ reachOffsetNoLine (o+errLen-1) posState'
        addError CompileError
          { errorFile = file
          , errorSpan = Just $ Span
            (Position (unPos $ sourceLine startPos) (unPos $ sourceColumn startPos))
            (Position (unPos $ sourceLine endPos) (unPos (sourceColumn endPos) + 1))
          , errorKind = Error
          , errorMessage = errText }
        go posState' rest
      where
        errLen =
          case err of
            TrivialError _ (Just (Tokens ts)) _ ->
              NonEmpty.length ts
            TrivialError _ _ _ -> 1
            FancyError _ xs ->
              foldl' fancyLenMax 1 xs
    fancyLenMax a = \case
      ErrorCustom SilentFail -> 0
      _ -> a

defaultParserState :: ParserState
defaultParserState = ParserState
  { minIndent = 0
  , multiline = True
  , exprBindings = [] }

isKeyword :: String -> Bool
isKeyword w = w `elem`
  [ "_"
  , "use"
  , "mod"
  , "operator"
  , "type"
  , "data"
  , "let"
  , "with"
  , "fun"
  , "match"
  , "in"
  , "unary"
  , "effect" ]

isIdentFirst, isIdentRest :: Char -> Bool
isIdentFirst x = (isAlpha x || x == '_') && isAscii x
isIdentRest  x = (isAlpha x || isDigit x || x == '_') && isAscii x

isOperatorChar :: Char -> Bool
isOperatorChar w = w `elem` ("+-*/%^!=<>:?|&~$." :: String)

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

getSpan :: Parser a -> Parser (Span, a)
getSpan p = andSpan <$> getPos <*> p <*> getPos
  where
    andSpan start res end = (Span start end, res)

parseMeta :: Parser a -> Parser (Meta a)
parseMeta p =
  uncurry metaWithSpan <$> getSpan p

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

getLevel :: Parser Int
getLevel = subtract 1 . unPos <$> L.indentLevel

getFilePath :: Parser FilePath
getFilePath =
  sourceName . pstateSourcePos . statePosState <$> getParserState

withBindings :: [Maybe String] -> Parser a -> Parser a
withBindings bindings = local $ \s -> s { exprBindings = reverse bindings ++ exprBindings s }

findBindingFor :: String -> Parser (Maybe Int)
findBindingFor name = do
  ParserState { exprBindings } <- ask
  return $ elemIndex (Just name) exprBindings

countBindings :: Parser Int
countBindings = asks (length . exprBindings)

bindingAtIndex :: Int -> Parser (Maybe String)
bindingAtIndex index = asks ((!! index) . exprBindings)

comment :: Parser ()
comment = hidden $ skipMany $ choice [lineCmnt, blockCmnt]

plainWhitespace :: Parser ()
plainWhitespace = void $ takeWhile1P Nothing isSpace
  where
    isSpace ' '  = True
    isSpace '\r' = True
    isSpace _    = False

parseSomeNewlines :: Parser Bool
parseSomeNewlines = fmap or $ hidden $ some $ choice
  [ plainWhitespace >> return False
  , char '\n' >> return True
  , lineCmnt  >> return False
  , blockCmnt  >> return False ]

data SpaceType
  = NoSpace
  | Whitespace
  | LineBreak

data SpaceError
  = ContinuationIndent Int
  | EndOfIndentedBlock

instance Show SpaceError where
  show = \case
    ContinuationIndent n ->
      "line continuation should be indented exactly 2 spaces more than its enclosing block (found " ++ show n ++ ")"
    EndOfIndentedBlock ->
      "unexpected end of indented block, is the indentation correct?"

trySpaces :: Parser (Either SpaceError SpaceType)
trySpaces =
  (parseSomeNewlines >>= ifSpaces) <|> return (Right NoSpace)
  where
    ifSpaces False =
      return $ Right Whitespace
    ifSpaces True = do
      ParserState { minIndent, multiline } <- ask
      -- getting the level here ensures that getting the position in a span is safe
      level <- getLevel
      if multiline then do
        case level - minIndent of
          0 ->
            return $ Right LineBreak
          2 ->
            return $ Right Whitespace
          n ->
            return $ Left $
              if n < 0 then
                EndOfIndentedBlock
              else
                ContinuationIndent n
      else do
        isEOF <- atEnd
        if isEOF then
          fail "unexpected end of input, did you forget a closing parenthesis or bracket?"
        else
          fail "line continuation not allowed unless directly inside indented block"

spaces :: Parser SpaceType
spaces =
  trySpaces >>= \case
    Right space -> return space
    Left err -> fail $ show err

spaceAnyIndent :: Parser ()
spaceAnyIndent = choice [plainWhitespace, void $ char '\n', lineCmnt, blockCmnt]

lineCmnt :: Parser ()
lineCmnt = hidden $ L.skipLineComment "--"

blockCmnt :: Parser ()
blockCmnt = hidden $ L.skipBlockCommentNested "{-" "-}"

nbsc :: Parser SpaceType
nbsc = do
  offset <- getOffset
  trySpaces >>= \case
    Right LineBreak -> do
      setOffset offset
      fail "unexpected line break"
    Right other ->
      return other
    Left EndOfIndentedBlock -> do
      setOffset offset
      fail "unexpected end of indented block"
    Left err ->
      fail $ show err

lineBreak :: Parser ()
lineBreak = do
  offset <- getOffset
  spaces >>= \case
    LineBreak ->
      return ()
    _ -> do
      setOffset offset
      fail "expected line break"

isSpace :: SpaceType -> Bool
isSpace NoSpace = False
isSpace _ = True

word :: Parser String
word = do
  first <- satisfy isIdentFirst
  rest <- takeWhileP Nothing isIdentRest
  return (first:rest)

identifier :: Parser String
identifier = label "identifier" $ do
  offset <- getOffset
  ident <- word
  if isKeyword ident then do
    setOffset offset
    unexpectedStr ident
  else
    return ident

keyword :: String -> Parser ()
keyword expected =
  expectStr expected $ try $ do
    offset <- getOffset
    ident <- word
    if ident == expected then
      return ()
    else do
      setOffset offset
      unexpectedStr ident

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

type PlainOp = String

data AnyOperator
  = ReservedOp ReservedOp
  | NonReservedOp NonReservedOp
  deriving Eq

instance Show AnyOperator where
  show = \case
    ReservedOp op    -> show op
    NonReservedOp op -> show op

data NonReservedOp
  = SpecialOp SpecialOp
  | PlainOp PlainOp
  deriving Eq

instance Show NonReservedOp where
  show = \case
    SpecialOp op -> show op
    PlainOp op   -> op

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

anySpecificOp :: AnyOperator -> Parser ()
anySpecificOp expected = label (show $ show expected) $ try $ do
  offset <- getOffset
  op <- anyOperator
  when (op /= expected) $ do
    setOffset offset
    unexpectedStr $ show op

reservedOp :: ReservedOp -> Parser ()
reservedOp = anySpecificOp . ReservedOp

specialOp :: SpecialOp -> Parser ()
specialOp = anySpecificOp . NonReservedOp . SpecialOp

plainOp :: PlainOp -> Parser ()
plainOp = anySpecificOp . NonReservedOp . PlainOp

nonReservedOp :: Parser NonReservedOp
nonReservedOp = label "operator" $ try $ do
  offset <- getOffset
  anyOperator >>= \case
    ReservedOp op -> do
      setOffset offset
      unexpectedStr $ show op
    NonReservedOp op ->
      return op

plainOrArrowOp :: Parser PlainOp
plainOrArrowOp = label "operator" $ try $ do
  offset <- getOffset
  nonReservedOp >>= \case
    SpecialOp FunctionArrow ->
      return $ show FunctionArrow
    SpecialOp op -> do
      setOffset offset
      unexpectedStr $ show op
    PlainOp op ->
      return op

unaryOp :: Parser PlainOp
unaryOp = label "plain operator" $ try $ do
  offset <- getOffset
  nonReservedOp >>= \case
    SpecialOp op -> do
      setOffset offset
      unexpectedStr $ show op
    PlainOp op ->
      return op

parseLabel :: Parser String
parseLabel = label "label" $
  char '<' *> word <* char '>'

expectLabel :: String -> Parser ()
expectLabel str =
  void $ string ("<" ++ str ++ ">")

expectStr :: String -> Parser a -> Parser a
expectStr s = label $ show s

unexpectedStr :: String -> Parser a
unexpectedStr = unexpected . Tokens . NonEmpty.fromList

addFail :: Maybe Span -> String -> Parser a
addFail maybeSpan msg = do
  file <- getFilePath
  span <-
    case maybeSpan of
      Nothing ->
        pointSpan <$> getPos
      Just span ->
        return span
  addError CompileError
    { errorFile = Just file
    , errorSpan = Just span
    , errorKind = Error
    , errorMessage = msg }
  customFailure SilentFail

