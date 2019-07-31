module Parser.Base where

import AST

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Void
import Data.List
import Data.Char
import Control.Monad.Reader
import Control.Monad.State.Strict

data Assoc
  = ALeft
  | ANon
  | ARight

data ParserState = ParserState 
  { minIndent :: Int
  , multiline :: Bool
  , exprBindings :: [Maybe String] }

type InnerParser = ParsecT Void String CompileIO
type Parser = ReaderT ParserState InnerParser

runCustomParser :: Parser a -> InnerParser a
runCustomParser p = runReaderT (followedByEnd p) defaultParserState

followedByEnd :: Parser a -> Parser a
followedByEnd p = p <* many spaceAnyIndent <* eof

defaultParserState :: ParserState
defaultParserState = ParserState
  { minIndent = 0
  , multiline = True
  , exprBindings = [] }

isKeyword, isReservedOp :: String -> Bool
isKeyword    w = w `elem` ["_", "use", "data", "fun", "let", "match", "in", "unary"]
isReservedOp w = w `elem` [".", "?", ","]

getPos :: Parser Position
getPos = toPosition . pstateSourcePos . statePosState <$> getParserState
  where
    toPosition s = Position
      { posLine = unPos $ sourceLine s
      , posColumn = unPos $ sourceColumn s }

getSpan :: Parser a -> Parser (Span, a)
getSpan p = andSpan <$> getPos <*> p <*> getPos
  where
    andSpan start res end = (Span start end, res)

parseMeta :: Parser a -> Parser (Meta a)
parseMeta p =
  uncurry metaWithSpan <$> getSpan p

blockOf :: Parser a -> Parser a
blockOf p = do
  newLine <- option False parseSomeNewlines
  ParserState { minIndent } <- ask
  if newLine then do
    level <- getLevel
    if level < minIndent then
      fail ("block indented less then containing block (" ++ show level ++ " < " ++ show minIndent ++ ")")
    else
      local (\s -> s { minIndent = level, multiline = True }) p
  else
    local (\s -> s { multiline = False }) p

getLevel :: Parser Int
getLevel = subtract 1 . unPos <$> L.indentLevel

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

spaces :: Parser SpaceType
spaces = (parseSomeNewlines >>= ifSpaces) <|> return NoSpace
  where
    ifSpaces False =
      return Whitespace
    ifSpaces True = do
      ParserState { minIndent, multiline } <- ask
      if multiline then do
        level <- getLevel
        case level - minIndent of
          0 ->
            return LineBreak
          2 ->
            return Whitespace
          n ->
            if n < 0 then
              fail "unexpected end of indented block"
            else
              fail "line continuation should be indented exactly 2 spaces more than its enclosing block"
      else
        fail "line continuation not allowed unless inside of a block"

spaceAnyIndent :: Parser ()
spaceAnyIndent = choice [plainWhitespace, void $ char '\n', lineCmnt, blockCmnt]

lineCmnt :: Parser ()
lineCmnt = hidden $ L.skipLineComment "--"

blockCmnt :: Parser ()
blockCmnt = hidden $ L.skipBlockCommentNested "{-" "-}"

nbsc :: Parser SpaceType
nbsc = spaces >>= \case
  LineBreak ->
    fail "unexpected line break in indented block"
  other ->
    return other

lineBreak :: Parser ()
lineBreak = spaces >>= \case
  LineBreak ->
    return ()
  _ ->
    fail "expected line break in indented block"

isSpace :: SpaceType -> Bool
isSpace NoSpace = False
isSpace _ = True

word :: Parser String
word = do
  first <- satisfy isIdentFirst
  rest <- takeWhileP Nothing isIdentRest
  return (first:rest)
  where
    isIdentFirst x = (isAlpha x || x == '_') && isAscii x
    isIdentRest x = (isAlpha x || isDigit x || x == '_') && isAscii x

identifier :: Parser String
identifier = label "identifier" $ do
  ident <- word
  if isKeyword ident then
    fail ("expected identifier, found keyword `" ++ ident ++ "`")
  else
    return ident

data SpecialOp
  = Assignment
  | FunctionArrow
  | TypeAscription

instance Show SpecialOp where
  show Assignment = "="
  show FunctionArrow = "->"
  show TypeAscription = ":"

isAllowedInParen :: SpecialOp -> Bool
isAllowedInParen = \case
  FunctionArrow -> True
  _ -> False

anyOperator :: Parser (Either SpecialOp String)
anyOperator = label "operator" $ do
  op <- some $ oneOf ("+-*/%^!=<>:?|&~$." :: String)
  guard $ not $ isReservedOp op
  return $ case op of
    "=" -> Left Assignment
    "->" -> Left FunctionArrow
    ":" -> Left TypeAscription
    _ -> Right op

operator :: Parser String
operator = anyOperator >>= \case
  Right op ->
    return op
  Left op ->
    if isAllowedInParen op then
      return $ show op
    else
      fail ("unexpected special operator `" ++ show op ++ "`")
