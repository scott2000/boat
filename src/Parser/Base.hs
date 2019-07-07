module Parser.Base where

import AST

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Void
import Data.List
import Data.Char
import Control.Monad.Reader
import qualified Data.Set as Set
import qualified Control.Monad.State.Strict as ST (State)

data ParserState = ParserState 
  { minIndent :: Int
  , multiline :: Bool
  , exprBindings :: [Maybe String] }

type InnerParser = ParsecT Void String (ST.State CompilerState)
type Parser = ReaderT ParserState InnerParser

runCustomParser :: Parser a -> InnerParser a
runCustomParser p = runReaderT (followedByEnd p) defaultParserState

followedByEnd :: Parser a -> Parser a
followedByEnd p = p <* sc' <* eof

defaultParserState :: ParserState
defaultParserState = ParserState { minIndent = 0, multiline = True, exprBindings = [] }

keywords :: [String]
keywords = ["fun", "let", "let", "match", "in"]

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
  newLine <- anySpaceChunk
  ParserState { minIndent } <- ask
  if newLine then do
    level <- subtract 1 . unPos <$> L.indentLevel
    if level < minIndent then
      fail ("block indented less then containing block (" ++ show level ++ " < " ++ show minIndent ++ ")")
    else
      local (\s -> s { minIndent = level, multiline = True }) p
  else
    local (\s -> s { multiline = False }) p

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

symbol :: Parser a -> Parser a
symbol p = sc' >> p

comment :: Parser ()
comment = hidden $ skipMany $ choice [lineCmnt, blockCmnt]

whitespace :: Parser ()
whitespace = void $ takeWhile1P Nothing isSpace
  where
    isSpace ' '  = True
    isSpace '\r' = True
    isSpace _    = False

indentedNewline :: Parser ()
indentedNewline = do
  ParserState { minIndent, multiline } <- ask
  if multiline then do
    char '\n'
    parseSpaces minIndent
  else
    fail "newline not allowed here"

parseSpaces :: Int -> Parser ()
parseSpaces minIndent = go 0
  where
    go :: Int -> Parser ()
    go n = ((lineCmnt <|> blockCmnt) >> go 0) <|> (token cont Set.empty >>= id) <|> stop
      where
        cont ' '  = Just $ go (n+1)
        cont '\n' = Just $ go 0
        cont '\r' = Just $ go n
        cont _    = Nothing
        stop
          | n == minIndent = return ()
          | otherwise =
            fail ("expected indent of " ++ show minIndent ++ ", found " ++ show n)

spaceChunk :: Parser ()
spaceChunk = choice [whitespace, indentedNewline, lineCmnt, blockCmnt]

anySpaceChunk :: Parser Bool
anySpaceChunk = fmap (foldr (||) False) $ hidden $ many $ choice
  [ whitespace >> return False,
    char '\n' >> return True,
    lineCmnt  >> return False,
    blockCmnt  >> return False ]

lookAheadSpace :: Parser ()
lookAheadSpace = choice [whitespace, void $ char '\n', lineCmnt, blockCmnt]

lineCmnt :: Parser ()
lineCmnt = hidden $ L.skipLineComment "--"

blockCmnt :: Parser ()
blockCmnt = hidden $ L.skipBlockCommentNested "{-" "-}"

sc :: Parser ()
sc = label "whitespace" $ skipSome spaceChunk

sc' :: Parser ()
sc' = hidden $ skipMany spaceChunk

word :: Parser String
word = do
  first <- satisfy isIdentFirst
  rest <- takeWhileP Nothing isIdentRest
  return (first:rest)
  where
    isIdentFirst x = (isAlpha x || x == '_') && isAscii x
    isIdentRest x = (isAlpha x || isDigit x || x == '_') && isAscii x

identifier :: Parser String
identifier = label "identifier" $ symbol $ do
  ident <- word
  if ident `elem` keywords then
    fail "expected identifier"
  else
    return ident
