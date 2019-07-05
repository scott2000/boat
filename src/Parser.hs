module Parser (module Parser.Base, Parsable (..), parser) where

import Parser.Base
import AST

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Control.Monad.State.Strict
import Control.Monad.Reader

class Parsable a where
  parseOne :: Parser a
  parseApp :: Meta a -> Parser a

paren :: Parsable a => Parser (Meta a)
paren = char '(' *> parser <* char ')'

parsePartial :: Parsable a => Parser (Meta a)
parsePartial = hidden paren <|> parseMeta parseOne

parser :: Parsable a => Parser (Meta a)
parser = try sc' >> parsePartial >>= parseBase
  where
    parseBase current = (try sc' >> parseMeta (parseApp current) >>= parseBase) <|> return current

instance Parsable Expr where
  parseOne = label "expression" $
    parseExprIdent
    <|> parseExprIndex
    <|> parseFunction

  parseApp a = EApp a <$> parsePartial

parseExprIdent :: Parser Expr
parseExprIdent = do
  name <- try identifier
  findBindingFor name <&> \case
    Nothing -> EGlobal name
    Just index -> EIndex index (Just name)

parseExprIndex :: Parser Expr
parseExprIndex =
  char '?' >> (index <$> try L.decimal <|> return (index 0))
  where
    index num = EIndex num Nothing

parseFunction :: Parser Expr
parseFunction = do
  string "fun"
  EFun <$> blockOf (some matchCase)

matchCase :: Parser MatchCase
matchCase = do
  pats <- try somePatterns
  expr <- withBindings (pats >>= bindingsForPat) $ blockOf parser
  return (pats, expr)
  where
    somePatterns = do
      p <- symbol $ parsePartial
      (p:) <$> manyPatterns
    manyPatterns = symbol $ ((string "->" >> return []) <|> somePatterns)

instance Parsable Pattern where
  parseOne = label "pattern" $
    (char '_' >> return PAny)
    <|> (char '?' >> return (PBind Nothing))
    <|> parsePatIdent

  parseApp Meta { unmeta = PCons name xs } = parsePartial <&> \x -> PCons name (xs ++ [x])
  parseApp other = fail ("pattern does not support parameters: " ++ show other)

parsePatIdent :: Parser Pattern
parsePatIdent =
  parseMeta identifier <&> \nameWithMeta ->
    let name = unmeta nameWithMeta in
    if isCap $ head name then
      PCons nameWithMeta []
    else
      PBind $ Just name

