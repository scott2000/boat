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
    parseBase current = try (sc' >> parseMeta (parseApp current) >>= parseBase) <|> return current

instance Parsable Expr where
  parseOne = label "expression" $
    parseExprIdent
    <|> parseExprIndex
    <|> parseFunction
    <|> parseLet
    <|> parseMatch

  parseApp a = EApp a <$> parsePartial

parseExprIdent :: Parser Expr
parseExprIdent = do
  name <- try identifier
  findBindingFor name <&> \case
    Nothing -> EGlobal name
    Just index -> EIndex index (Just name)

parseExprIndex :: Parser Expr
parseExprIndex =
  char '?' >> (try L.decimal <|> return 0) >>= index
  where
    index num = do
      count <- countBindings
      if num < count then
        bindingAtIndex num >>= \case
          Nothing ->
            return $ EIndex num Nothing
          Just name ->
            fail ("binding declared by name `" ++ name ++ "` should also be referred to by name")
      else if count == 0 then
        fail ("found De Bruijn index, but no bindings are in scope")
      else if count == 1 then
        fail ("found De Bruijn index of " ++ show num ++ ", but only 1 binding is in scope")
      else
        fail ("found De Bruijn index of " ++ show num ++ ", but only " ++ show count ++ " bindings are in scope")

parseFunction :: Parser Expr
parseFunction = do
  string "fun"
  EFun <$> blockOf (some matchCase)

parseLet :: Parser Expr
parseLet = do
  string "let"
  pat <- blockOf parser
  sc' >> string "="
  val <- blockOf parser
  sc' >> string "in"
  expr <- blockOf $ withBindings (bindingsForPat pat) parser
  return $ ELetIn pat val expr

parseMatch :: Parser Expr
parseMatch =
  pure EMatchIn
  <*  string "match"
  <*> blockOf (some parsePartial)
  <*  symbol (string "in")
  <*> blockOf (some matchCase)

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

