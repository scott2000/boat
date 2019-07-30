module Parser (module Parser.Base, Parsable (..), parser, parseFile) where

import Parser.Base
import AST

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Semigroup ((<>))
import Control.Monad.State.Strict

parseName :: Parser Name
parseName =
  parenOp <|> Identifier <$> identifier
  where
    parenOp = label "parenthesized operator" $
      char '(' *> nbsc *> (unaryOp <|> pure Operator) <*> operator <* nbsc <* char ')'
    unaryOp = label "keyword \"unary\"" $
      string "unary" *> nbsc *> pure Unary

parsePath :: Parser Path
parsePath = label "path" $
  Path <$> ((:) <$> try parseName <*> many (char '.' *> parseName))

parseFile :: File -> Parser File
parseFile file =
  spaces >> (parseAll >>= parseFile) <|> (file <$ eof)
  where
    parseAll = parseUse <|> parseLet <|> parseData
    parseUse =
      parseMeta (string "use" *> nbsc *> parseUseModule) <&> \use ->
        fileAddUse use file
    parseLet = do
      string "let"
      nameWithSpan <- nbsc *> getSpan parseName <* nbsc
      maybeAscription <- optional (char ':' *> parser <* nbsc)
      body <- char '=' >> parser
      let
        bodyWithAscription =
          case maybeAscription of
            Just ascription ->
              copySpan body $ ETypeAscribe body ascription
            Nothing ->
              body
      fileAddLet nameWithSpan bodyWithAscription file
    parseData = do
      string "data"
      nameWithSpan <- nbsc *> getSpan parseName <* nbsc
      case extractLocalName $ snd nameWithSpan of
        Just local ->
          fail ("invalid data type name, did you mean to capitalize it like `" ++ capFirst local ++ "`?")
        Nothing ->
          return ()
      args <- blockOf $ manyUntil (char '=') $ parseMeta $ do
        name <- parseName
        case extractLocalName name of
          Just local ->
            return local
          Nothing ->
            fail ("type parameters must start with a lowercase letter, instead found `" ++ show name ++ "`")
      vars <- blockOf $ someBetweenLines parseVariant
      fileAddData nameWithSpan args vars file

parseUseModule :: Parser UseModule
parseUseModule =
  (UseModule <$> try (parseMeta parseName) <*> parseUseContents)
  <|> (UseAny <$ char '_')

parseUseContents :: Parser (Maybe UseContents)
parseUseContents =
  (char '.' >> Just . UseDot <$> parseMeta parseUseModule)
  <|> (Just . UseAll <$> parseParen)
  <|> return Nothing
  where
    parseParen =
      nbsc *> char '(' *> parenInner <* spaces <* char ')'
    parenInner =
      blockOf $ parseCommaList $ parseMeta parseUseModule

parseCommaList :: Parser a -> Parser [a]
parseCommaList p =
  parseSomeCommaList p <|> return []

parseSomeCommaList :: Parser a -> Parser [a]
parseSomeCommaList p =
  (:) <$> p <*> manyCommas
  where
    manyCommas = option [] $ do
      try (spaces >> char ',') >> spaces
      option [] ((:) <$> p <*> manyCommas)

parseVariant :: Parser (Meta DataVariant)
parseVariant =
  variantFromType <$> parserPrec minPrec >>= eitherToFail

data InfixOp = InfixOp
  { infixBacktick :: Bool
  , infixPath :: Meta Path }

infixOp :: Parser (Either (Span, SpecialOp) InfixOp)
infixOp = label "operator" (backtickOp <|> normalOp)
  where
    backtickOp =
      Right . InfixOp True <$> parseMeta (char '`' *> parsePath <* char '`')
    normalOp =
      getSpan anyOperator <&> \case
        (span, Right op) ->
          Right $ InfixOp False $ metaWithSpan span $ Local $ Operator op
        (span, Left op) ->
          Left (span, op)

class (Show a, ExprLike a) => Parsable a where
  parseOne :: Parser a
  parseSpecial :: (Span, SpecialOp) -> Maybe (Prec -> Meta a -> Parser (Meta a))
  parseSpecial _ = Nothing

paren :: Parsable a => Parser (Meta a)
paren =
  parseMeta (char '(' *> (emptyParen <|> fullParen))
  where
    emptyParen = opUnit <$ char ')'
    fullParen = opParen <$> parser <* spaces <* char ')'

parserNoPrefix :: Parsable a => Parser (Meta a)
parserNoPrefix = parseMeta parseOne <|> hidden paren

parserPartial :: Parsable a => Parser (Meta a)
parserPartial = parseMeta parsePrefix <|> parserNoPrefix
  where
    parsePrefix = do
      path <- try $ do
        path <- parseMeta (Local . Unary <$> operator)
        spaceAfter <- isSpace <$> nbsc
        guard (not spaceAfter)
        return path
      opUnary path <$> parserPrec compactPrec

type Prec = Int

minPrec, normalPrec, applyPrec, compactPrec :: Prec
minPrec     = 0
normalPrec  = 1
applyPrec   = 2
compactPrec = 3

parser :: Parsable a => Parser (Meta a)
parser = blockOf $ parserPrec minPrec

parserNoSpace :: Parsable a => Parser (Meta a)
parserNoSpace = parserPrec applyPrec

parserPrec :: Parsable a => Prec -> Parser (Meta a)
parserPrec prec = parserPartial >>= parserBase prec

parserBase :: Parsable a => Prec -> Meta a -> Parser (Meta a)
parserBase prec current =
  ((seq <|> opOrApp) >>= parserBase prec) <|> return current
  where
    seq =
      case opSeq of
        Just f | prec == minPrec -> do
          try lineBreak
          metaExtendPrec f prec current
        _ -> empty

    opOrApp = join $ try $ do
      spaceBefore <- isSpace <$> nbsc
      Just x <- op spaceBefore <|> app
      return x
      where
        op spaceBefore = try $ do
          parsedOp <- infixOp
          spaceAfter <- isSpace <$> nbsc
          guard (spaceAfter || not spaceBefore)
          let
            isBacktick =
              case parsedOp of
                Right InfixOp { infixBacktick = True } -> True
                _ -> False
            opPrec =
              if spaceAfter || isBacktick then
                normalPrec
              else
                compactPrec
          if prec <= opPrec then
            case parsedOp of
              Right path ->
                return $ Just $ do
                  bin <- metaExtendPrec (opBinary $ infixPath path) opPrec current
                  if prec == opPrec then
                    return bin
                  else
                    return $ copySpan bin $ opParen bin
              Left op ->
                case parseSpecial op of
                  Nothing ->
                    return Nothing
                  Just p ->
                    return $ Just $ p opPrec current
          else
            return Nothing

        app = do
          guard (prec < applyPrec)
          return $ Just $ metaExtendFail opApply applyPrec current

eitherToFail :: Monad m => Either String a -> m a
eitherToFail (Right x) = return x
eitherToFail (Left err) = fail err

metaExtendPrec :: Parsable b => (Meta a -> Meta b -> c) -> Prec -> Meta a -> Parser (Meta c)
metaExtendPrec f prec current =
  parserPrec prec <&> \next ->
    metaWithEnds current next $ f current next

metaExtendFail
  :: Parsable b
  => (Meta a -> Meta b -> Either String c)
  -> Prec
  -> Meta a
  -> Parser (Meta c)
metaExtendFail f prec current = do
  next <- parserPrec prec
  metaWithEnds current next <$> eitherToFail (f current next)

instance Parsable Type where
  parseOne = label "type" $
    parseCapIdent "type" TPoly
    <|> (char '_' >> TAnon <$> getNewAnon)

  parseSpecial (span, FunctionArrow) =
    Just $ metaExtendPrec $ \a b ->
      let
        innerWithoutSpan =
          meta $ TApp (metaWithSpan span TFuncArrow) a
        innerWithSpan =
          case metaSpan a of
            Just aSpan ->
              innerWithoutSpan { metaSpan = Just (aSpan <> span) }
            Nothing ->
              innerWithoutSpan
      in
        TApp innerWithSpan b
  parseSpecial _ = Nothing

instance Parsable Expr where
  parseOne = label "expression" $
    -- identifiers must come first to avoid matching keyword prefix
    parseExprIdent
    <|> parseExprIndex
    <|> parseLet
    <|> parseFunction
    <|> parseMatch
    <|> parseExprUse

  parseSpecial (_, TypeAscription) =
    Just $ metaExtendPrec ETypeAscribe
  parseSpecial _ = Nothing

parseExprIdent :: Parser Expr
parseExprIdent = do
  path <- try parsePath
  case extractLocalPath path of
    Just local ->
      findBindingFor local <&> \case
        Just n ->
          EIndex n (Just local)
        Nothing ->
          EGlobal path
    Nothing ->
      return $ EGlobal path

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
  EValue . VFun <$> blockOf matchCases

parseLet :: Parser Expr
parseLet = do
  string "let"
  pat <- parser
  nbsc >> char '='
  val <- parser
  expr <- withBindings (bindingsForPat pat) parser
  return $ ELet pat val expr

parseMatch :: Parser Expr
parseMatch =
  pure EMatchIn
  <*  string "match"
  <*> blockOf (some (try spaces >> parserNoSpace))
  <*> blockOf matchCases

parseExprUse :: Parser Expr
parseExprUse =
  pure EUse
  <*  string "use"
  <*  nbsc
  <*> parseMeta parseUseModule
  <*> parser  

matchCases :: Parser [MatchCase]
matchCases = someBetweenLines matchCase

matchCase :: Parser MatchCase
matchCase = do
  pats <- someUntil (string "->") parserNoSpace
  expr <- withBindings (pats >>= bindingsForPat) parser
  return (pats, expr)

someBetweenLines :: Parser a -> Parser [a]
someBetweenLines p = (:) <$> p <*> many (try lineBreak >> p)

someUntil :: Parser a -> Parser b -> Parser [b]
someUntil end p =
  (:) <$> p <*> manyUntil end p

manyUntil :: Parser a -> Parser b -> Parser [b]
manyUntil end p =
  spaces >> (([] <$ end) <|> someUntil end p)

instance Parsable Pattern where
  parseOne = label "pattern" $
    parseCapIdent "pattern" (PBind . Just)
    <|> (PAny <$ char '_')
    <|> (PBind Nothing <$ char '?')

  parseSpecial (_, TypeAscription) =
    Just $ metaExtendPrec PTypeAscribe
  parseSpecial _ = Nothing

parseCapIdent :: ExprLike a => String -> (String -> a) -> Parser a
parseCapIdent kind localBind = do
  pathWithMeta <- parseMeta parsePath
  let path = unmeta pathWithMeta
  case extractLocalPath path of
    Just name ->
      return $ localBind $ name
    Nothing ->
      let components = unpath path in
      case last components of
        Identifier name
          | isLocalIdentifier name ->
            let alt = Path $ init components ++ [Identifier $ capFirst name] in
            fail ("invalid path for " ++ kind ++ ", did you mean to capitalize it like `" ++ show alt ++ "`?")
        _ ->
          return $ opNamed $ pathWithMeta

