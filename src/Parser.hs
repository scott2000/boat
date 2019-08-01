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
      keyword "unary" *> nbsc *> pure Unary

parsePath :: Parser Path
parsePath =
  Path <$> ((:) <$> try parseName <*> many (char '.' *> parseName))

parseFile :: File -> Parser File
parseFile file =
  option file (try spaces >> (parseAll >>= parseFile) <|> (file <$ eof))
  where
    parseAll =
      parseUse
      <|> parseMod
      <|> parseLet
      <|> parseData
    parseUse =
      parseMeta (keyword "use" *> nbsc *> parseUseModule) <&> \use ->
        fileAddUse use file
    parseMod = do
      keyword "mod"
      name <- nbsc >> parseMeta parseName
      mod <- blockOf $ parseFile $ subFileOf file
      return $ fileAddMod name mod file
    parseLet = do
      keyword "let"
      name <- nbsc *> parseMeta parseName <* nbsc
      maybeAscription <- optional (specialOp TypeAscription *> blockOf parserExpectEnd <* nbsc)
      body <- specialOp Assignment >> parser
      let
        bodyWithAscription =
          case maybeAscription of
            Just ascription ->
              copySpan body $ ETypeAscribe body ascription
            Nothing ->
              body
      fileAddLet name bodyWithAscription file
    parseData = do
      keyword "data"
      name <- nbsc *> parseMeta parseName <* nbsc
      case extractLocalName $ unmeta name of
        Just local ->
          fail ("invalid data type name, did you mean to capitalize it like `" ++ capFirst local ++ "`?")
        Nothing ->
          return ()
      args <- blockOf $ manyUntil (specialOp Assignment) $ parseMeta $ do
        name <- parseName
        case extractLocalName name of
          Just local ->
            return local
          Nothing ->
            fail ("type parameters must start with a lowercase letter, instead found `" ++ show name ++ "`")
      vars <- blockOf $ someBetweenLines parseVariant
      fileAddData name args vars file

-- TODO: remove all uses of `try` with `parseName` after finding another solution to `_` keyword parsing

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
  variantFromType <$> parserExpectEnd >>= eitherToFail

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
    parsePrefix :: forall a. Parsable a => Parser a
    parsePrefix = do
      path <- try $ do
        offset <- getOffset
        path <- parseMeta (Local . Unary <$> operator)
        spaceAfter <- isSpace <$> nbsc
        if spaceAfter then do
          setOffset offset
          fail ("operator not allowed at start of " ++ opKind (Of :: Of a))
        else
          return path
      opUnary path <$> parserPrec compactPrec

type Prec = Int

expectEndPrec :: Prec
expectEndPrec = -1

minPrec, normalPrec, applyPrec, compactPrec :: Prec
minPrec     = 0
normalPrec  = 1
applyPrec   = 2
compactPrec = 3

parser :: Parsable a => Parser (Meta a)
parser = blockOf $ parserPrec minPrec

parserExpectEnd :: Parsable a => Parser (Meta a)
parserExpectEnd = parserPrec expectEndPrec

parserNoSpace :: Parsable a => Parser (Meta a)
parserNoSpace = parserPrec applyPrec

parserPrec :: Parsable a => Prec -> Parser (Meta a)
parserPrec prec = parserPartial >>= parserBase prec

parserBase :: forall a. Parsable a => Prec -> Meta a -> Parser (Meta a)
parserBase prec current =
  join (seqOpApp <|> return (return current))
  where
    seqOpApp =
      try $ do
        offset <- getOffset
        trySpaces >>= \case
          Right NoSpace -> opOrApp False
          Right Whitespace -> opOrApp True
          Right LineBreak ->
            if prec == minPrec then
              return $
                case opSeq of
                  Just f ->
                    metaExtendPrec f prec current
                  Nothing -> do
                    setOffset offset
                    fail "line breaks are only allowed in expressions"
            else
              empty
          Left err ->
            return $ fail $ show err

    opOrApp spaceBefore =
      op <|> app >>= \case
        Just x ->
          return x
        Nothing ->
          empty
      where
        op = try $ do
          offset <- getOffset
          parsedOp <- infixOp
          offsetAfterOp <- getOffset
          trySpaces >>= \case
            Right NoSpace ->
              opAfterSpace offset parsedOp False
            Right Whitespace ->
              opAfterSpace offset parsedOp True
            Right LineBreak ->
              return $ Just $ do
                setOffset offsetAfterOp
                fail "line break never allowed after operator"
            Left err ->
              return $ Just $ do
                setOffset offsetAfterOp
                fail $ show err

        opAfterSpace offset parsedOp spaceAfter = do
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
                    parserBase prec $ copySpan bin $ opParen bin
              Left op ->
                case parseSpecial op of
                  Nothing ->
                    if prec == minPrec then
                      return $ Just $ do
                        setOffset offset
                        fail ("special operator `" ++ show (snd op) ++ "` not allowed in " ++ opKind (Of :: Of a))
                    else
                      return Nothing
                  Just p ->
                    return $ Just $ p opPrec current
          else
            return Nothing

        app = do
          guard (prec < applyPrec)
          return $ Just $
            (metaExtendFail opApply applyPrec current >>= parserBase prec)
            <|> (return current)

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
  keyword "fun"
  EValue . VFun <$> blockOf matchCases

parseLet :: Parser Expr
parseLet = do
  keyword "let"
  pat <- blockOf parserExpectEnd
  nbsc >> specialOp Assignment
  val <- parser
  expr <- withBindings (bindingsForPat pat) parser
  return $ ELet pat val expr

parseMatch :: Parser Expr
parseMatch =
  pure EMatchIn
  <*  keyword "match"
  <*> blockOf (some (try spaces >> parserNoSpace))
  <*> blockOf matchCases

parseExprUse :: Parser Expr
parseExprUse =
  pure EUse
  <*  keyword "use"
  <*  nbsc
  <*> parseMeta parseUseModule
  <*> parser  

matchCases :: Parser [MatchCase]
matchCases = someBetweenLines matchCase

matchCase :: Parser MatchCase
matchCase = do
  pats <- someUntil (specialOp FunctionArrow) parserNoSpace
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

