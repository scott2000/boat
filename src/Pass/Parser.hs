module Pass.Parser (Parsable (..), parseFile) where

import Utility.Basics
import Utility.AST
import Utility.Program
import Utility.Parser

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Maybe
import Data.Semigroup ((<>))
import qualified Data.Set as Set
import Control.Monad.State.Strict

parseName :: Parser Name
parseName =
  parseParen <|> Identifier <$> identifier
  where
    parseParen = label "parenthesized operator" $
      char '(' *> nbsc *> (parseUnary <|> Operator <$> plainOrArrowOp) <* nbsc <* char ')'
    parseUnary = label "keyword \"unary\"" $
      keyword "unary" >> nbsc >> Unary <$> unaryOp

parsePath :: Parser Path
parsePath =
  Path <$> ((:) <$> try parseName <*> many (reservedOp PathDot *> parseName))

parseFile :: FilePath -> Parser Module
parseFile path = parseModule defaultModule
  where
    parseModule m =
      option m (try spaces >> (parseAll >>= parseModule) <|> (m <$ eof))
      where
        parseAll =
          parseUse
          <|> parseMod
          <|> parseLet
          <|> parseData
          <|> parseEffect
          <|> parseOperator

        parseUse =
          keyword "use" *> nbsc *> parseMeta parseUseModule <&> \use ->
            modAddUse use path m

        parseMod = do
          keyword "mod"
          name <- nbsc >> parseName
          nbsc >> specialOp Assignment
          sub <- blockOf $ parseModule defaultModule
          return $ modAddSub name sub m

        parseOperator = do
          keyword "operator"
          nbsc >> (keyword "type" >> blockOf operatorType) <|> operatorDecl
          where
            operatorType = do
              ops <- parseSomeSeparatedList '<' operatorPart
              return $ modAddOpType ops path m
            operatorPart =
              try (OpLink <$> parseMeta (char '(' *> parsePath <* spaces <* char ')'))
              <|> (OpDeclare <$> parseMeta parseName)
            operatorDecl = do
              opAssoc <- option ANon (operatorAssoc <* nbsc)
              names <- someUntil (specialOp TypeAscription) $ parseMeta parseName
              opType <- nbsc >> parseMeta parsePath
              let decl = OpDecl { opAssoc, opType }
              modAddOpDecls names decl path m
            operatorAssoc =
              (ALeft <$ expectLabel "left")
              <|> (ARight <$ expectLabel "right")

        parseEffect = do
          keyword "effect"
          name <- nbsc >> parseMeta parseName
          effectSuper <- optional (try nbsc >> specialOp TypeAscription >> blockOf (parseMeta parsePath))
          modAddEffect name EffectDecl { effectSuper } path m

        parseLet = do
          keyword "let"
          name <- nbsc *> parseMeta parseName <* nbsc
          maybeAscription <- optional (specialOp TypeAscription *> blockOf parserExpectEnd <* nbsc)
          constraints <- (parseConstraints <* nbsc) <|> pure []
          body <- specialOp Assignment >> blockOf parser
          let
            bodyWithAscription =
              case maybeAscription of
                Just ascription ->
                  copySpan body $ ETypeAscribe body ascription
                Nothing ->
                  body
            letDecl = LetDecl
              { letBody = bodyWithAscription
              , letConstraints = constraints }
          modAddLet name letDecl path m

        parseData = do
          keyword "data" >> nbsc
          isMod <- (keyword "mod" >> nbsc >> return True) <|> return False
          nameAndParams <-
            parserExpectEnd >>= dataAndArgsFromType path
          nbsc >> specialOp Assignment
          vars <- blockOf $
            someBetweenLines (parserExpectEnd >>= variantFromType path)
          case (nameAndParams, catMaybes vars) of
            ((Just name, effs, params), vars) ->
              let
                dataDecl = DataDecl
                  { dataMod = isMod
                  , dataArgs = params
                  , dataEffects = effs
                  , dataVariants = vars }
              in
                modAddData name dataDecl path m
            _ ->
              return m

-- TODO: remove all uses of `try` with `parseName` after finding another solution to `_` keyword parsing

parseConstraints :: Parser [Constraint]
parseConstraints = do
  keyword "with"
  blockOf $ parseSomeCommaList parseConstraint

parseConstraint :: Parser Constraint
parseConstraint =
  pure IsSubEffectOf
  <*> parseEffect
  <*  nbsc
  <*  specialOp TypeAscription
  <*  nbsc
  <*> blockOf parseEffectSet

parseEffectSet :: Parser EffectSet
parseEffectSet = do
  effects <- parseSomeSeparatedList '+' (parseMeta parseEffect)
  return EffectSet { setEffects = Set.fromList effects }

parseEffect :: Parser Effect
parseEffect = label "effect" $
  parseCapIdent "effect" (EffectNamed . unmeta) EffectPoly
  <|> (keyword "_" >> EffectAnon <$> getNewAnon)

parseUseModule :: Parser UseModule
parseUseModule =
  (UseModule <$> try (parseMeta parseName) <*> parseUseContents)
  <|> (UseAny <$ keyword "_")

parseUseContents :: Parser UseContents
parseUseContents =
  (reservedOp PathDot >> UseDot <$> parseMeta parseUseModule)
  <|> (UseAll <$> (parseParen <|> return []))
  where
    parseParen =
      try nbsc *> char '(' *> parenInner <* spaces <* char ')'
    parenInner =
      blockOf $ parseSomeCommaList $ parseMeta parseUseModule

parseSomeCommaList :: Parser a -> Parser [a]
parseSomeCommaList = parseSomeSeparatedList ','

parseSomeSeparatedList :: Char -> Parser a -> Parser [a]
parseSomeSeparatedList sep p =
  (:) <$> p <*> manyCommas
  where
    manyCommas = option [] $ do
      try (spaces >> char sep) >> spaces
      option [] ((:) <$> p <*> manyCommas)

data InfixOp = InfixOp
  { infixBacktick :: Bool
  , infixPath :: Meta Path }

infixOp :: Parser (Either (Span, SpecialOp) InfixOp)
infixOp = label "operator" (backtickOp <|> normalOp)
  where
    backtickOp =
      Right . InfixOp True <$> parseMeta (char '`' *> parsePath <* char '`')
    normalOp =
      getSpan nonReservedOp <&> \case
        (span, SpecialOp op) ->
          Left (span, op)
        (span, PlainOp op) ->
          Right $ InfixOp False $ metaWithSpan span $ Local $ Operator op

class (Show a, ExprLike a) => Parsable a where
  parseOne :: Parser a
  parseSpecial :: (Span, SpecialOp) -> Maybe (Prec -> Meta a -> Parser (Meta a))
  parseSpecial _ = Nothing

paren :: Parsable a => Parser (Meta a)
paren =
  parseMeta (char '(' *> (emptyParen <|> fullParen))
  where
    emptyParen = opUnit <$ char ')'
    fullParen = opParen <$> blockOf parser <* spaces <* char ')'

parserNoPrefix :: Parsable a => Parser (Meta a)
parserNoPrefix = parseMeta parseOne <|> hidden paren

-- parserNoPrefix :: Parsable a => Parser (Meta a)
-- parserNoPrefix = do
--   term <- parserNoEffects
--   case opEffectApply of
--     Nothing -> return term
--     Just eApply -> tryEffect eApply term <|> return term
--   where
--     tryEffect eApply term = do
--       start <- try $ nbsc >> parseMeta (reservedOp PipeSeparator)
--       effects <- nbsc *> parseEffectSet <* nbsc
--       end <- parseMeta $ reservedOp PipeSeparator
--       let newTerm = metaWithEnds term end $ eApply term (metaWithEnds start end effects)
--       tryEffect eApply newTerm <|> return newTerm

parserPartial :: Parsable a => Parser (Meta a)
parserPartial = hidden parsePrefix <|> parserNoPrefix
  where
    parsePrefix :: forall a. Parsable a => Parser (Meta a)
    parsePrefix = parseMeta $ do
      path <- try $ do
        path <- parseMeta (Local . Unary <$> unaryOp)
        spaceAfter <- isSpace <$> nbsc
        if spaceAfter then do
          addFail (metaSpan path) $
            "infix operator not allowed at start of " ++ opKind (Of :: Of a)
            ++ "\n(make sure prefix operators have no space after them)"
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
parser = parserPrec minPrec

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
          Left EndOfIndentedBlock ->
            fail $ show EndOfIndentedBlock
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
            Left EndOfIndentedBlock ->
              fail $ show EndOfIndentedBlock
            Left err ->
              return $ Just $ fail $ show err

        opAfterSpace offset parsedOp spaceAfter = do
          let
            isSpecial =
              case parsedOp of
                Right InfixOp { infixBacktick = True } -> True
                Left _ -> True
                _ -> False
          guard (spaceAfter || not spaceBefore || isSpecial)
          let
            opPrec =
              if spaceAfter || isSpecial then
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
                      return $ Just $ addFail (Just $ fst op)
                        ("special operator `" ++ show (snd op) ++ "` not allowed in " ++ opKind (Of :: Of a))
                    else
                      return Nothing
                  Just p ->
                    return $ Just $ p opPrec current
          else
            return Nothing

        app = do
          guard (prec < applyPrec)
          return $ Just $
            ((appEff <|> metaExtendFail opApply applyPrec current) >>= parserBase prec)
            <|> return current

        appEff =
          case opEffectApply of
            Nothing -> empty
            Just eApply -> do
              start <- try $ nbsc >> parseMeta (reservedOp PipeSeparator)
              effects <- nbsc *> parseEffectSet <* nbsc
              end <- parseMeta $ reservedOp PipeSeparator
              metaWithEnds current end <$> eitherToFail (eApply current $ metaWithEnds start end effects)

eitherToFail :: Either (Meta String) a -> Parser a
eitherToFail (Right x) = return x
eitherToFail (Left Meta { unmeta = msg, metaSpan }) = addFail metaSpan msg

metaExtendPrec :: Parsable b => (Meta a -> Meta b -> c) -> Prec -> Meta a -> Parser (Meta c)
metaExtendPrec f prec current =
  parserPrec prec <&> \next ->
    metaWithEnds current next $ f current next

metaExtendFail
  :: Parsable b
  => (Meta a -> Meta b -> Either (Meta String) c)
  -> Prec
  -> Meta a
  -> Parser (Meta c)
metaExtendFail f prec current = do
  next <- parserPrec prec
  metaWithEnds current next <$> eitherToFail (f current next)

instance Parsable Type where
  parseOne = label "type" $
    parseCapIdent "type" opNamed TPoly
    <|> (keyword "_" >> TAnon <$> getNewAnon)

  parseSpecial (span, FunctionArrow) =
    Just $ metaExtendPrec $ \lhs rhs ->
      let
        arrow = metaWithSpan span $ Core $ Operator "->"
        withNoEff = metaWithSpan span $ TNamed [] arrow
        firstApp = metaWithEnds lhs arrow $ TApp withNoEff lhs
      in
        TApp firstApp rhs
  parseSpecial (span, SplitArrow) =
    Just $ \prec lhs -> do
      effects <- parseMeta parseEffectSet
      nbsc
      (endSpan, _) <- getSpan $ plainOp "|>"
      nbsc
      parserPrec prec <&> \rhs ->
        let
          arrowSpan = span <> endSpan
          arrow = metaWithSpan arrowSpan $ Core $ Operator "->"
          withEff = metaWithSpan arrowSpan $ TNamed [effects] arrow
          firstApp = metaWithEnds lhs withEff $ TApp withEff lhs
        in
          metaWithEnds firstApp rhs $ TApp firstApp rhs

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
parseExprIndex = do
  (span, num) <- getSpan $ do
    reservedOp QuestionMark
    try L.decimal <|> return 0
  count <- countBindings
  if num < count then
    bindingAtIndex num >>= \case
      Nothing ->
        return $ EIndex num Nothing
      Just name ->
        addFail (Just span) ("binding declared by name `" ++ name ++ "` should also be referred to by name")
  else
    addFail (Just span) $
      case count of
        0 ->
          "found De Bruijn index, but no bindings are in scope"
        1 ->
          ("found De Bruijn index of " ++ show num ++ ", but only 1 binding is in scope")
        _ ->
          ("found De Bruijn index of " ++ show num ++ ", but only " ++ show count ++ " bindings are in scope")

parseFunction :: Parser Expr
parseFunction = do
  keyword "fun"
  EValue . VFun <$> blockOf matchCases

parseLet :: Parser Expr
parseLet = do
  keyword "let"
  pat <- blockOf parserExpectEnd
  nbsc >> specialOp Assignment
  val <- blockOf parser
  lineBreak
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
  <*  lineBreak
  <*> parser

matchCases :: Parser [MatchCase]
matchCases = someBetweenLines matchCase

matchCase :: Parser MatchCase
matchCase = do
  pats <- someUntil (specialOp FunctionArrow) parserNoSpace
  expr <- withBindings (pats >>= bindingsForPat) $ blockOf parser
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
    parseCapIdent "pattern" opNamed (PBind . Just)
    <|> (PAny <$ keyword "_")
    <|> (PBind Nothing <$ reservedOp QuestionMark)

  parseSpecial (_, TypeAscription) =
    Just $ metaExtendPrec PTypeAscribe
  parseSpecial _ = Nothing

parseCapIdent :: String
              -> (Meta Path -> a)
              -> (String -> a)
              -> Parser a
parseCapIdent kind named localBind = do
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
            addFail (metaSpan pathWithMeta)
              ("invalid path for " ++ kind ++ ", did you mean to capitalize it like `" ++ show alt ++ "`?")
        _ ->
          return $ named $ pathWithMeta

