-- | Parser functions for various types of expressions involving precedence
module Parse.Expression where

import Utility
import Parse.Primitives

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import qualified Data.Set as Set
import Control.Monad.State.Strict

-- | Parse a single 'Name'
parseName :: Parser Name
parseName =
  parseParen <|> Identifier <$> identifier
  where
    parseParen = label "parenthesized operator" $
      char '(' *> nbsc *> (parseUnary <|> Operator <$> plainOrArrowOp) <* nbsc <* char ')'
    parseUnary = label "keyword \"unary\"" $
      keyword "unary" >> nbsc >> Unary <$> unaryOp

-- | Parse a single 'Path'
parsePath :: Parser Path
parsePath =
  toPath <$> ((:) <$> try parseName <*> many (hidden (reservedOp PathDot) *> parseName))

-- | Parse a single 'UseModule'
parseUseModule :: Parser UseModule
parseUseModule =
  (UseModule <$> try (withSpan parseName) <*> parseUseContents)
  <|> (UseAny <$ keyword "_")

-- | Parse a single 'UseContents'
parseUseContents :: Parser UseContents
parseUseContents =
  (reservedOp PathDot >> UseDot <$> withSpan parseUseModule)
  <|> (UseAll <$> (parseParen <|> return []))
  where
    parseParen =
      try nbsc *> char '(' *> blockOf parenInner <* spaces <* char ')'
    parenInner =
      parseSomeCommaList $ withSpan parseUseModule

-- | Parse a set of effects separated by a plus symbol
parseEffectSet :: Parser (EffectSet Span)
parseEffectSet = do
  effects <- parseSomeSeparatedList '+' (withSpan parseEffect)
  setEffects <- toUniqueSet Set.empty effects
  return EffectSet { setEffects }
  where
    toUniqueSet set [] = return set
    toUniqueSet set (e:es)
      | e `Set.member` set = do
        file <- getFilePath
        addError compileError
          { errorFile = file
          , errorSpan = getSpan e
          , errorKind = Warning
          , errorMessage = "effect is unnecessary since it was already listed" }
        toUniqueSet set es
      | otherwise =
        toUniqueSet (Set.insert e set) es

-- | Parse a single 'Effect'
parseEffect :: Parser Effect
parseEffect = label "effect" $
  parseCapIdent "effect" (EffectNamed . unmeta) EffectPoly
  <|> (keyword "_" >> EffectAnon <$> getNewAnon)

-- | Parse an identifier in one of two given ways depending on capitalization
parseCapIdent :: String
              -> (Meta Span Path -> a)
              -> (String -> a)
              -> Parser a
parseCapIdent kind named localBind = do
  pathWithMeta <- withSpan parsePath
  let path = unmeta pathWithMeta
  case extractLocalPath path of
    Just name ->
      return $ localBind $ name
    Nothing ->
      let components = unpath path in
      case last components of
        Identifier name
          | isLocalIdentifier name ->
            let alt = toPath $ init components ++ [Identifier $ capFirst name] in
            addFail (getSpan pathWithMeta)
              ("invalid path for " ++ kind ++ ", did you mean to capitalize it like `" ++ show alt ++ "`?")
        _ ->
          return $ named $ pathWithMeta

-- | Represents a parsed infix operator (including those surrounded by backticks)
data InfixOp = InfixOp
  { infixBacktick :: Bool
  , infixPath :: Meta Span Path }

-- | Parse an infix operator, or fail with a special operator and its span
infixOp :: Parser (Either (Meta Span SpecialOp) InfixOp)
infixOp = label "operator" (backtickOp <|> normalOp)
  where
    backtickOp =
      Right . InfixOp True <$> withSpan (char '`' *> parsePath <* char '`')
    normalOp =
      withSpan nonReservedOp <&> \case
        SpecialOp op :&: span ->
          Left $ op :&: span
        PlainOp op :&: span ->
          Right $ InfixOp False $ withInfo span $ Local $ Operator op

-- | A class for an expression that can be parsed that uses operator precedence
class ExprLike a => Parsable a where
  -- | Parse a single basic expression
  parseOne :: Parser a
  -- | Try to parse a given special operator
  parseSpecial :: Meta Span SpecialOp -> Maybe (Prec -> Meta Span a -> Parser (Meta Span a))
  parseSpecial _ = Nothing

-- | Parse an expression inside of parentheses
paren :: Parsable a => Parser (Meta Span a)
paren =
  withSpan (char '(' *> (emptyParen <|> fullParen))
  where
    emptyParen = opUnit <$ char ')'
    fullParen = opParen <$> blockOf parser <* spaces <* char ')'

-- | Parse a single expression, including ones with a prefix operator
parserPartial :: Parsable a => Parser (Meta Span a)
parserPartial =
  hidden parsePrefix
  <|> hidden parseEffectForall
  <|> withSpan parseOne
  <|> hidden paren
  where
    parsePrefix :: forall a. Parsable a => Parser (Meta Span a)
    parsePrefix = withSpan do
      path <- do
        path <- try $ withSpan (Local . Unary <$> unaryOp)
        spaceAfter <- isSpace <$> nbsc
        if spaceAfter then
          addFail (getSpan path) $
            "infix operator not allowed at start of " ++ opKind (Of :: Of a)
            ++ "\n(make sure prefix operators have no space after them)"
        else
          return path
      opUnary path <$> parserPrec CompactPrec

    parseEffectForall =
      case opForallEffect of
        Nothing -> empty
        Just forEff -> withSpan do
          reservedOp PipeSeparator
          name <- nbsc >> withSpan identifier
          nbsc >> reservedOp PipeSeparator
          when (isCap $ head $ unmeta name) do
            file <- getFilePath
            addError compileError
              { errorFile = file
              , errorSpan = getSpan name
              , errorMessage = "effect variable name must start with a lowercase letter" }
          nbsc >> forEff name <$> parserPrec NormalPrec

-- | Parse a single expression
parser :: Parsable a => Parser (Meta Span a)
parser = parserPrec MinPrec

-- | Parse a single expression, but expect to be terminated by a special operator
parserExpectEnd :: Parsable a => Parser (Meta Span a)
parserExpectEnd = parserPrec ExpectEndPrec

-- | Parse a single expression, but require parentheses for spaces to be used
parserNoSpace :: Parsable a => Parser (Meta Span a)
parserNoSpace = parserPrec ApplyPrec

-- | Parse a single expression at a certain precedence level (the most general way to parse something)
parserPrec :: Parsable a => Prec -> Parser (Meta Span a)
parserPrec prec = parserPartial >>= parserBase prec

-- | Continue parsing after an expression with a given precedence level
parserBase :: forall a. Parsable a => Prec -> Meta Span a -> Parser (Meta Span a)
parserBase prec current =
  join (seqOpApp <|> return (return current))
  where
    seqOpApp =
      try do
        offset <- getOffset
        trySpaces >>= \case
          Right NoSpace -> opOrApp False
          Right Whitespace -> opOrApp True
          Right LineBreak ->
            if prec == MinPrec then
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
            spaceErrorFail offset err

    opOrApp spaceBefore =
      op <|> app >>= \case
        Just x ->
          return x
        Nothing ->
          empty
      where
        op = try do
          offset <- getOffset
          infixOp >>= \case
            Left special ->
              opParseSpecial offset special
            Right normal ->
              parseSpaceAfterOperator offset $ opAfterSpace normal

        parseSpaceAfterOperator offset f = do
          offsetAfterOp <- getOffset
          trySpaces >>= \case
            Right NoSpace ->
              f False
            Right Whitespace ->
              f True
            Right LineBreak ->
              return $ Just do
                setOffset offsetAfterOp
                fail "line break never allowed after operator"
            Left err ->
              spaceErrorFail offset err

        opParseSpecial offset op =
          if prec <= SpecialPrec then
            case parseSpecial op of
              Nothing ->
                if prec == MinPrec then
                  return $ Just $ addFail (getSpan op)
                    ("special operator `" ++ show (unmeta op) ++ "` not allowed in " ++ opKind (Of :: Of a))
                else
                  return Nothing
              Just p ->
                parseSpaceAfterOperator offset \_ ->
                  return $ Just $ p SpecialPrec current
          else
            return Nothing

        opAfterSpace parsedOp spaceAfter = do
          let isBacktick = infixBacktick parsedOp
          guard (spaceAfter || not spaceBefore || isBacktick)
          let
            opPrec =
              if spaceAfter || isBacktick then
                NormalPrec
              else
                CompactPrec
          if prec <= opPrec then
            return $ Just do
              bin <- metaExtendPrec (opBinary $ infixPath parsedOp) opPrec current
              if prec == opPrec then
                return bin
              else
                parserBase prec $ copyInfo bin $ opParen bin
          else
            return Nothing

        app = do
          guard (prec < ApplyPrec)
          return $ Just $
            ((appEff <|> metaExtendFail opApply ApplyPrec current) >>= parserBase prec)
            <|> return current

        appEff =
          case opEffectApply of
            Nothing -> empty
            Just eApply -> do
              start <- try $ nbsc >> withSpan (reservedOp PipeSeparator)
              effects <- nbsc *> parseEffectSet <* nbsc
              end <- withSpan $ reservedOp PipeSeparator
              withEnds current end <$> eitherToFail (eApply current $ withEnds start end effects)

-- | Convert a result using 'Either' to fail parsing instead
eitherToFail :: Either (Meta Span String) a -> Parser a
eitherToFail (Right x) = return x
eitherToFail (Left (msg :&: span)) = addFail span msg

-- | Extend an already-parsed expression by parsing another expression at a precedence and calling a function
metaExtendPrec :: Parsable b => (Meta Span a -> Meta Span b -> c) -> Prec -> Meta Span a -> Parser (Meta Span c)
metaExtendPrec f prec current =
  parserPrec prec <&> \next ->
    withEnds current next $ f current next

-- | Like 'metaExtendPrec', but with the function called to get the result may fail
metaExtendFail
  :: Parsable b
  => (Meta Span a -> Meta Span b -> Either (Meta Span String) c)
  -> Prec
  -> Meta Span a
  -> Parser (Meta Span c)
metaExtendFail f prec current = do
  next <- parserPrec prec
  withEnds current next <$> eitherToFail (f current next)

instance Parsable (Type Span) where
  parseOne = label "type" $
    parseCapIdent "type" opNamed TPoly
    <|> (keyword "_" >> TAnon <$> getNewAnon)

  parseSpecial (FunctionArrow :&: span) =
    Just $ metaExtendPrec \lhs rhs ->
      let
        arrow = withInfo span TFuncArrow
        firstApp = withEnds lhs arrow $ TApp arrow lhs
      in
        TApp firstApp rhs
  parseSpecial (SplitArrow :&: span) =
    Just \prec lhs -> do
      effects <- withSpan parseEffectSet
      nbsc
      endSpan <- getSpan <$> withSpan (plainOp "|>")
      nbsc
      parserPrec prec <&> \rhs ->
        let
          arrowSpan = span <> endSpan
          arrow = withInfo arrowSpan TFuncArrow
          withEff = withInfo arrowSpan $ TEffApp arrow effects
          firstApp = withEnds lhs withEff $ TApp withEff lhs
        in
          withEnds firstApp rhs $ TApp firstApp rhs

  parseSpecial _ = Nothing

instance Parsable (Expr Span) where
  parseOne = label "expression" $
    -- Identifiers must come first to avoid matching keyword prefix
    parseExprIdent
    <|> parseExprIndex
    <|> parseLet
    <|> parseFunction
    <|> parseMatch
    <|> parseExprUse

  parseSpecial (TypeAscription :&: _) =
    Just $ metaExtendPrec ETypeAscribe
  parseSpecial _ = Nothing

-- | Parse an identifier for an expression using the current local variable bindings in scope
parseExprIdent :: Parser (Expr Span)
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

-- | Parse a DeBruijn expression index to refer to an unnamed local variable
parseExprIndex :: Parser (Expr Span)
parseExprIndex = do
  (num :&: span) <- withSpan do
    reservedOp QuestionMark
    try L.decimal <|> return 0
  count <- countBindings
  if num < count then
    bindingAtIndex num >>= \case
      Nothing ->
        return $ EIndex num Nothing
      Just name ->
        addFail span ("binding declared by name `" ++ name ++ "` should also be referred to by name")
  else
    addFail span $
      case count of
        0 ->
          "found De Bruijn index, but no bindings are in scope"
        1 ->
          ("found De Bruijn index of " ++ show num ++ ", but only 1 binding is in scope")
        _ ->
          ("found De Bruijn index of " ++ show num ++ ", but only " ++ show count ++ " bindings are in scope")

-- | Parse a function expression
parseFunction :: Parser (Expr Span)
parseFunction = do
  keyword "fun"
  EValue . VFun <$> blockOf matchCases

-- | Parse a let expression
parseLet :: Parser (Expr Span)
parseLet = do
  keyword "let"
  pat <- blockOf parserExpectEnd
  file <- getFilePath
  assertUniqueBindings file [pat]
  nbsc >> specialOp Assignment
  val <- blockOf parser
  lineBreak
  expr <- withBindings (bindingsForPat pat) parser
  return $ ELet pat val expr

-- | Parse a match expression
parseMatch :: Parser (Expr Span)
parseMatch =
  pure EMatchIn
  <*  keyword "match"
  <*> blockOf (some (try nbsc >> parserNoSpace))
  <*> blockOf matchCases

-- | Parse a use expression
parseExprUse :: Parser (Expr Span)
parseExprUse =
  pure EUse
  <*  keyword "use"
  <*  nbsc
  <*> withSpan parseUseModule
  <*  lineBreak
  <*> parser

-- | Parse a set of pattern match cases
matchCases :: Parser [MatchCase Span]
matchCases = someBetweenLines matchCase

-- | Parse a single 'MatchCase'
matchCase :: Parser (MatchCase Span)
matchCase = do
  pats <- someUntil (specialOp FunctionArrow) parserNoSpace
  file <- getFilePath
  assertUniqueBindings file pats
  expr <- withBindings (pats >>= bindingsForPat) $ blockOf parser
  return (pats, expr)

instance Parsable (Pattern Span) where
  parseOne = label "pattern" $
    parseCapIdent "pattern" opNamed (PBind . Just)
    <|> (PAny <$ keyword "_")
    <|> (PBind Nothing <$ reservedOp QuestionMark)

  parseSpecial (TypeAscription :&: _) =
    Just $ metaExtendPrec PTypeAscribe
  parseSpecial _ = Nothing

