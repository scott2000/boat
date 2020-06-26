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
  Path <$> ((:) <$> try parseName <*> many (hidden (reservedOp PathDot) *> parseName))

-- | Parse a single 'UseModule'
parseUseModule :: Parser UseModule
parseUseModule =
  (UseModule <$> try (parseMeta parseName) <*> parseUseContents)
  <|> (UseAny <$ keyword "_")

-- | Parse a single 'UseContents'
parseUseContents :: Parser UseContents
parseUseContents =
  (reservedOp PathDot >> UseDot <$> parseMeta parseUseModule)
  <|> (UseAll <$> (parseParen <|> return []))
  where
    parseParen =
      try nbsc *> char '(' *> blockOf parenInner <* spaces <* char ')'
    parenInner =
      parseSomeCommaList $ parseMeta parseUseModule

-- | Parse a set of effects separated by a plus symbol
parseEffectSet :: Parser EffectSet
parseEffectSet = do
  effects <- parseSomeSeparatedList '+' (parseMeta parseEffect)
  return EffectSet { setEffects = Set.fromList effects }

-- | Parse a single 'Effect'
parseEffect :: Parser Effect
parseEffect = label "effect" $
  parseCapIdent "effect" (EffectNamed . unmeta) EffectPoly
  <|> (keyword "_" >> EffectAnon <$> getNewAnon)

-- | Parse an identifier in one of two given ways depending on capitalization
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

-- | Represents a parsed infix operator (including those surrounded by backticks)
data InfixOp = InfixOp
  { infixBacktick :: Bool
  , infixPath :: Meta Path }

-- | Parse an infix operator, or fail with a special operator and its span
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
          Right $ InfixOp False $ metaWithSpan' span $ Local $ Operator op

-- | A class for an expression that can be parsed that uses operator precedence
class (Show a, ExprLike a) => Parsable a where
  -- | Parse a single basic expression
  parseOne :: Parser a
  -- | Try to parse a given special operator
  parseSpecial :: (Span, SpecialOp) -> Maybe (Prec -> Meta a -> Parser (Meta a))
  parseSpecial _ = Nothing

-- | Parse an expression inside of parentheses
paren :: Parsable a => Parser (Meta a)
paren =
  parseMeta (char '(' *> (emptyParen <|> fullParen))
  where
    emptyParen = opUnit <$ char ')'
    fullParen = opParen <$> blockOf parser <* spaces <* char ')'

-- | Parse a single expression, including ones with a prefix operator
parserPartial :: Parsable a => Parser (Meta a)
parserPartial =
  hidden parsePrefix
  <|> hidden parseEffectForall
  <|> parseMeta parseOne
  <|> hidden paren
  where
    parsePrefix :: forall a. Parsable a => Parser (Meta a)
    parsePrefix = parseMeta do
      path <- do
        path <- try $ parseMeta (Local . Unary <$> unaryOp)
        spaceAfter <- isSpace <$> nbsc
        if spaceAfter then
          addFail (metaSpan path) $
            "infix operator not allowed at start of " ++ opKind (Of :: Of a)
            ++ "\n(make sure prefix operators have no space after them)"
        else
          return path
      opUnary path <$> parserPrec CompactPrec

    parseEffectForall =
      case opForallEffect of
        Nothing -> empty
        Just forEff -> parseMeta do
          reservedOp PipeSeparator
          name <- nbsc >> parseMeta identifier
          nbsc >> reservedOp PipeSeparator
          when (isCap $ head $ unmeta name) do
            file <- getFilePath
            addError compileError
              { errorFile = Just file
              , errorSpan = metaSpan name
              , errorMessage = "effect variable name must start with a lowercase letter" }
          nbsc >> forEff name <$> parserPrec NormalPrec

-- | Represents the precedence of a type of operation
data Prec
  -- | A special precedence for when an expression will be terminated by a special operator
  = ExpectEndPrec
  -- | The default precedence for an expression
  | MinPrec
  -- | The precedence for a regular operator surrounded by whitespace
  | SpecialPrec
  -- | The precedence for a regular operator surrounded by whitespace
  | NormalPrec
  -- | The precedence for function application
  | ApplyPrec
  -- | The precedence for a compact operator not surrounded by whitespace
  | CompactPrec
  deriving (Ord, Eq)

-- | Parse a single expression
parser :: Parsable a => Parser (Meta a)
parser = parserPrec MinPrec

-- | Parse a single expression, but expect to be terminated by a special operator
parserExpectEnd :: Parsable a => Parser (Meta a)
parserExpectEnd = parserPrec ExpectEndPrec

-- | Parse a single expression, but require parentheses for spaces to be used
parserNoSpace :: Parsable a => Parser (Meta a)
parserNoSpace = parserPrec ApplyPrec

-- | Parse a single expression at a certain precedence level (the most general way to parse something)
parserPrec :: Parsable a => Prec -> Parser (Meta a)
parserPrec prec = parserPartial >>= parserBase prec

-- | Continue parsing after an expression with a given precedence level
parserBase :: forall a. Parsable a => Prec -> Meta a -> Parser (Meta a)
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
                  return $ Just $ addFail (Just $ fst op)
                    ("special operator `" ++ show (snd op) ++ "` not allowed in " ++ opKind (Of :: Of a))
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
                parserBase prec $ copySpan bin $ opParen bin
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
              start <- try $ nbsc >> parseMeta (reservedOp PipeSeparator)
              effects <- nbsc *> parseEffectSet <* nbsc
              end <- parseMeta $ reservedOp PipeSeparator
              metaWithEnds current end <$> eitherToFail (eApply current $ metaWithEnds start end effects)

-- | Convert a result using 'Either' to fail parsing instead
eitherToFail :: Either (Meta String) a -> Parser a
eitherToFail (Right x) = return x
eitherToFail (Left Meta { unmeta = msg, metaSpan }) = addFail metaSpan msg

-- | Extend an already-parsed expression by parsing another expression at a precedence and calling a function
metaExtendPrec :: Parsable b => (Meta a -> Meta b -> c) -> Prec -> Meta a -> Parser (Meta c)
metaExtendPrec f prec current =
  parserPrec prec <&> \next ->
    metaWithEnds current next $ f current next

-- | Like 'metaExtendPrec', but with the function called to get the result may fail
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
    Just $ metaExtendPrec \lhs rhs ->
      let
        arrow = metaWithSpan' span $ Core $ Operator "->"
        withNoEff = metaWithSpan' span $ TNamed [] arrow
        firstApp = metaWithEnds lhs arrow $ TApp withNoEff lhs
      in
        TApp firstApp rhs
  parseSpecial (span, SplitArrow) =
    Just \prec lhs -> do
      effects <- parseMeta parseEffectSet
      nbsc
      (endSpan, _) <- getSpan $ plainOp "|>"
      nbsc
      parserPrec prec <&> \rhs ->
        let
          arrowSpan = span <> endSpan
          arrow = metaWithSpan' arrowSpan $ Core $ Operator "->"
          withEff = metaWithSpan' arrowSpan $ TNamed [effects] arrow
          firstApp = metaWithEnds lhs withEff $ TApp withEff lhs
        in
          metaWithEnds firstApp rhs $ TApp firstApp rhs

  parseSpecial _ = Nothing

instance Parsable Expr where
  parseOne = label "expression" $
    -- Identifiers must come first to avoid matching keyword prefix
    parseExprIdent
    <|> parseExprIndex
    <|> parseLet
    <|> parseFunction
    <|> parseMatch
    <|> parseExprUse

  parseSpecial (_, TypeAscription) =
    Just $ metaExtendPrec ETypeAscribe
  parseSpecial _ = Nothing

-- | Parse an identifier for an expression using the current local variable bindings in scope
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

-- | Parse a DeBruijn expression index to refer to an unnamed local variable
parseExprIndex :: Parser Expr
parseExprIndex = do
  (span, num) <- getSpan do
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

-- | Parse a function expression
parseFunction :: Parser Expr
parseFunction = do
  keyword "fun"
  EValue . VFun <$> blockOf matchCases

-- | Parse a let expression
parseLet :: Parser Expr
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
parseMatch :: Parser Expr
parseMatch =
  pure EMatchIn
  <*  keyword "match"
  <*> blockOf (some (try nbsc >> parserNoSpace))
  <*> blockOf matchCases

-- | Parse a use expression
parseExprUse :: Parser Expr
parseExprUse =
  pure EUse
  <*  keyword "use"
  <*  nbsc
  <*> parseMeta parseUseModule
  <*  lineBreak
  <*> parser

-- | Parse a set of pattern match cases
matchCases :: Parser [MatchCase]
matchCases = someBetweenLines matchCase

-- | Parse a single 'MatchCase'
matchCase :: Parser MatchCase
matchCase = do
  pats <- someUntil (specialOp FunctionArrow) parserNoSpace
  file <- getFilePath
  assertUniqueBindings file pats
  expr <- withBindings (pats >>= bindingsForPat) $ blockOf parser
  return (pats, expr)

instance Parsable Pattern where
  parseOne = label "pattern" $
    parseCapIdent "pattern" opNamed (PBind . Just)
    <|> (PAny <$ keyword "_")
    <|> (PBind Nothing <$ reservedOp QuestionMark)

  parseSpecial (_, TypeAscription) =
    Just $ metaExtendPrec PTypeAscribe
  parseSpecial _ = Nothing

