-- | Functions for parsing a module from an entire file
module Parse.Module where

import Utility
import Parse.Primitives
import Parse.Expression

import Text.Megaparsec
import Text.Megaparsec.Char

import Data.Maybe

-- | Run 'parseFile' on a certain path and return the parsed module
parseSingleFile :: FilePath -> CompileIO Module
parseSingleFile path = do
  file <- liftIO $ readFile path
  let parserT = runCustomParser $ parseFile path
  runParserT parserT path file >>= \case
    Left err -> do
      convertParseErrors err
      return defaultModule
    Right m ->
      return m

-- | Parse a single 'Module' from file
parseFile :: FilePath -> Parser Module
parseFile file = do
  trySpaces >>= \case
    Right NoSpace ->
      return ()
    Right LineBreak ->
      return ()
    _ ->
      fail "expected unindented top-level items for module"
  moduleAddCoreImports . moduleAddLocalImports <$> parseModule defaultModule
  where
    parseModule m = do
      m <-
        parseUse
        <|> parseMod
        <|> parseLet
        <|> parseData
        <|> parseEffect
        <|> parseOperator
      option m (try lineBreak >> ((m <$ hidden eof) <|> parseModule m))
      where
        parseUse =
          keyword "use" *> nbsc *> withSpan parseUseModule <&> \use ->
            modAddUse file use m

        parseMod = do
          keyword "mod"
          name <- nbsc >> parseName
          nbsc >> specialOp Assignment
          sub <- blockOf $ parseModule defaultModule
          return $ modAddSub name (moduleAddLocalImports sub) m

        parseOperator = do
          keyword "operator"
          nbsc >> (keyword "type" >> blockOf operatorType) <|> operatorDecl
          where
            operatorType = do
              ops <- parseSomeSeparatedList '<' operatorPart
              return $ modAddOpType file ops m
            operatorPart =
              try (OpLink <$> withSpan (char '(' *> nbsc *> parsePath <* nbsc <* char ')'))
              <|> (OpDeclare <$> withSpan parseName)
            operatorDecl = do
              opAssoc <- option ANon (operatorAssoc <* nbsc)
              names <- someUntil (specialOp TypeAscription) $ withSpan parseName
              opType <- nbsc >> withSpan parsePath
              let decl = OpDecl { opAssoc, opType }
              modAddOpDecls file names decl m
            operatorAssoc =
              (ALeft <$ expectLabel "left")
              <|> (ARight <$ expectLabel "right")

        parseEffect = do
          keyword "effect"
          name <- nbsc >> withSpan parseName
          effectSuper <- option [] parseEffectSuper
          modAddEffect file name EffectDecl { effectSuper } m
          where
            parseEffectSuper = do
              try (nbsc >> specialOp TypeAscription)
              blockOf $ parseSomeCommaList parseSingleEffect
            parseSingleEffect = do
              effs :&: span <- withSpan parseEffectSet
              case esToList effs of
                [eff] ->
                  return eff
                _ -> do
                  file <- getFilePath
                  addError compileError
                    { errorFile = file
                    , errorSpan = span
                    , errorMessage =
                      "effects cannot inherit from a single set of multiple effects\n" ++
                      "(to inherit from multiple effects at once, separate them with commas)" }
                  withInfo span . EffectAnon <$> getNewAnon

        parseLet = do
          keyword "let"
          name <- nbsc *> withSpan parseName <* nbsc
          maybeAscription <- optional (specialOp TypeAscription *> blockOf parserExpectEnd <* nbsc)
          constraints <- option [] (parseConstraints <* nbsc)
          body <- specialOp Assignment >> blockOf parser
          case maybeAscription of
            Nothing ->
              case body of
                ETypeAscribe _ ty :&: _ | Nothing <- findBlank ty ->
                  addError compileError
                    { errorFile = file
                    , errorSpan = getSpan ty
                    , errorKind = Warning
                    , errorMessage =
                      "type ascription could be moved to top of let binding\n" ++
                      "(`let " ++ show name ++ " : " ++ show ty ++ "`)" }
                _ ->
                  return ()
            Just ty
              | Just blankSpan <- findBlank ty ->
                addError compileError
                  { errorFile = file
                  , errorSpan = blankSpan
                  , errorMessage = "top level type ascription cannot contain `_`" }
              | otherwise ->
                return ()
          let
            letDecl = LetDecl
              { letTypeAscription = maybeAscription
              , letConstraints = constraints
              , letBody = body }
          modAddLet file name letDecl m

        parseData = do
          keyword "data" >> nbsc
          isMod <-
            (keyword "mod" >> nbsc >> return True) <|> return False
          namedDataSig <-
            parserExpectEnd >>= namedDataSigFromType file
          nbsc >> specialOp Assignment
          vars <- blockOf $
            someBetweenLines (parserExpectEnd >>= variantFromType file)
          case namedDataSig of
            Nothing ->
              return m
            Just (name, dataSig) ->
              let
                dataDecl = DataDecl
                  { dataMod = isMod
                  , dataSig
                  , dataVariants = catMaybes vars }
              in
                modAddData file name dataDecl m

-- | Parse a set of constraints for a with-clause
parseConstraints :: Parser [MetaR Span Constraint]
parseConstraints = do
  keyword "with"
  catMaybes <$> (blockOf $ parseSomeCommaList parseConstraint)

-- | Tries to parse a single 'Constraint'
parseConstraint :: Parser (Maybe (MetaR Span Constraint))
parseConstraint = do
  (baseTy, maybeAscription) :&: span <- withSpan do
    baseTy <- parserExpectEnd
    maybeAscription <- optional do
      try (nbsc >> specialOp TypeAscription) >> nbsc
      blockOf $ withSpan parseEffectSet
    return (baseTy, maybeAscription)
  file <- getFilePath
  constraint <- disambiguateConstraint file baseTy maybeAscription
  return $ withInfo span <$> constraint

