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
parseFile path = do
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
          keyword "use" *> nbsc *> parseMeta parseUseModule <&> \use ->
            modAddUse use path m

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
              return $ modAddOpType ops path m
            operatorPart =
              try (OpLink <$> parseMeta (char '(' *> nbsc *> parsePath <* nbsc <* char ')'))
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
          effectSuper <- parseEffectSuper <|> pure []
          modAddEffect name EffectDecl { effectSuper } path m
          where
            parseEffectSuper = do
              try (nbsc >> specialOp TypeAscription)
              blockOf $ parseSomeCommaList $ parseMeta parsePath

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
              , letConstraints = constraints
              , letInferredType = ()
              , letInstanceArgs = [] }
          modAddLet name letDecl path m

        parseData = do
          keyword "data" >> nbsc
          isMod <- (keyword "mod" >> nbsc >> return True) <|> return False
          (name, dataSig) <-
            parserExpectEnd >>= namedDataSigFromType path
          nbsc >> specialOp Assignment
          vars <- blockOf $
            someBetweenLines (parserExpectEnd >>= variantFromType path)
          case name of
            Nothing ->
              return m
            Just name ->
              let
                dataDecl = DataDecl
                  { dataMod = isMod
                  , dataSig
                  , dataVariants = catMaybes vars }
              in
                modAddData name dataDecl path m

-- | Parse a set of constraints for a with-clause
parseConstraints :: Parser [Meta Constraint]
parseConstraints = do
  keyword "with"
  blockOf $ parseSomeCommaList (parseMeta parseConstraint)

-- | Parse a single 'Constraint'
parseConstraint :: Parser Constraint
parseConstraint =
  pure IsSubEffectOf
  <*> parseMeta parseEffect
  <*  nbsc
  <*  specialOp TypeAscription
  <*  nbsc
  <*> blockOf parseEffectSet

