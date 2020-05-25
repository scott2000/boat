-- | Utilities for dealing with top-level declarations and full packages
module Utility.Program
  ( -- * Top-Level Declarations
    InFile (..)
  , ShowWithName (..)
  , Associativity (..)
  , OpDecl (..)
  , EffectDecl (..)
  , LetDecl
  , LetDeclWith (..)

    -- * Data Types
  , DataDecl (..)
  , DataVariant
  , variantFromType
  , DataSig (..)
  , namedDataSigFromType
  , pattern UnnamedArg
  , TypeVariance (..)
  , DataArg (..)
  , pattern NullaryArg

    -- * Operator Types
  , OpType
  , OpPart (..)
  , opTypeDeclarations
  , OpTypeEnds

    -- * Fully Resolved Representation
  , AllDecls
  , AllDeclsWith (..)
  , emptyDecls

    -- * Nested Module Representation
  , Module (..)
  , defaultModule
  , moduleFromSubs
  , modIsEmpty

    -- * Adding Declarations to the Module
  , modAddUse
  , modAddSub
  , modAddOpType
  , modAddOpDecls
  , modAddEffect
  , modAddLet
  , modAddData
  ) where

import Utility.Basics
import Utility.AST

import Data.List
import Data.Maybe
import Data.Char

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified Data.Set as Set

import Control.Monad.State.Strict

-- | Associates a file path with a declaration
data InFile a = (:/:)
  { -- | The file where the declaration can be found
    getFile :: FilePath
    -- | The innner declaration being stored
  , unfile :: a }
  deriving (Functor, Foldable, Traversable)

instance Ord a => Ord (InFile a) where
  (_ :/: a) `compare` (_ :/: b) =
    a `compare` b

instance Eq a => Eq (InFile a) where
  (_ :/: a) == (_ :/: b) = a == b

instance Show a => Show (InFile a) where
  showsPrec i = showsPrec i . unfile

-- | Class for showing a value with an externally provided name
class ShowWithName a where
  -- | Show the declaration using the provided name
  showWithName :: String -> a -> String

instance ShowWithName a => ShowWithName (Meta a) where
  showWithName name = showWithName name . unmeta

instance ShowWithName a => ShowWithName (InFile a) where
  showWithName name = showWithName name . unfile

-- | Shows a key-value pair where the key is the name
showDecl :: (ShowWithName a, Show s) => (s, a) -> String
showDecl (name, decl) = showWithName (show name) decl

-- | Shows every item in a map where the key is the name
showDeclMap :: (ShowWithName a, Show s) => Map s a -> [String]
showDeclMap = map showDecl . Map.toList

-- | Represents the upper and lower bound for the precedence of an operator type
type OpTypeEnds = (Maybe (Meta Path), Maybe (Meta Path))

-- | A collection of all declarations in a package by absolute path
type AllDecls = AllDeclsWith ()

-- | A collection of all declarations in a package by absolute path (with some type information)
data AllDeclsWith ty = AllDecls
  { allOpTypes :: !(Map (Meta Path) (InFile OpTypeEnds))
  , allOpDecls :: !(Map (Meta Path) (InFile OpDecl))
  , allEffects :: !(Map (Meta Path) (InFile EffectDecl))
  , allDatas :: !(Map (Meta Path) (InFile DataDecl))
  , allLets :: !(Map (Meta Path) (InFile (LetDeclWith ty))) }

instance Show AllDecls where
  show AllDecls { allOpTypes, allOpDecls, allEffects, allDatas, allLets } =
    intercalate "\n" $ concat
      [ map showOpType $ Map.toList allOpTypes
      , showDeclMap allOpDecls
      , showDeclMap allEffects
      , showDeclMap allDatas
      , showDeclMap allLets ]
    where
      showOpType (path, _ :/: (left, right)) =
        "operator type " ++ leftStr ++ show path ++ rightStr
        where
          leftStr =
            case left of
              Nothing -> ""
              Just lowerBound -> "(" ++ show lowerBound ++ ") < "
          rightStr =
            case right of
              Nothing -> ""
              Just upperBound -> " < (" ++ show upperBound ++ ")"

-- | An empty collection of declarations
emptyDecls :: AllDecls
emptyDecls = AllDecls
  { allOpTypes = Map.empty
  , allOpDecls = Map.empty
  , allEffects = Map.empty
  , allDatas = Map.empty
  , allLets = Map.empty }

-- | A direct representation of a parsed module that hasn't been flattened yet
data Module = Module
  { modUses :: ![InFile (Meta UseModule)]
  , modSubs :: !(Map Name [Module])
  , modOpTypes :: ![InFile OpType]
  , modOpDecls :: !(Map (Meta Name) (InFile OpDecl))
  , modEffects :: !(Map (Meta Name) (InFile EffectDecl))
  , modDatas :: !(Map (Meta Name) (InFile DataDecl))
  , modLets :: !(Map (Meta Name) (InFile LetDecl)) }

instance Show Module where
  show Module { modUses, modSubs, modOpTypes, modOpDecls, modEffects, modDatas, modLets } =
    intercalate "\n" $ concat
      [ map showUse $ reverse modUses
      , map showMod $ Map.toList modSubs
      , map showOpType $ reverse modOpTypes
      , showDeclMap modOpDecls
      , showDeclMap modEffects
      , showDeclMap modDatas
      , showDeclMap modLets ]
    where
      showUse use =
        "use " ++ show use
      showMod (name, mods) =
        intercalate "\n" $ mods <&> \mod ->
          "mod " ++ show name ++ " =" ++ indent (show mod)
      showOpType (_ :/: ops) =
        "operator type " ++ intercalate " < " (map show ops)

-- | An empty module with no declarations
defaultModule :: Module
defaultModule = Module
  { modUses = []
  , modSubs = Map.empty
  , modOpTypes = []
  , modOpDecls = Map.empty
  , modEffects = Map.empty
  , modDatas = Map.empty
  , modLets = Map.empty }

-- | Creates a module from a name and a set of sub-modules to associate with that name
moduleFromSubs :: Name -> [Module] -> Module
moduleFromSubs _ [] = defaultModule
moduleFromSubs name mods = defaultModule
  { modSubs = Map.singleton name mods }

-- | Checks if a given module is empty
modIsEmpty :: Module -> Bool
modIsEmpty m =
  null (modUses m)
  && Map.null (modSubs m)
  && null (modOpTypes m)
  && Map.null (modOpDecls m)
  && Map.null (modDatas m)
  && Map.null (modLets m)

-- | Adds a 'UseModule' to the module
modAddUse :: Meta UseModule -> FilePath -> Module -> Module
modAddUse use path mod = mod
  { modUses = path :/: use : modUses mod }

-- | Adds a sub-module to the module
modAddSub :: Name -> Module -> Module -> Module
modAddSub name sub mod =
  if modIsEmpty sub then mod else mod
    { modSubs = Map.insertWith (flip (++)) name [sub] $ modSubs mod }

-- | A list of parts of an operator type declaration
type OpType = [OpPart]

-- | A single term in an operator type declaration
data OpPart
  -- | A declaration of a new operator type
  = OpDeclare (Meta Name)
  -- | A reference to an already declared operator type in parentheses
  | OpLink (Meta Path)

instance Show OpPart where
  show = \case
    OpDeclare name ->
      show name
    OpLink path ->
      "(" ++ show path ++ ")"

-- | Adds an 'OpType' declaration to the module
modAddOpType :: OpType -> FilePath -> Module -> Module
modAddOpType ops path mod = mod
  { modOpTypes = path :/: ops : modOpTypes mod }

-- | Get a list of all of the newly-declared operator types in an 'OpType'
opTypeDeclarations :: OpType -> [Name]
opTypeDeclarations ops = do
  op <- ops
  case op of
    OpDeclare name ->
      return $ unmeta name
    OpLink _ ->
      mempty

-- | Represents the associativity of an operation
data Associativity
  -- | Require explicit grouping whenever multiple operators are used
  = ANon
  -- | Group @(a ? b ? c)@ as @((a ? b) ? c)@
  | ALeft
  -- | Group @(a ? b ? c)@ as @(a ? (b ? c))@
  | ARight

instance Show Associativity where
  show = \case
    ANon   -> "non"
    ALeft  -> "left"
    ARight -> "right"

-- | A declaration of a certain associativity and operator type for an operator
data OpDecl = OpDecl
  { opAssoc :: Associativity
  , opType :: Meta Path }

instance ShowWithName OpDecl where
  showWithName name op =
    "operator" ++ assoc ++ " " ++ name ++ " : " ++ show (opType op)
    where
      assoc =
        case opAssoc op of
          ANon -> ""
          ALeft -> " <left>"
          ARight -> " <right>"

-- | Adds an 'OpDecl' for a list of operators to the module
modAddOpDecls
  :: AddError m
  => [Meta Name]
  -> OpDecl
  -> FilePath
  -> Module
  -> m Module
modAddOpDecls names op path mod = do
  let
    oldOps = modOpDecls mod
    opDecl = path :/: op
    newOps = names <&> \name -> (name, opDecl)
  forM_ names \name ->
    when (Map.member name oldOps) $
      addError CompileError
        { errorFile = Just path
        , errorSpan = metaSpan name
        , errorKind = Error
        , errorMessage = "duplicate operator declaration for name `" ++ show name ++ "`" }
  return mod { modOpDecls = Map.union (Map.fromList newOps) oldOps }

-- | A declaration of a new effect with an optional super-effect
data EffectDecl = EffectDecl
  { effectSuper :: Maybe (Meta Path) }

instance ShowWithName EffectDecl where
  showWithName name EffectDecl { effectSuper } =
    "effect " ++ name ++
      case effectSuper of
        Nothing -> ""
        Just effect ->
          " : " ++ show effect

-- | Adds an 'EffectDecl' to the module
modAddEffect
  :: AddError m
  => Meta Name
  -> EffectDecl
  -> FilePath
  -> Module
  -> m Module
modAddEffect name decl path mod = do
  let
    oldEffects = modEffects mod
    newDecl = path :/: decl
  when (unmeta name == Identifier "Pure") $
    addError CompileError
      { errorFile = Just path
      , errorSpan = metaSpan name
      , errorKind = Error
      , errorMessage = "effect name cannot be `Pure` because this is a special item" }
  when (Map.member name oldEffects) $
    addError CompileError
      { errorFile = Just path
      , errorSpan = metaSpan name
      , errorKind = Error
      , errorMessage = "duplicate effect declaration for name `" ++ show name ++ "`" }
  return mod { modEffects = Map.insert name newDecl oldEffects }

-- | A declaration for a top-level binding of an expression
type LetDecl = LetDeclWith ()

-- | A declaration for a top-level binding of an expression (with some type information)
data LetDeclWith ty = LetDecl
  { letBody :: MetaR ExprWith ty
  , letConstraints :: [Constraint] }

instance ShowWithName LetDecl where
  showWithName name decl =
    "let " ++ name ++ typeClause ++ withClause ++ " =" ++ indent (show body)
    where
      (body, typeClause) =
        case letBody decl of
          Meta { unmeta = ETypeAscribe expr ty } ->
            (expr, " : " ++ show ty)
          other ->
            (other, "")

      withClause =
        case letConstraints decl of
          [] -> ""
          cs -> " with " ++ intercalate ", " (map show cs)

-- | Adds a @LetDecl@ to the module
modAddLet
  :: AddError m
  => Meta Name
  -> LetDecl
  -> FilePath
  -> Module
  -> m Module
modAddLet name decl path mod = do
  let
    oldLets = modLets mod
    newDecl = path :/: decl
  when (Map.member name oldLets) $
    addError CompileError
      { errorFile = Just path
      , errorSpan = metaSpan name
      , errorKind = Error
      , errorMessage = "duplicate let binding for name `" ++ show name ++ "`" }
  return mod { modLets = Map.insert name newDecl oldLets }

-- | Represents the variance of a type or effect parameter
data TypeVariance
  -- | An uninferred variance for a parameter
  = VAnon AnonCount
  -- | Covariance, represented as @(+)@ for high-order parameters
  | VOutput
  -- | Contravariance, represented as @(-)@ for high-order parameters
  | VInput
  -- | Invariance, represented as @_@ for high-order parameters
  | VInvariant
  deriving Eq

instance Show TypeVariance where
  show = \case
    VAnon _ -> "(?)"
    VOutput -> show SymbolOutput
    VInput -> show SymbolInput
    VInvariant -> "_"

instance Semigroup TypeVariance where
  VOutput <> x = x
  VInvariant <> _ = VInvariant
  x <> VOutput = x
  _ <> VInvariant = VInvariant
  VInput <> VInput = VOutput

-- | The symbol used to represent 'VOutput'
pattern SymbolOutput :: Path
pattern SymbolOutput = Local (Operator "+")

-- | The symbol used to represent 'VInput'
pattern SymbolInput :: Path
pattern SymbolInput = Local (Operator "-")

-- | Represents the kind of a parameter for a 'DataDecl'
data DataArg = DataArg
  { argVariance :: !TypeVariance
  , argParams :: [DataArg] }
  deriving Eq

instance Show DataArg where
  show arg =
    showWithName (show $ argVariance arg) arg

instance ShowWithName DataArg where
  showWithName name DataArg { argParams }
    | null argParams = name
    | otherwise = "(" ++ unwords (name : map show argParams) ++ ")"

-- | Makes a 'DataArg' that accepts no additional parameters
pattern NullaryArg :: TypeVariance -> DataArg
pattern NullaryArg variance = DataArg variance []

-- | Used in place of a name for arguments that weren't named
pattern UnnamedArg :: Meta String
pattern UnnamedArg = DefaultMeta "_"

-- | Represents the effect and type parameters a 'DataDecl' can accept
data DataSig = DataSig
  { dataEffects :: [(Meta String, TypeVariance)]
  , dataArgs :: [(Meta String, DataArg)] }

instance ShowWithName DataSig where
  showWithName name DataSig { dataArgs, dataEffects } =
    name ++ effectSuffixStr (map (unmeta . fst) dataEffects) ++ unwords ("" : map showArg dataArgs)
    where
      showArg (name, dataArg) = showWithName (unmeta name) dataArg

-- | A single variant of a 'DataDecl'
type DataVariant = (Meta Name, [Meta Type])

-- | Represents a declaration of a new data type
data DataDecl = DataDecl
  { dataMod :: Bool
  , dataSig :: !DataSig
  , dataVariants :: [Meta DataVariant] }

instance ShowWithName DataDecl where
  showWithName name DataDecl { dataMod, dataSig, dataVariants } =
    "data " ++ mod ++ showWithName name dataSig
    ++ " =" ++ indent (intercalate "\n" (map (showVariant . unmeta) dataVariants))
    where
      mod = if dataMod then "mod " else ""
      showVariant (name, types) =
        show name ++ " " ++ unwords (map show types)

-- | Adds a 'DataDecl' to the module
modAddData
  :: AddError m
  => Meta Name
  -> DataDecl
  -> FilePath
  -> Module
  -> m Module
modAddData name decl path mod = do
  let
    oldDatas = modDatas mod
    newDecl = path :/: decl
  when (Map.member name oldDatas) $
    addError CompileError
      { errorFile = Just path
      , errorSpan = metaSpan name
      , errorKind = Error
      , errorMessage = "duplicate data type declaration for name `" ++ show name ++ "`" }
  return mod { modDatas = Map.insert name newDecl oldDatas }

-- | A common subset of the possibilities for a type or effect
data MaybeLowercase
  = MLNamed Path
  | MLPoly String
  | MLAnon
  | MLOther String

-- | Tries to extract a 'DataDecl' parameter if possible
extractParameter :: AddError m
                 => (String -> m (Maybe (Meta String, TypeVariance)))
                 -> Maybe Span
                 -> String
                 -> MaybeLowercase
                 -> m (Maybe (Meta String, TypeVariance))
extractParameter err span kind = \case
  MLNamed SymbolOutput ->
    unnamed VOutput
  MLNamed SymbolInput ->
    unnamed VInput
  MLNamed (Path path) ->
    case path of
      [Identifier ('_':rest)] ->
        let
          suggestion =
            case rest of
              (x:_) | isAlpha x ->
                ", did you mean `" ++ lowerFirst rest ++ "`?"
              _ -> ""
        in
          err (kind ++ " parameter name must start with a lowercase letter" ++ suggestion)
      [Identifier name] ->
        err (kind ++ " parameter name must be lowercase, did you mean `" ++ lowerFirst name ++ "`?")
      _ ->
        err (kind ++ " parameter name must be unqualified, did you mean `" ++ show (last path) ++ "`?")
  MLPoly local ->
    getNewAnon >>= justParam local . VAnon
  MLAnon ->
    unnamed VInvariant
  MLOther other ->
    err ("expected name for " ++ kind ++ " parameter, found `" ++ other ++ "` instead")
  where
    justParam name var =
      return $ Just ((meta name) { metaSpan = span }, var)
    unnamed var =
      justParam "_" var

-- | Parses a given type as a 'DataArg'
dataArgFromType :: AddError m
                => FilePath
                -> Meta Type
                -> m DataArg
dataArgFromType file typeWithMeta =
  -- It doesn't matter what is returned on error since it won't be needed until the next phase anyway
  case reduceApplyNoInfix typeWithMeta of
    Left path -> do
      addError CompileError
        { errorFile = Just file
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          "type parameter variances must use prefix notation" }
      return $ DataArg VInvariant []
    Right (ReducedApp Meta { unmeta = baseTy, metaSpan = baseSpan } args) -> do
      baseVariance <- case baseTy of
        TNamed [] (DefaultMeta SymbolOutput) -> return VOutput
        TNamed [] (DefaultMeta SymbolInput) -> return VInput
        TAnon _ -> return VInvariant
        _ -> do
          addError CompileError
            { errorFile = Just file
            , errorSpan = baseSpan
            , errorKind = Error
            , errorMessage =
              "expected one of (+), (-), or _ for higher-kinded type parameter variance" }
          return VInvariant
      paramsVariance <- forM args $ dataArgFromType file
      return DataArg
        { argVariance = baseVariance
        , argParams = paramsVariance }

-- | Tries to parse a given type as a 'DataArg' with a name for the base
namedDataArgFromType :: AddError m
                     => FilePath
                     -> Meta Type
                     -> m (Maybe (Meta String, DataArg))
namedDataArgFromType file typeWithMeta =
  case reduceApplyNoInfix typeWithMeta of
    Left path -> do
      addError CompileError
        { errorFile = Just file
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          "expected a type parameter, not an infix operator" }
      return Nothing
    Right (ReducedApp Meta { unmeta = baseTy, metaSpan = baseSpan } args) -> do
      let
        err msg = do
          addError CompileError
            { errorFile = Just file
            , errorSpan = baseSpan
            , errorKind = Error
            , errorMessage = msg }
          return Nothing
      nameAndVariance <- extractParameter err baseSpan "type" $
        case baseTy of
          TNamed [] path -> MLNamed $ unmeta path
          TPoly local -> MLPoly local
          TAnon _ -> MLAnon
          other -> MLOther (show other)
      case nameAndVariance of
        Nothing -> return Nothing
        Just (name, variance) -> do
          params <- forM args $ dataArgFromType file
          return $ Just (name, DataArg { argVariance = variance, argParams = params })

-- | Tries to parse a named 'DataSig' from a given type
namedDataSigFromType :: AddError m
                     => FilePath                       -- ^ The file where the data type is defined
                     -> Meta Type                      -- ^ The type containing the signature to parse
                     -> m (Maybe (Meta Name), DataSig) -- ^ The parsed name (if valid) and signature
namedDataSigFromType file typeWithMeta =
  case reduceApply typeWithMeta of
    Left (_, b) -> do
      addError CompileError
        { errorFile = Just file
        , errorSpan = metaSpan b
        , errorKind = Error
        , errorMessage =
          "expected only a single operator for data type delcaration, found multiple instead" }
      -- The data signature doesn't matter since the name is invalid anyway
      return (Nothing, DataSig [] [])
    Right (ReducedApp Meta { unmeta = baseTy, metaSpan = nSpan } args) -> do
      (name, effs) <-
        let
          err span msg = do
            addError CompileError
              { errorFile = Just file
              , errorSpan = span
              , errorKind = Error
              , errorMessage = msg }
            return (Nothing, [])
        in
          case baseTy of
            TNamed effs pathWithMeta ->
              let Meta { unmeta = Path path, metaSpan } = pathWithMeta in
              if last path == Operator "->" then
                err metaSpan "data type name cannot be (->) because this is a special item"
              else
                case path of
                  [name] ->
                    return (Just $ copySpan pathWithMeta name, effs)
                  _ ->
                    err metaSpan ("data type name must be unqualified, did you mean `" ++ show (last path) ++ "`?")
            TPoly local ->
              err nSpan ("data type name must be capitalized, did you mean `" ++ capFirst local ++ "`?")
            other ->
              err nSpan ("expected a name for the data type, found `" ++ show other ++ "` instead")
      effs <- forM effs \effSet ->
        let
          err msg = do
            addError CompileError
              { errorFile = Just file
              , errorSpan = metaSpan effSet
              , errorKind = Error
              , errorMessage = msg }
            return Nothing
        in
          case Set.toList $ setEffects $ unmeta effSet of
            [eff] ->
              extractParameter err (metaSpan eff) "effect" $
                case unmeta eff of
                  EffectNamed path -> MLNamed path
                  EffectPoly local -> MLPoly local
                  EffectAnon _ -> MLAnon
            _ -> err "effect parameters must each be in their own set of pipes, you cannot use `+` in between"
      vars <- forM args $ namedDataArgFromType file
      -- Errors can be ignored since they will be checked at the end of the phase (before the signature can be used)
      return (name, DataSig (catMaybes effs) (catMaybes vars))

-- | Tries to parse a 'DataVariant' from a given type
variantFromType :: AddError m
                => FilePath                     -- ^ The file where the data type is defined
                -> Meta Type                    -- ^ The type containing the signature to parse
                -> m (Maybe (Meta DataVariant)) -- ^ The parsed variant (if valid)
variantFromType file typeWithMeta =
  case reduceApply typeWithMeta of
    Left (a, b) -> do
      addError CompileError
        { errorFile = Just file
        , errorSpan = metaSpan b
        , errorKind = Error
        , errorMessage =
          if a == b then
            "cannot resolve asoociativity of `" ++ show b ++ "` without explicit parentheses"
          else
            "cannot resolve relative operator precedence of `"
            ++ show b ++ "` after `" ++ show a ++ "` without explicit parentheses" }
      return Nothing
    Right (ReducedApp baseTy args) ->
      let
        err msg = do
          addError CompileError
            { errorFile = Just file
            , errorSpan = metaSpan baseTy
            , errorKind = Error
            , errorMessage = msg }
          return Nothing
      in
        case unmeta baseTy of
          TNamed _ Meta { unmeta = Core (Operator "->") } ->
            err "data type variant name cannot use (->) in an infix position, this syntax is reserved for types"
          TNamed (eff : _) _ -> do
            addError CompileError
              { errorFile = Just file
              , errorSpan = metaSpan eff
              , errorKind = Error
              , errorMessage = "data type variants cannot take effect arguments" }
            return Nothing
          TNamed [] pathWithMeta ->
            let Meta { unmeta = Path path } = pathWithMeta in
            case path of
              [name] ->
                return $ Just $ copySpan typeWithMeta (copySpan pathWithMeta name, args)
              _ ->
                err ("data type variant names must be unqualified, did you mean `" ++ show (last path) ++ "`?")
          TPoly local ->
            err ("data type variant names must be capitalized, did you mean `" ++ capFirst local ++ "`?")
          other ->
            err ("expected a name for the data type variant, found `" ++ show other ++ "` instead")

