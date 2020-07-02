-- | Utilities for dealing with top-level declarations and full packages
module Utility.Program
  ( -- * Top-Level Declarations
    ShowWithName (..)
  , Associativity (..)
  , OpDecl (..)
  , EffectDecl (..)
  , Constraint (..)
  , disambiguateConstraint
  , LetDecl (..)
  , InferredLetDecl (..)

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
  , PathMap
  , AllDecls (..)
  , InferredDecls (..)
  , emptyDecls

    -- * Nested Module Representation
  , NameMap
  , Module (..)
  , defaultModule
  , moduleFromSubs
  , modIsEmpty
  , moduleAddLocalImports
  , moduleAddCoreImports

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

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

-- | Class for showing a value with an externally provided name
class ShowWithName a where
  -- | Show the declaration using the provided name
  showWithName :: String -> a -> String

instance ShowWithName a => ShowWithName (Meta info a) where
  showWithName name = showWithName name . unmeta

-- | Shows a key-value pair where the key is the name
showDecl :: (ShowWithName a, Show s) => (s, a) -> String
showDecl (name, decl) = showWithName (show name) decl

-- | Shows every item in a 'Map' where the key is the name
showDeclMap :: (ShowWithName a, Show s) => Map s a -> [String]
showDeclMap = map showDecl . Map.toAscList

-- | Shows every item in a 'HashMap' where the key is the name
showDeclHashMap :: (ShowWithName a, Show s) => HashMap s a -> [String]
showDeclHashMap = map showDecl . HashMap.toList

-- | A map of declarations using a 'Path' as the key
type PathMap a = HashMap Path (Meta (InFile Span) a)

-- | Represents the upper and lower bound for the precedence of an operator type
type OpTypeEnds = (Maybe (Meta Span Path), Maybe (Meta Span Path))

-- | A collection of all declarations in a package by absolute path
data AllDecls = AllDecls
  { allOpTypes :: !(PathMap OpTypeEnds)
  , allOpDecls :: !(PathMap OpDecl)
  , allEffects :: !(PathMap EffectDecl)
  , allDatas :: !(PathMap DataDecl)
  , allLets :: !(PathMap LetDecl) }

instance Show AllDecls where
  show AllDecls { allOpTypes, allOpDecls, allEffects, allDatas, allLets } =
    intercalate "\n" $ concat
      [ map showOpType $ HashMap.toList allOpTypes
      , showDeclHashMap allOpDecls
      , showDeclHashMap allEffects
      , showDeclHashMap allDatas
      , showDeclHashMap allLets ]
    where
      showOpType (path, (left, right) :&: _) =
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
  { allOpTypes = HashMap.empty
  , allOpDecls = HashMap.empty
  , allEffects = HashMap.empty
  , allDatas = HashMap.empty
  , allLets = HashMap.empty }

-- | Like 'AllDecls', but with all types inferred and some information discarded
data InferredDecls = InferredDecls
  { iEffects :: !(PathMap EffectDecl)
  , iDatas :: !(PathMap DataDecl)
  , iLets :: !(PathMap InferredLetDecl) }

instance Show InferredDecls where
  show InferredDecls { iEffects, iDatas, iLets } =
    intercalate "\n" $ concat
      [ showDeclHashMap iEffects
      , showDeclHashMap iDatas
      , showDeclHashMap iLets ]

-- | Like 'LetDecl', but with all types inferred and some extra information
data InferredLetDecl = InferredLetDecl
  { iLetBody :: MetaR (Typed Span) Expr
  , iLetConstraints :: [MetaR () Constraint]
  , iLetInferredType :: Type ()
  , iLetInstanceArgs :: [String] }

instance ShowWithName InferredLetDecl where
  showWithName name InferredLetDecl { iLetInferredType } =
    "let " ++ name ++ " : " ++ show iLetInferredType

-- | A map of declarations using a 'Name' as the key
type NameMap a = HashMap Name (Meta (InFile Span) a)

-- | A direct representation of a parsed module that hasn't been flattened yet
data Module = Module
  { modUses :: ![InFile (Meta Span UseModule)]
  , modSubs :: !(HashMap Name [Module])
  , modOpTypes :: ![InFile OpType]
  , modOpDecls :: !(NameMap OpDecl)
  , modEffects :: !(NameMap EffectDecl)
  , modDatas :: !(NameMap DataDecl)
  , modLets :: !(NameMap LetDecl) }

instance Show Module where
  show Module { modUses, modSubs, modOpTypes, modOpDecls, modEffects, modDatas, modLets } =
    intercalate "\n" $ concat
      [ map showUse $ reverse modUses
      , map showMod $ HashMap.toList modSubs
      , map showOpType $ reverse modOpTypes
      , showDeclHashMap modOpDecls
      , showDeclHashMap modEffects
      , showDeclHashMap modDatas
      , showDeclHashMap modLets ]
    where
      showUse (_ :/: use) =
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
  , modSubs = HashMap.empty
  , modOpTypes = []
  , modOpDecls = HashMap.empty
  , modEffects = HashMap.empty
  , modDatas = HashMap.empty
  , modLets = HashMap.empty }

-- | Creates a module from a name and a set of sub-modules to associate with that name
moduleFromSubs :: Name -> [Module] -> Module
moduleFromSubs _ [] = defaultModule
moduleFromSubs name mods = defaultModule
  { modSubs = HashMap.singleton name mods }

-- | Checks if a given module is empty
modIsEmpty :: Module -> Bool
modIsEmpty m =
  null (modUses m)
  && HashMap.null (modSubs m)
  && null (modOpTypes m)
  && HashMap.null (modOpDecls m)
  && HashMap.null (modDatas m)
  && HashMap.null (modLets m)

-- | A 'UseModule' that includes something from Core
pattern CoreInclude :: DefaultInfo info => UseContents -> InFile (Meta info UseModule)
pattern CoreInclude contents =
  NoFile :/: DefaultMeta (UseModule (DefaultMeta (Identifier "Core")) contents)

-- | Add an import to bring every local item into scope
moduleAddLocalImports :: Module -> Module
moduleAddLocalImports m = m
  { modUses = NoFile :/: meta UseAny : modUses m }

-- | Add a Core import if it wasn't explicitly imported
moduleAddCoreImports :: Module -> Module
moduleAddCoreImports m = m
  { modUses = addCore $ modUses m }
  where
    addCore [] =
      [CoreInclude $ UseAll [meta UseAny]]
    addCore (CoreInclude (UseAll []): rest) =
      rest
    addCore list@(CoreInclude _ : _) =
      list
    addCore (use:rest) =
      use : addCore rest

-- | Adds a 'UseModule' to the module
modAddUse :: FilePath -> Meta Span UseModule -> Module -> Module
modAddUse file use mod = mod
  { modUses = file :/: use : modUses mod }

-- | Adds a sub-module to the module
modAddSub :: Name -> Module -> Module -> Module
modAddSub name sub mod =
  if modIsEmpty sub then mod else mod
    { modSubs = HashMap.insertWith (flip (++)) name [sub] $ modSubs mod }

-- | A list of parts of an operator type declaration
type OpType = [OpPart]

-- | A single term in an operator type declaration
data OpPart
  -- | A declaration of a new operator type
  = OpDeclare (Meta Span Name)
  -- | A reference to an already declared operator type in parentheses
  | OpLink (Meta Span Path)

instance Show OpPart where
  show = \case
    OpDeclare name ->
      show name
    OpLink path ->
      "(" ++ show path ++ ")"

-- | Adds an 'OpType' declaration to the module
modAddOpType :: FilePath -> OpType -> Module -> Module
modAddOpType file ops mod = mod
  { modOpTypes = file :/: ops : modOpTypes mod }

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
  , opType :: Meta Span Path }

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
  => FilePath
  -> [Meta Span Name]
  -> OpDecl
  -> Module
  -> m Module
modAddOpDecls file names op mod = do
  let
    oldOps = modOpDecls mod
    newOps = names <&> \(name :&: span) ->
      (name, op :&: file :/: span)
  forM_ names \(name :&: span) ->
    when (HashMap.member name oldOps) $
      addError compileError
        { errorFile = file
        , errorSpan = span
        , errorMessage = "duplicate operator declaration for name `" ++ show name ++ "`" }
  return mod { modOpDecls = HashMap.union (HashMap.fromList newOps) oldOps }

-- | A declaration of a new effect with an optional super-effect
data EffectDecl = EffectDecl
  { effectSuper :: [Meta Span Path] }

instance ShowWithName EffectDecl where
  showWithName name EffectDecl { effectSuper } =
    "effect " ++ name ++
      case effectSuper of
        [] -> ""
        _ ->
          " : " ++ intercalate ", " (map show effectSuper)

-- | Try to insert a declaration into a 'NameMap' with a given error message for failure
insertWithError :: AddError m => FilePath -> Meta Span Name -> a -> String -> NameMap a -> m (NameMap a)
insertWithError file (name :&: span) decl errorMessage map = do
  when (HashMap.member name map) $
    addError compileError
      { errorFile = file
      , errorSpan = span
      , errorMessage }
  return $ HashMap.insert name (decl :&: file :/: span) map

-- | Adds an 'EffectDecl' to the module
modAddEffect
  :: AddError m
  => FilePath
  -> Meta Span Name
  -> EffectDecl
  -> Module
  -> m Module
modAddEffect file name decl mod = do
  insertWithError file name decl
    ("duplicate effect declaration for name `" ++ show name ++ "`")
    (modEffects mod) <&> \modEffects -> mod { modEffects }

-- | A constraint from a with-clause in a declaration
data Constraint info
  = Meta info Effect `IsSubEffectOf` EffectSet info
  | Meta info String `HasArguments` [DataArg]
  deriving (Ord, Eq)

instance Show (Constraint info) where
  show = \case
    effect `IsSubEffectOf` set ->
      show effect ++ " : " ++ show set
    name `HasArguments` args ->
      showWithName (unmeta name) $ DataArg VInvariant args

-- | A declaration for a top-level binding of an expression
data LetDecl = LetDecl
  { letBody :: MetaR Span Expr
  , letConstraints :: [MetaR Span Constraint] }

instance ShowWithName LetDecl where
  showWithName name decl =
    "let " ++ name ++ typeClause ++ withClause ++ " =" ++ indent (show body)
    where
      (body, typeClause) =
        case letBody decl of
          ETypeAscribe expr ty :&: _ ->
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
  => FilePath
  -> Meta Span Name
  -> LetDecl
  -> Module
  -> m Module
modAddLet file name decl mod = do
  insertWithError file name decl
    ("duplicate let binding for name `" ++ show name ++ "`")
    (modLets mod) <&> \modLets -> mod { modLets }

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
  deriving (Ord, Eq)

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
  _ <> _ = error "(<>) called with VAnon"

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
  deriving (Ord, Eq)

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
pattern UnnamedArg :: Meta Span String
pattern UnnamedArg = DefaultMeta "_"

-- | Represents the effect and type parameters a 'DataDecl' can accept
data DataSig = DataSig
  { dataEffects :: [(Meta Span String, TypeVariance)]
  , dataArgs :: [(Meta Span String, DataArg)] }

instance ShowWithName DataSig where
  showWithName name DataSig { dataArgs, dataEffects } =
    name ++ effectSuffixStr (map (unmeta . fst) dataEffects) ++ unwords ("" : map showArg dataArgs)
    where
      showArg (name, dataArg) = showWithName (unmeta name) dataArg

-- | A single variant of a 'DataDecl'
type DataVariant = (Meta Span Name, [MetaR Span Type])

-- | Represents a declaration of a new data type
data DataDecl = DataDecl
  { dataMod :: Bool
  , dataSig :: !DataSig
  , dataVariants :: [Meta Span DataVariant] }

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
  => FilePath
  -> Meta Span Name
  -> DataDecl
  -> Module
  -> m Module
modAddData file name decl mod = do
  insertWithError file name decl
    ("duplicate data type declaration for name `" ++ show name ++ "`")
    (modDatas mod) <&> \modDatas -> mod { modDatas }

-- | Parses a constraint from a type that would be ambiguous on its own
disambiguateConstraint :: AddError m
                       => FilePath
                       -> MetaR Span Type
                       -> Maybe (EffectSet Span)
                       -> m (Maybe (Constraint Span))
disambiguateConstraint file typeWithMeta maybeAscription =
  case maybeAscription of
    Nothing ->
      -- There was no ascription, so this is a type constraint
      case reduceApplyNoInfix typeWithMeta of
        Left _ ->
          -- Anything using an infix operator must be a trait constraint
          traitsUnimplemented
        Right (ReducedApp (baseTy :&: baseSpan) args) ->
          case baseTy of
            TNamed _ _ ->
              -- Named types are for trait constraints
              traitsUnimplemented
            TPoly name
              | null args -> do
                addError compileError
                  { errorFile = file
                  , errorSpan = getSpan typeWithMeta
                  , errorMessage = "expected arguments after kind constraint" }
                return Nothing
              | otherwise -> do
                -- This is a kind constraint like (m (+))
                argKinds <- forM args $ dataArgFromType file
                return $ Just $ (name :&: baseSpan) `HasArguments` argKinds
            TAnon _ -> do
              addError compileError
                { errorFile = file
                , errorSpan = baseSpan
                , errorMessage = "constraint name cannot be left blank" }
              return Nothing
            _ -> do
              addError compileError
                { errorFile = file
                , errorSpan = baseSpan
                , errorMessage = "expected a name for a constraint" }
              return Nothing
    Just bound -> runMaybeT do
      -- There was an ascription, so this is an effect constraint
      eff <-
        case unmeta typeWithMeta of
          TNamed [] name ->
            return $ EffectNamed $ unmeta name
          TPoly name ->
            return $ EffectPoly name
          TAnon anon -> do
            addError compileError
              { errorFile = file
              , errorSpan = getSpan typeWithMeta
              , errorMessage = "expected a specific effect before `:` in constraint" }
            return $ EffectAnon anon
          _ -> MaybeT do
            addError compileError
              { errorFile = file
              , errorSpan = getSpan typeWithMeta
              , errorMessage = "expected a single effect before `:` in constraint" }
            return Nothing
      forM_ (setEffects bound) \eff ->
        case unmeta eff of
          EffectAnon _ ->
            addError compileError
              { errorFile = file
              , errorSpan = getSpan eff
              , errorMessage = "effect in constraint cannot be left blank" }
          _ -> return ()
      return $ copyInfo typeWithMeta eff `IsSubEffectOf` bound
  where
    traitsUnimplemented = do
      addError compileError
        { errorFile = file
        , errorSpan = getSpan typeWithMeta
        , errorMessage = "trait constraints have not been implemented yet" }
      return Nothing

-- | A common subset of the possibilities for a type or effect
data MaybeLowercase
  = MLNamed Path
  | MLPoly String
  | MLAnon
  | MLOther String

-- | Tries to extract a 'DataDecl' parameter if possible
extractParameter :: AddError m
                 => (String -> m (Maybe (Meta Span String, TypeVariance)))
                 -> Span
                 -> String
                 -> MaybeLowercase
                 -> m (Maybe (Meta Span String, TypeVariance))
extractParameter err span kind = \case
  MLNamed SymbolOutput ->
    unnamed VOutput
  MLNamed SymbolInput ->
    unnamed VInput
  MLNamed (Path { unpath = path }) ->
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
      return $ Just (name :&: span, var)
    unnamed var =
      justParam "_" var

-- | Parses a given type as a 'DataArg'
dataArgFromType :: AddError m
                => FilePath
                -> MetaR Span Type
                -> m DataArg
dataArgFromType file typeWithMeta =
  -- It doesn't matter what is returned on error since it won't be needed until the next phase anyway
  case reduceApplyNoInfix typeWithMeta of
    Left path -> do
      addError compileError
        { errorFile = file
        , errorSpan = getSpan path
        , errorCategory = Just ECInferVariance
        , errorMessage =
          "type parameter variances must use prefix notation" }
      return $ DataArg VInvariant []
    Right (ReducedApp (baseTy :&: baseSpan) args) -> do
      baseVariance <- case baseTy of
        TNamed [] (DefaultMeta SymbolOutput) -> return VOutput
        TNamed [] (DefaultMeta SymbolInput) -> return VInput
        TAnon _ -> return VInvariant
        _ -> do
          addError compileError
            { errorFile = file
            , errorSpan = baseSpan
            , errorCategory = Just ECInferVariance
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
                     -> MetaR Span Type
                     -> m (Maybe (Meta Span String, DataArg))
namedDataArgFromType file typeWithMeta =
  case reduceApplyNoInfix typeWithMeta of
    Left path -> do
      addError compileError
        { errorFile = file
        , errorSpan = getSpan path
        , errorMessage =
          "expected a type parameter, not an infix operator" }
      return Nothing
    Right (ReducedApp (baseTy :&: baseSpan) args) -> do
      let
        err msg = do
          addError compileError
            { errorFile = file
            , errorSpan = baseSpan
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
                     => FilePath                           -- ^ The file where the data type is defined
                     -> MetaR Span Type                     -- ^ The type containing the signature to parse
                     -> m (Maybe (Meta Span Name), DataSig) -- ^ The parsed name (if valid) and signature
namedDataSigFromType file typeWithMeta =
  case reduceApply typeWithMeta of
    Left (_, b) -> do
      addError compileError
        { errorFile = file
        , errorSpan = getSpan b
        , errorMessage =
          "expected only a single operator for data type delcaration, found multiple instead" }
      -- The data signature doesn't matter since the name is invalid anyway
      return (Nothing, DataSig [] [])
    Right (ReducedApp (baseTy :&: nSpan) args) -> do
      (name, effs) <-
        let
          err span msg = do
            addError compileError
              { errorFile = file
              , errorSpan = span
              , errorMessage = msg }
            return (Nothing, [])
        in
          case baseTy of
            TNamed effs pathWithMeta ->
              let Path { unpath = names } :&: span = pathWithMeta in
              if last names == Operator "->" then
                err span "data type name cannot be (->) because this is a special item"
              else
                case names of
                  [name] ->
                    return (Just $ copyInfo pathWithMeta name, effs)
                  _ ->
                    err span ("data type name must be unqualified, did you mean `" ++ show (last names) ++ "`?")
            TPoly local ->
              err nSpan ("data type name must be capitalized, did you mean `" ++ capFirst local ++ "`?")
            other ->
              err nSpan ("expected a name for the data type, found `" ++ show other ++ "` instead")
      effs <- forM effs \effSet ->
        let
          err msg = do
            addError compileError
              { errorFile = file
              , errorSpan = getSpan effSet
              , errorMessage = msg }
            return Nothing
        in
          case Set.toList $ setEffects $ unmeta effSet of
            [eff] ->
              extractParameter err (getSpan eff) "effect" $
                case unmeta eff of
                  EffectNamed path -> MLNamed path
                  EffectPoly local -> MLPoly local
                  _ -> MLAnon
            _ -> err "effect parameters must each be in their own set of pipes, you cannot use `+` in between"
      vars <- forM args $ namedDataArgFromType file
      -- Errors can be ignored since they will be checked at the end of the phase (before the signature can be used)
      return (name, DataSig (catMaybes effs) (catMaybes vars))

-- | Tries to parse a 'DataVariant' from a given type
variantFromType :: AddError m
                => FilePath                         -- ^ The file where the data type is defined
                -> MetaR Span Type                   -- ^ The type containing the signature to parse
                -> m (Maybe (Meta Span DataVariant)) -- ^ The parsed variant (if valid)
variantFromType file typeWithMeta =
  case reduceApply typeWithMeta of
    Left (a, b) -> do
      addError compileError
        { errorFile = file
        , errorSpan = getSpan b
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
          addError compileError
            { errorFile = file
            , errorSpan = getSpan baseTy
            , errorMessage = msg }
          return Nothing
      in
        case unmeta baseTy of
          TNamed _ (Core (Operator "->") :&: _) ->
            err "data type variant name cannot use (->) in an infix position, this syntax is reserved for types"
          TNamed (eff : _) _ -> do
            addError compileError
              { errorFile = file
              , errorSpan = getSpan eff
              , errorMessage = "data type variants cannot take effect arguments" }
            return Nothing
          TNamed [] pathWithMeta ->
            let names = unpath $ unmeta pathWithMeta in
            case names of
              [name] ->
                return $ Just $ copyInfo typeWithMeta (copyInfo pathWithMeta name, args)
              _ ->
                err ("data type variant names must be unqualified, did you mean `" ++ show (last names) ++ "`?")
          TPoly local ->
            err ("data type variant names must be capitalized, did you mean `" ++ capFirst local ++ "`?")
          other ->
            err ("expected a name for the data type variant, found `" ++ show other ++ "` instead")

