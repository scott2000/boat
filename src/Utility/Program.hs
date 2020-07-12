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
  , dataSigToTypeKind
  , pattern UnnamedArg
  , TypeVariance (..)
  , TypeKind (..)
  , pattern NullaryKind
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
import Data.Char

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Control.Monad.State.Strict

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
  { iDatas :: !(PathMap DataDecl)
  , iLets :: !(PathMap InferredLetDecl) }

instance Show InferredDecls where
  show InferredDecls { iDatas, iLets } =
    intercalate "\n" $ concat
      [ showDeclHashMap iDatas
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
    when (name `HashMap.member` oldOps) $
      addError compileError
        { errorFile = file
        , errorSpan = span
        , errorMessage = "duplicate operator declaration for name `" ++ show name ++ "`" }
  return mod { modOpDecls = HashMap.fromList newOps <> oldOps }

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
  when (name `HashMap.member` map) $
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
  = Meta info String `IsSubEffectOf` Meta info Path
  | Meta info String `HasKind` TypeKind
  deriving (Ord, Eq)

instance Show (Constraint info) where
  show = \case
    effect `IsSubEffectOf` set ->
      show effect ++ " : " ++ show set
    name `HasKind` typeKind ->
      showWithName (unmeta name) typeKind

instance After (Constraint Span) where
  after m = mapM \case
    eff `IsSubEffectOf` super ->
      IsSubEffectOf eff <$> afterPath m KEffect super
    other ->
      return other

-- | A declaration for a top-level binding of an expression
data LetDecl = LetDecl
  { letTypeAscription :: Maybe (MetaR Span Type)
  , letConstraints :: [MetaR Span Constraint]
  , letBody :: MetaR Span Expr }

instance ShowWithName LetDecl where
  showWithName name LetDecl { letTypeAscription, letConstraints, letBody } =
    let indent = indentationIncrement in
    "let " ++ name ++ typeClause ++ withClause ++ " ="
    ++ newline indent
    ++ showExprBlock indent letBody
    where
      typeClause =
        case letTypeAscription of
          Nothing -> ""
          Just ty -> " : " ++ show ty

      withClause =
        case letConstraints of
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

-- | The kind of a type parameter
data TypeKind = TypeKind
  { kindEffs :: [TypeVariance]
  , kindArgs :: [DataArg] }
  deriving (Ord, Eq)

instance Show TypeKind where
  show = showWithName (show VInvariant)

instance ShowWithName TypeKind where
  showWithName name TypeKind { kindEffs, kindArgs } =
    unwords ((name ++ effectSuffixStr (map show kindEffs)) : map showArg kindArgs)
    where
      showArg (NullaryArg var) = show var
      showArg arg = "(" ++ show arg ++ ")"

-- | Makes a 'TypeKind' that accepts no additional parameters
pattern NullaryKind :: TypeKind
pattern NullaryKind = TypeKind [] []

-- | Represents the kind of a parameter for a 'DataDecl'
data DataArg = DataArg
  { argVariance :: !TypeVariance
  , argKind :: !TypeKind }
  deriving (Ord, Eq)

instance Show DataArg where
  show arg =
    showWithName (show $ argVariance arg) arg

instance ShowWithName DataArg where
  showWithName name =
    showWithName name . argKind

-- | Makes a 'DataArg' that accepts no additional parameters
pattern NullaryArg :: TypeVariance -> DataArg
pattern NullaryArg variance = DataArg variance NullaryKind

-- | Used in place of a name for arguments that weren't named
pattern UnnamedArg :: Meta Span String
pattern UnnamedArg = DefaultMeta "_"

-- | Represents the effect and type parameters a 'DataDecl' can accept
data DataSig = DataSig
  { dataEffs :: [(Meta Span String, TypeVariance)]
  , dataArgs :: [(Meta Span String, DataArg)] }

instance ShowWithName DataSig where
  showWithName name DataSig { dataEffs, dataArgs } =
    unwords ((name ++ effectSuffixStr (map showEff dataEffs)) : map showArg dataArgs)
    where
      showEff (UnnamedArg, eff) = show eff
      showEff (name, _) = unmeta name

      showArg (UnnamedArg, NullaryArg var) = show var
      showArg (UnnamedArg, arg) = "(" ++ show arg ++ ")"
      showArg (name, NullaryArg _) = unmeta name
      showArg (name, arg) = "(" ++ showWithName (unmeta name) arg ++ ")"

-- | Converts a 'DataSig' to a 'TypeKind' by discarding the names of the arguments
dataSigToTypeKind :: DataSig -> TypeKind
dataSigToTypeKind DataSig { dataEffs, dataArgs } = TypeKind
  { kindEffs = map snd dataEffs
  , kindArgs = map snd dataArgs }

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
        show $ expandApp (TNamed . Local <$> name) [] types

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
                       => FilePath                     -- ^ The file being parsed
                       -> MetaR Span Type              -- ^ The initial part of the constraint
                       -> Maybe (MetaR Span EffectSet) -- ^ The ascription part of the constraint (if any)
                       -> m (Maybe (Constraint Span))  -- ^ The parsed constraint (if valid)
disambiguateConstraint file typeWithMeta maybeAscription =
  case maybeAscription of
    Nothing ->
      -- There was no ascription, so this is a type constraint
      case reduceApplyNoInfix typeWithMeta of
        Left _ ->
          -- Anything using an infix operator must be a trait constraint
          traitsUnimplemented
        Right (ReducedApp (baseTy :&: baseSpan) effs args) ->
          let
            err msg = do
              addError compileError
                { errorFile = file
                , errorSpan = baseSpan
                , errorMessage = msg }
              return Nothing
          in
            case baseTy of
              TNamed _ ->
                -- Named types are for trait constraints
                traitsUnimplemented
              TPoly name
                | null effs && null args ->
                  err "expected arguments after kind constraint"
                | otherwise -> do
                  -- This is a kind constraint like (m (+))
                  typeKindFromEffsAndArgs file effs args <&> fmap \argKind ->
                    (name :&: baseSpan) `HasKind` argKind
              TAnon _ -> do
                err "constraint name cannot be left blank"
              _ -> do
                err "expected a name for a constraint"
    Just (bound :&: boundSpan) -> do
      -- There was an ascription, so this is an effect constraint
      eff <-
        let
          err msg = do
            addError compileError
              { errorFile = file
              , errorSpan = getSpan typeWithMeta
              , errorMessage = msg }
            return Nothing
        in
          case unmeta typeWithMeta of
            TNamed _ ->
              err "expected a lowercase effect variable before `:` in constraint"
            TPoly name ->
              return $ Just $ copyInfo typeWithMeta name
            _ ->
              err "expected a single effect variable before `:` in constraint"
      super <-
        let
          err msg = do
            addError compileError
              { errorFile = file
              , errorSpan = boundSpan
              , errorMessage = msg }
            return Nothing
        in
          case esToList bound of
            [eff] ->
              case unmeta eff of
                EffectNamed path ->
                  return $ Just $ path :&: boundSpan
                EffectPoly _ ->
                  err "upper bound for effect constraint cannot be another effect variable"
                _ ->
                  err "upper bound for effect constraint cannot be left blank"
            _ ->
              err "effect variables can only be constrained by a single effect"
      return $ IsSubEffectOf <$> eff <*> super
  where
    traitsUnimplemented = do
      addError compileError
        { errorFile = file
        , errorSpan = getSpan typeWithMeta
        , errorMessage = "trait constraints have not been implemented yet" }
      return Nothing

-- | A common subset of the possibilities for a type or effect
data TypeOrEffect
  = TENamed Path
  | TEPoly String
  | TEAnon
  | TEOther String

instance Show TypeOrEffect where
  show = \case
    TENamed path -> show path
    TEPoly name -> name
    TEAnon -> "_"
    TEOther other -> other

-- | Either a 'Type' or an 'Effect'
class FromTypeOrEffect a where
  -- | Get the 'ExprKind' and the @TypeOrEffect@ from this value
  fromTE :: a -> (ExprKind, TypeOrEffect)

instance FromTypeOrEffect (Type info) where
  fromTE ty =
    (,) KType case ty of
      TNamed path -> TENamed path
      TPoly poly -> TEPoly poly
      TAnon _ -> TEAnon
      other -> TEOther $ show other

instance FromTypeOrEffect Effect where
  fromTE eff =
    (,) KEffect case eff of
      EffectNamed path -> TENamed path
      EffectPoly poly -> TEPoly poly
      EffectAnon _ -> TEAnon
      other -> TEOther $ show other

-- | Extract an unnamed variance from a 'Type' or an 'Effect'
extractUnnamed :: (AddError m, FromTypeOrEffect a) => FilePath -> Meta Span a -> m (Maybe TypeVariance)
extractUnnamed file (typeOrEffect :&: span) =
  case te of
    TENamed SymbolOutput ->
      return $ Just VOutput
    TENamed SymbolInput ->
      return $ Just VInput
    TEAnon ->
      return $ Just VInvariant
    other ->
      err ("expected variance for " ++ show kind ++ " parameter, found `" ++ show other ++ "` instead")
  where
    (kind, te) = fromTE typeOrEffect
    err msg = do
      addError compileError
        { errorFile = file
        , errorSpan = span
        , errorMessage = msg }
      return Nothing

-- | Extract a named argument from a 'Type' or an 'Effect'
extractNamed :: (AddError m, FromTypeOrEffect a)
             => FilePath
             -> Meta Span a
             -> m (Maybe (Meta Span String, TypeVariance))
extractNamed file (typeOrEffect :&: span) =
  case te of
    TENamed SymbolOutput ->
      unnamed VOutput
    TENamed SymbolInput ->
      unnamed VInput
    TENamed (Path { unpath = path }) ->
      case path of
        [Identifier ('_':rest)] ->
          let
            suggestion =
              case rest of
                (x:_) | isAlpha x ->
                  ", did you mean `" ++ lowerFirst rest ++ "`?"
                _ -> ""
          in
            err (show kind ++ " parameter name must start with a lowercase letter" ++ suggestion)
        [Identifier name] ->
          err (show kind ++ " parameter name must be lowercase, did you mean `" ++ lowerFirst name ++ "`?")
        _ ->
          err (show kind ++ " parameter name must be unqualified, did you mean `" ++ show (last path) ++ "`?")
    TEAnon ->
      unnamed VInvariant
    TEPoly local ->
      getNewAnon <&> \anon ->
        Just (local :&: span, VAnon anon)
    TEOther other ->
      err ("expected name for " ++ show kind ++ " parameter, found `" ++ other ++ "` instead")
  where
    (kind, te) = fromTE typeOrEffect
    unnamed var =
      return $ Just ("_" :&: span, var)
    err msg = do
      addError compileError
        { errorFile = file
        , errorSpan = span
        , errorMessage = msg }
      return Nothing

-- | Using an extraction function, extract a single effect from a set of effects
extractSingleEffect :: AddError m
                    => FilePath
                    -> (FilePath -> Meta Span Effect -> m (Maybe a))
                    -> MetaR Span EffectSet
                    -> m (Maybe a)
extractSingleEffect file parseEffect (es :&: span) =
  case esToList es of
    [eff] ->
      parseEffect file eff
    _ -> do
      addError compileError
        { errorFile = file
        , errorSpan = span
        , errorMessage = "each effect parameter must be in its own set of pipes, not separated by `+`" }
      return Nothing

-- | Tries to parse a 'TypeKind' from lists of effect and type arguments
typeKindFromEffsAndArgs :: AddError m => FilePath -> [MetaR Span EffectSet] -> [MetaR Span Type] -> m (Maybe TypeKind)
typeKindFromEffsAndArgs file effs args = do
  effs <- forM effs $ extractSingleEffect file extractUnnamed
  args <- forM args \ty ->
    typeKindFromType file extractUnnamed ty <&> fmap \(argVariance, argKind) ->
      DataArg { argVariance, argKind }
  return $ TypeKind <$> sequence effs <*> sequence args

-- | Tries to parse a 'TypeKind' given a way to parse the head of the type
typeKindFromType :: AddError m
                 => FilePath
                 -> (FilePath -> MetaR Span Type -> m (Maybe a))
                 -> MetaR Span Type
                 -> m (Maybe (a, TypeKind))
typeKindFromType file parseHead typeWithMeta =
  case reduceApplyNoInfix typeWithMeta of
    Left path -> do
      addError compileError
        { errorFile = file
        , errorSpan = getSpan typeWithMeta
        , errorMessage = "unexpected infix operator in type kind declaration: " ++ show path }
      return Nothing
    Right (ReducedApp baseTy effs args) -> do
      head <- parseHead file baseTy
      kind <- typeKindFromEffsAndArgs file effs args
      return $ (,) <$> head <*> kind

-- | Tries to parse a 'DataSig' from a given type
namedDataSigFromType :: AddError m
                     => FilePath                            -- ^ The file where the data type is defined
                     -> MetaR Span Type                     -- ^ The type containing the signature to parse
                     -> m (Maybe (Meta Span Name, DataSig)) -- ^ The parsed name and signature (if valid)
namedDataSigFromType file typeWithMeta =
  case reduceApply typeWithMeta of
    Left (_, _ :&: span) -> do
      addError compileError
        { errorFile = file
        , errorSpan = span
        , errorMessage = "expected only a single operator for data type delcaration, found multiple instead" }
      return Nothing
    Right (ReducedApp (baseTy :&: baseSpan) effs args) -> do
      name <-
        let
          err msg = do
            addError compileError
              { errorFile = file
              , errorSpan = baseSpan
              , errorMessage = msg }
            return Nothing
        in
          case baseTy of
            TNamed Path { unpath = names } ->
              if last names == Operator "->" then
                err "data type name cannot be (->) because this is a special item"
              else
                case names of
                  [name] ->
                    return $ Just $ name :&: baseSpan
                  _ ->
                    err ("data type name must be unqualified, did you mean `" ++ show (last names) ++ "`?")
            TPoly local ->
              err ("data type name must be capitalized, did you mean `" ++ capFirst local ++ "`?")
            other ->
              err ("expected a name for the data type, found `" ++ show other ++ "` instead")
      effs <- forM effs $ extractSingleEffect file extractNamed
      args <- forM args \ty ->
        typeKindFromType file extractNamed ty <&> fmap \((name, argVariance), argKind) ->
          (name, DataArg { argVariance, argKind })
      return $ (,) <$> name <*> (DataSig <$> sequence effs <*> sequence args)

-- | Tries to parse a 'DataVariant' from a given type
variantFromType :: AddError m
                => FilePath                          -- ^ The file where the data type is defined
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
    Right (ReducedApp (baseTy :&: baseSpan) effs args) ->
      let
        err msg = do
          addError compileError
            { errorFile = file
            , errorSpan = baseSpan
            , errorMessage = msg }
          return Nothing
      in
        case baseTy of
          TNamed (Core (Operator "->")) ->
            err "data type variant name cannot use (->) in an infix position, this syntax is reserved for types"
          TNamed Path { unpath = names } ->
            case names of
              [name]
                | (eff : _) <- effs -> do
                  addError compileError
                    { errorFile = file
                    , errorSpan = getSpan eff
                    , errorMessage = "data type variants cannot take effect arguments" }
                  return Nothing
                | otherwise ->
                  return $ Just $ copyInfo typeWithMeta (name :&: baseSpan, args)
              _ ->
                err ("data type variant names must be unqualified, did you mean `" ++ show (last names) ++ "`?")
          TPoly local ->
            err ("data type variant names must be capitalized, did you mean `" ++ capFirst local ++ "`?")
          other ->
            err ("expected a name for the data type variant, found `" ++ show other ++ "` instead")

