module Utility.Program where

import Utility.Basics
import Utility.AST

import Data.List
import Data.Maybe
import Data.Char

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified Data.Set as Set

import Control.Monad.State.Strict

data InFile a = (:/:)
  { getFile :: FilePath
  , unfile :: a }
  deriving (Functor, Foldable, Traversable)

instance Ord a => Ord (InFile a) where
  (_ :/: a) `compare` (_ :/: b) =
    a `compare` b

instance Eq a => Eq (InFile a) where
  (_ :/: a) == (_ :/: b) = a == b

instance Show a => Show (InFile a) where
  showsPrec i = showsPrec i . unfile

class ShowWithName a where
  showWithName :: String -> a -> String

instance ShowWithName a => ShowWithName (Meta a) where
  showWithName name = showWithName name . unmeta

instance ShowWithName a => ShowWithName (InFile a) where
  showWithName name = showWithName name . unfile

showDecl :: (ShowWithName a, Show s) => (s, a) -> String
showDecl (name, decl) = showWithName (show name) decl

showDeclMap :: (ShowWithName a, Show s) => Map s a -> [String]
showDeclMap = map showDecl . Map.toList

type OpTypeEnds = (Maybe (Meta Path), Maybe (Meta Path))

data AllDecls = AllDecls
  { allOpTypes :: !(Map (Meta Path) (InFile OpTypeEnds))
  , allOpDecls :: !(Map (Meta Path) (InFile OpDecl))
  , allEffects :: !(Map (Meta Path) (InFile EffectDecl))
  , allDatas :: !(Map (Meta Path) (InFile DataDecl))
  , allLets :: !(Map (Meta Path) (InFile LetDecl)) }

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

emptyDecls :: AllDecls
emptyDecls = AllDecls
  { allOpTypes = Map.empty
  , allOpDecls = Map.empty
  , allEffects = Map.empty
  , allDatas = Map.empty
  , allLets = Map.empty }

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

defaultModule :: Module
defaultModule = Module
  { modUses = []
  , modSubs = Map.empty
  , modOpTypes = []
  , modOpDecls = Map.empty
  , modEffects = Map.empty
  , modDatas = Map.empty
  , modLets = Map.empty }

moduleFromSubs :: Name -> [Module] -> Module
moduleFromSubs _ [] = defaultModule
moduleFromSubs name mods = defaultModule
  { modSubs = Map.singleton name mods }

modIsEmpty :: Module -> Bool
modIsEmpty m =
  null (modUses m)
  && Map.null (modSubs m)
  && null (modOpTypes m)
  && Map.null (modOpDecls m)
  && Map.null (modDatas m)
  && Map.null (modLets m)

modAddUse :: Meta UseModule -> FilePath -> Module -> Module
modAddUse use path mod = mod
  { modUses = path :/: use : modUses mod }

modAddSub :: Name -> Module -> Module -> Module
modAddSub name sub mod =
  if modIsEmpty sub then mod else mod
    { modSubs = Map.insertWith (flip (++)) name [sub] $ modSubs mod }

type OpType = [OpPart]

data OpPart
  = OpDeclare (Meta Name)
  | OpLink (Meta Path)
  deriving (Ord, Eq)

instance Show OpPart where
  show = \case
    OpDeclare name ->
      show name
    OpLink path ->
      "(" ++ show path ++ ")"

modAddOpType :: OpType -> FilePath -> Module -> Module
modAddOpType ops path mod = mod
  { modOpTypes = path :/: ops : modOpTypes mod }

opTypeDeclarations :: OpType -> [Name]
opTypeDeclarations ops = do
  op <- ops
  case op of
    OpDeclare name ->
      return $ unmeta name
    OpLink _ ->
      mempty

data Associativity
  = ANon
  | ALeft
  | ARight

instance Show Associativity where
  show = \case
    ANon   -> "non"
    ALeft  -> "left"
    ARight -> "right"

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

modAddOpDecls
  :: MonadState CompileState m
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
  forM_ names $ \name ->
    when (Map.member name oldOps) $
      addError CompileError
        { errorFile = Just path
        , errorSpan = metaSpan name
        , errorKind = Error
        , errorMessage = "duplicate operator declaration for name `" ++ show name ++ "`" }
  return mod { modOpDecls = Map.union (Map.fromList newOps) oldOps }

data EffectDecl = EffectDecl
  { effectSuper :: Maybe (Meta Path) }

instance ShowWithName EffectDecl where
  showWithName name EffectDecl { effectSuper } =
    "effect " ++ name ++
      case effectSuper of
        Nothing -> ""
        Just effect ->
          " : " ++ show effect

modAddEffect
  :: MonadState CompileState m
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

data LetDecl = LetDecl
  { letBody :: Meta Expr
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

modAddLet
  :: MonadState CompileState m
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

data TypeVariance
  -- An uninferred variance for DataDecl parameter
  = VAnon AnonCount
  -- Covariance, represented as (+) for high-order parameters
  | VOutput
  -- Contravariance, represented as (-) for high-order parameters
  | VInput
  -- Invariance, represented as _ for high-order parameters
  | VInvariant
  deriving (Ord, Eq)

instance Show TypeVariance where
  show = \case
    VAnon _ -> "<unknown>"
    VOutput -> show SymbolOutput
    VInput -> show SymbolInput
    VInvariant -> show SymbolInvariannt

instance Semigroup TypeVariance where
  VOutput <> x = x
  VInvariant <> _ = VInvariant
  x <> VOutput = x
  _ <> VInvariant = VInvariant
  VInput <> VInput = VOutput

pattern SymbolOutput :: Type
pattern SymbolOutput = TNamed [] (DefaultMeta (Local (Operator "+")))

pattern SymbolInput :: Type
pattern SymbolInput = TNamed [] (DefaultMeta (Local (Operator "-")))

pattern SymbolInvariannt :: Type
pattern SymbolInvariannt = TAnon AnonAny

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

pattern NullaryArg :: TypeVariance -> DataArg
pattern NullaryArg var = DataArg var []

data DataSig = DataSig
  { dataEffects :: [(Meta String, TypeVariance)]
  , dataArgs :: [(Meta String, DataArg)] }

instance ShowWithName DataSig where
  showWithName name DataSig { dataArgs, dataEffects } =
    name ++ effectSuffixStr (map (show . fst) dataEffects) ++ unwords ("" : map showArg dataArgs)
    where
      showArg (name, dataArg) = showWithName (unmeta name) dataArg

type DataVariant = (Meta Name, [Meta Type])

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

modAddData
  :: MonadState CompileState m
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

data MaybeLowercase
  = MLNamed Path
  | MLPoly String
  | MLOther String

extractLowercase :: MonadState CompileState m
                 => (String -> m (Maybe (Meta String, TypeVariance)))
                 -> Maybe Span
                 -> String
                 -> MaybeLowercase
                 -> m (Maybe (Meta String, TypeVariance))
extractLowercase err span kind = \case
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
  MLPoly local -> do
    anon <- getNewAnon
    return $ Just ((meta local) { metaSpan = span }, VAnon anon)
  MLOther other ->
    err ("expected name for " ++ kind ++ " parameter, found `" ++ other ++ "` instead")

dataArgFromType :: MonadState CompileState m
                => FilePath
                -> Meta Type
                -> m DataArg
dataArgFromType file typeWithMeta =
  case reduceApply typeWithMeta of
    Left (_, b) -> do
      addError CompileError
        { errorFile = Just file
        , errorSpan = metaSpan b
        , errorKind = Error
        , errorMessage =
          "cannot resolve operator precedence (try not to use infix operators for variance)" }
      return $ DataArg VInvariant []
    Right (ReducedApp Meta { unmeta = baseTy, metaSpan = baseSpan } args) -> do
      baseVariance <- case baseTy of
        SymbolOutput -> return VOutput
        SymbolInput -> return VInput
        SymbolInvariannt -> return VInvariant
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

namedDataArgFromType :: MonadState CompileState m
                     => FilePath
                     -> Meta Type
                     -> m (Maybe (Meta String, DataArg))
namedDataArgFromType file typeWithMeta =
  case reduceApply typeWithMeta of
    Left (a, _) -> do
      addError CompileError
        { errorFile = Just file
        , errorSpan = metaSpan a
        , errorKind = Error
        , errorMessage =
          "expected a type parameter, not a series of infix operators" }
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
      nameAndVariance <- extractLowercase err baseSpan "type" $
        case baseTy of
          TNamed [] path -> MLNamed $ unmeta path
          TPoly local -> MLPoly local
          other -> MLOther (show other)
      case nameAndVariance of
        Nothing -> return Nothing
        Just (name, variance) -> do
          params <- forM args $ dataArgFromType file
          return $ Just (name, DataArg { argVariance = variance, argParams = params })

dataAndArgsFromType :: MonadState CompileState m
                    => FilePath
                    -> Meta Type
                    -> m (Maybe (Meta Name), [(Meta String, TypeVariance)], [(Meta String, DataArg)])
dataAndArgsFromType file typeWithMeta =
  case reduceApply typeWithMeta of
    Left (_, b) -> do
      addError CompileError
        { errorFile = Just file
        , errorSpan = metaSpan b
        , errorKind = Error
        , errorMessage =
          "expected only a single operator for data type delcaration, found multiple instead" }
      return (Nothing, [], [])
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
      effs <- forM effs $ \effSet ->
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
              extractLowercase err (metaSpan eff) "effect" $
                case unmeta eff of
                  EffectNamed path -> MLNamed path
                  EffectPoly local -> MLPoly local
                  other -> MLOther (show other)
            _ -> err "effect parameters must each be in their own set of pipes, you cannot use `+` in between"
      vars <- forM args $ namedDataArgFromType file
      return (name, catMaybes effs, catMaybes vars)

variantFromType :: MonadState CompileState m => FilePath -> Meta Type -> m (Maybe (Meta DataVariant))
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

