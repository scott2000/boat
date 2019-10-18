module Program where

import Basics
import AST

import Data.List

import Data.Map (Map)
import qualified Data.Map.Strict as Map

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
  show (_ :/: x) = show x

type OpTypeEnds = (Maybe (Meta Path), Maybe (Meta Path))

data AllDecls = AllDecls
  { allOpTypes :: !(Map (Meta Path) (InFile OpTypeEnds))
  , allOpDecls :: !(Map (Meta Path) (InFile OpDecl))
  , allDatas :: !(Map (Meta Path) (InFile DataDecl))
  , allLets :: !(Map (Meta Path) (InFile LetDecl)) }

instance Show AllDecls where
  show AllDecls { allOpTypes, allOpDecls, allDatas, allLets } =
    intercalate "\n"
      [ "op types: " ++ intercalate ", " (map show $ Map.keys allOpTypes)
      , "op decls: " ++ intercalate ", " (map show $ Map.keys allOpDecls)
      , "datas: " ++ intercalate ", " (map show $ Map.keys allDatas)
      , "lets: " ++ intercalate ", " (map show $ Map.keys allLets) ]

emptyDecls :: AllDecls
emptyDecls = AllDecls
  { allOpTypes = Map.empty
  , allOpDecls = Map.empty
  , allDatas = Map.empty
  , allLets = Map.empty }

-- TODO: consider removing strictness annotation?

data Module = Module
  { modUses :: ![InFile (Meta UseModule)]
  , modSubs :: !(Map Name [Module])
  , modOpTypes :: ![InFile OpType]
  , modOpDecls :: !(Map (Meta Name) (InFile OpDecl))
  , modDatas :: !(Map (Meta Name) (InFile DataDecl))
  , modLets :: !(Map (Meta Name) (InFile LetDecl)) }

instance Show Module where
  show mod = intercalate "\n" $ concat
      [ map showUse $ reverse $ modUses mod
      , map showMod $ Map.toList $ modSubs mod
      , map showOpType $ reverse $ modOpTypes mod
      , map showOpDecl $ Map.toList $ modOpDecls mod
      , map showData $ Map.toList $ modDatas mod
      , map showLet $ Map.toList $ modLets mod ]
    where
      showUse use =
        "use " ++ show use
      showMod (name, mods) =
        intercalate "\n" $ mods <&> \mod ->
          "mod " ++ show name ++ " =" ++ indent (show mod)
      showOpType (_ :/: ops) =
        "operator type " ++ intercalate " < " (map show ops)
      showOpDecl (name, _ :/: op) =
        "operator" ++ assoc ++ " " ++ show name ++ " : " ++ show (opType op)
        where
          assoc =
            case opAssoc op of
              ANon -> ""
              ALeft -> " <left>"
              ARight -> " <right>"
      showLet (name, _ :/: LetDecl { letBody }) =
        "let " ++ show name ++ " =" ++ indent (show letBody)
      showData (name, _ :/: DataDecl { dataArgs, dataVariants }) =
        "data " ++ unwords (show name : map unmeta dataArgs)
        ++ " =" ++ indent (intercalate "\n" (map (showVariant . unmeta) dataVariants))
      showVariant (name, types) =
        show name ++ " " ++ unwords (map show types)

defaultModule :: Module
defaultModule = Module
  { modUses = []
  , modSubs = Map.empty
  , modOpTypes = []
  , modOpDecls = Map.empty
  , modDatas = Map.empty
  , modLets = Map.empty }

moduleFromSubs :: Name -> [Module] -> Module
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

newtype LetDecl = LetDecl
  { letBody :: Meta Expr }

modAddLet
  :: MonadState CompileState m
  => Meta Name
  -> Meta Expr
  -> FilePath
  -> Module
  -> m Module
modAddLet name body path mod = do
  let
    oldLets = modLets mod
    newDecl = path :/: LetDecl
      { letBody = body }
  when (Map.member name oldLets) $
    addError CompileError
      { errorFile = Just path
      , errorSpan = metaSpan name
      , errorKind = Error
      , errorMessage = "duplicate let binding for name `" ++ show name ++ "`" }
  return mod { modLets = Map.insert name newDecl oldLets }

type DataVariant = (Meta Name, [Meta Type])

data DataDecl = DataDecl
  { dataArgs :: [Meta String]
  , dataVariants :: [Meta DataVariant] }

modAddData
  :: MonadState CompileState m
  => Meta Name
  -> [Meta String]
  -> [Meta DataVariant]
  -> FilePath
  -> Module
  -> m Module
modAddData name args vars path mod = do
  let
    oldDatas = modDatas mod
    newDecl = path :/: DataDecl
      { dataArgs = args
      , dataVariants = vars }
  when (unmeta name /= Operator "->") $
    case find ((Operator "->" ==) . unmeta) $ map (fst . unmeta) vars of
      Just Meta { metaSpan = arrowSpan } ->
        addError CompileError
          { errorFile = Just path
          , errorSpan = arrowSpan
          , errorKind = Warning
          , errorMessage = "data type `" ++ show name ++ "` contains type constructor named (->)" }
      Nothing ->
        return ()
  when (Map.member name oldDatas) $
    addError CompileError
      { errorFile = Just path
      , errorSpan = metaSpan name
      , errorKind = Error
      , errorMessage = "duplicate data type declaration for name `" ++ show name ++ "`" }
  return mod { modDatas = Map.insert name newDecl oldDatas }

variantFromType :: Meta Type -> Either String (Meta DataVariant)
variantFromType typeWithMeta = do
  (f, xs) <- reduceApply typeWithMeta
  case unmeta f of
    TNamed (Path path) ->
      case path of
        [name] ->
          Right $ copySpan typeWithMeta (copySpan f name, xs)
        _ ->
          Left ("data type variant names must be unqualified, did you mean `" ++ show (last path) ++ "`?")
    TPoly local ->
      Left ("data type variant names must be capitalized, did you mean `" ++ capFirst local ++ "`?")
    other ->
      Left ("expected a name for the data type variant, found " ++ show other ++ " instead")

