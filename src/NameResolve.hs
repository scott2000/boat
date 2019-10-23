module NameResolve (nameResolve) where

import Basics
import AST
import Program

import Data.List
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.Reader
import Control.Monad.State.Strict

type NR = ReaderT Names (StateT NameState CompileIO)

type NameSet mark = Map Name (Either (Set Path) (Path, Item, mark))

data Names = Names
  { finalNames :: NameSet ImportId
  , otherNames :: NameSet () }
  deriving Show

defaultNames :: Names
defaultNames = Names
  { finalNames = Map.empty
  , otherNames = Map.empty }

addName :: mark -> Path -> (Name, Item) -> NameSet mark -> NameSet mark
addName id path (name, item) s =
  if Map.member name s then
    Map.adjust collide name s
  else do
    Map.insert name (Right (path, item, id)) s
  where
    collide = \case
      Left paths
        | path `elem` paths -> Left paths
        | otherwise         -> Left $ Set.insert path paths
      Right (oldPath, oldItem, _)
        | path == oldPath
        , item == oldItem -> Right (path, item, id)
        | otherwise       -> Left $ Set.insert path $ Set.singleton oldPath

withNames :: Names -> NR a -> NR a
withNames names nr = lift $ runReaderT nr names

data Item = Item
  { itemSub :: Maybe NameTable
  , isType :: Bool
  , isValue :: Bool
  , isPattern :: Bool
  , isOperatorType :: Bool }
  deriving (Show, Ord, Eq)

instance Semigroup Item where
  a <> b = Item
    { itemSub = itemSub a <> itemSub b
    , isType = isType a || isType b
    , isValue = isValue a || isValue b
    , isPattern = isPattern a || isPattern b
    , isOperatorType = isOperatorType a || isOperatorType b }

instance Monoid Item where
  mempty = Item
    { itemSub = Nothing
    , isType = False
    , isValue = False
    , isPattern = False
    , isOperatorType = False }
  mappend = (<>)

isInfixable :: Item -> Bool
isInfixable item =
  isType item
  || isValue item
  || isPattern item

modItem :: NameTable -> Item
modItem nt = mempty
  { itemSub = Just nt }

typeItem :: Item
typeItem = mempty
  { isType = True }

valueItem :: Item
valueItem = mempty
  { isValue = True }

patternItem :: Item
patternItem = mempty
  { isPattern = True }

operatorTypeItem :: Item
operatorTypeItem = mempty
  { isOperatorType = True }

newtype NameTable = NameTable
  { getNameTable :: Map Name Item }
  deriving (Show, Ord, Eq)

instance Semigroup NameTable where
  NameTable a <> NameTable b =
    NameTable $ Map.unionWith (<>) a b

instance Monoid NameTable where
  mempty = NameTable Map.empty
  mappend = (<>)

toNameTable :: Map Name [Module] -> NameTable
toNameTable =
  NameTable . fmap (modItem . foldr addModule mempty)

addModule :: Module -> NameTable -> NameTable
addModule mod nt = nt
  <> toNameTable (modSubs mod)
  <> foldMap opTypeItem (modOpTypes mod)
  <> convert typeItem (modDatas mod)
  <> convert valueItem (modLets mod)
  <> foldMap patternsForData (Map.toList $ modDatas mod)
  where
    convert k m =
      NameTable $ k <$ Map.mapKeysMonotonic unmeta m
    opTypeItem (_ :/: ops) =
      NameTable $ Map.fromList $ opTypeDeclarations ops <&> \name ->
        (name, operatorTypeItem)
    patternsForData (dataName, _ :/: DataDecl { dataMod, dataVariants }) =
      let
        variantTable =
          NameTable $ Map.fromList $ dataVariants <&> \
            Meta { unmeta = (name, _) } ->
              (unmeta name, valueItem <> patternItem)
      in
        if dataMod then
          NameTable $ Map.singleton (unmeta dataName) mempty
            { itemSub = Just variantTable }
        else
          variantTable

nameTableToList :: NameTable -> [(Name, Item)]
nameTableToList = Map.toList . getNameTable

nameTableEntry :: Name -> NameTable -> Maybe Item
nameTableEntry name = Map.lookup name . getNameTable

nameTableMember :: Name -> NameTable -> Bool
nameTableMember name = Map.member name . getNameTable

type ImportId = Int

hiddenImport :: ImportId
hiddenImport = -1

data NameState = NameState
  { allDecls :: AllDecls
  , nameTable :: NameTable
  , unusedIds :: Map ImportId (InFile Span)
  , importId :: ImportId }

defaultNameState :: NameTable -> NameState
defaultNameState nameTable = NameState
  { allDecls = emptyDecls
  , nameTable
  , unusedIds = Map.empty
  , importId = 0 }

uniqueId :: FilePath -> Maybe Span -> NR ImportId
uniqueId file maybeSpan =
  case maybeSpan of
    Nothing ->
      return hiddenImport
    Just span -> do
      s <- get
      let id = importId s
      put s
        { unusedIds = Map.insert id (file :/: span) $ unusedIds s
        , importId = id + 1 }
      return id

prefixUse :: [Name] -> Meta UseModule -> Meta UseModule
prefixUse []     use = use
prefixUse (n:ns) use =
  meta $ UseModule (meta n) $ UseDot $ prefixUse ns use

addUse :: Path -> InFile (Meta UseModule) -> NR a -> NR a
addUse path (file :/: useWithMeta) nr =
  case useWithMeta of
    Meta { unmeta = UseAny, metaSpan = Just span } -> do
      -- the span is required here because the automatic `use _` doesn't have a span
      -- and we only want to catch imports made by the programmer
      lift $ lift $ addError CompileError
        { errorFile = Just file
        , errorSpan = Just span
        , errorKind = Warning
        , errorMessage = "`use _` does nothing since top level names are imported automatically" }
      nr
    Meta { unmeta = use, metaSpan } -> do
      case use of
        UseModule name (UseAll []) ->
          lift $ lift $ addError CompileError
            { errorFile = Just file
            , errorSpan = metaSpan
            , errorKind = Warning
            , errorMessage = "`use " ++ show name ++ "` does nothing since top level names are imported automatically" }
        _ ->
          return ()
      nt <- gets nameTable
      let
        usePath =
          case use of
            UseModule name _
              | nameTableMember (unmeta name) nt -> useWithMeta
            _ ->
              prefixUse (unpath path) useWithMeta
      add EmptyPath nt usePath nr
  where
    add :: Path -> NameTable -> Meta UseModule -> NR a -> NR a
    add path nt use nr = do
      names <- ask
      case unmeta use of
        UseAny -> do
          id <- uniqueId file $ metaSpan use
          let
            finalNames' =
              foldr (addName id path) (finalNames names) $ nameTableToList nt
            names' = names { finalNames = finalNames' }
          withNames names' nr
        UseModule Meta { unmeta = name, metaSpan } (UseDot rest) ->
          case nameTableEntry name nt of
            Just item@Item { itemSub = Just sub } -> do
              let
                otherNames' = addName () path (name, item) $ otherNames names
                names' = names { otherNames = otherNames' }
              withNames names' $ add (path .|. name) sub rest nr
            _ -> do
              lift $ lift $ addError CompileError
                { errorFile = Just file
                , errorSpan = metaSpan
                , errorKind = Error
                , errorMessage = "`" ++ show path ++ "` does not contain a module named `" ++ show name ++ "`" }
              nr
        UseModule Meta { unmeta = name, metaSpan } (UseAll rest) ->
          case nameTableEntry name nt of
            Just item -> do
              id <-
                if null rest then
                  uniqueId file metaSpan
                else
                  return hiddenImport
              let
                finalNames' = addName id path (name, item) $ finalNames names
                names' = names { finalNames = finalNames' }
              withNames names' $ case rest of
                [] -> nr
                _ ->
                  let subPath = path .|. name in
                  case item of
                    Item { itemSub = Just sub } ->
                      foldr (add subPath sub) nr rest
                    _ -> do
                      lift $ lift $ addError CompileError
                        { errorFile = Just file
                        , errorSpan = metaSpan
                        , errorKind = Error
                        , errorMessage = "cannot import items from `" ++ show subPath ++ "` because it is not a module" }
                      nr
            Nothing -> do
              lift $ lift $ addError CompileError
                { errorFile = Just file
                , errorSpan = metaSpan
                , errorKind = Error
                , errorMessage = "`" ++ show path ++ "` does not contain any items named `" ++ show name ++ "`" }
              nr

insertData :: Meta Path -> InFile DataDecl -> NR ()
insertData path decl = do
  s <- get
  let
    decls = allDecls s
    datas = allDatas decls
  case Map.lookupIndex path datas of
    Just i ->
      lift $ lift $ addError CompileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          let
            baseMessage = "duplicate data type declaration for path `" ++ show path ++ "`\n"
            (otherPath, otherFile :/: _) = Map.elemAt i datas
          in case metaSpan otherPath of
            Just otherSpan ->
              baseMessage ++ "(other at " ++ otherFile ++ ":" ++ show otherSpan ++ ")"
            Nothing ->
              baseMessage ++ "(other in " ++ otherFile ++ ")" }
    Nothing ->
      put s
        { allDecls = decls
          { allDatas = Map.insert path decl datas } }

insertLet :: Meta Path -> InFile LetDecl -> NR ()
insertLet path decl = do
  s <- get
  let
    decls = allDecls s
    lets = allLets decls
  case Map.lookupIndex path lets of
    Just i ->
      lift $ lift $ addError CompileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          let
            baseMessage = "duplicate let binding for path `" ++ show path ++ "`\n"
            (otherPath, otherFile :/: _) = Map.elemAt i lets
          in case metaSpan otherPath of
            Just otherSpan ->
              baseMessage ++ "(other at " ++ otherFile ++ ":" ++ show otherSpan ++ ")"
            Nothing ->
              baseMessage ++ "(other in " ++ otherFile ++ ")" }
    Nothing ->
      put s
        { allDecls = decls
          { allLets = Map.insert path decl lets } }

insertOpType :: Meta Path -> InFile OpTypeEnds -> NR ()
insertOpType path newOp = do
  s <- get
  let
    decls = allDecls s
    ops = allOpTypes decls
  case Map.lookupIndex path ops of
    Just i ->
      lift $ lift $ addError CompileError
        { errorFile = Just $ getFile newOp
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          let
            baseMessage = "duplicate operator type declaration for path `" ++ show path ++ "`\n"
            (otherPath, otherFile :/: _) = Map.elemAt i ops
          in case metaSpan otherPath of
            Just otherSpan ->
              baseMessage ++ "(other at " ++ otherFile ++ ":" ++ show otherSpan ++ ")"
            Nothing ->
              baseMessage ++ "(other in " ++ otherFile ++ ")" }
    Nothing ->
      put s
        { allDecls = decls
          { allOpTypes = Map.insert path newOp ops } }

insertOpDecl :: Meta Path -> InFile OpDecl -> NR ()
insertOpDecl path decl = do
  s <- get
  let
    decls = allDecls s
    ops = allOpDecls decls
  case Map.lookupIndex path ops of
    Just i ->
      lift $ lift $ addError CompileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          let
            baseMessage = "duplicate operator declaration for path `" ++ show path ++ "`\n"
            (otherPath, otherFile :/: _) = Map.elemAt i ops
          in case metaSpan otherPath of
            Just otherSpan ->
              baseMessage ++ "(other at " ++ otherFile ++ ":" ++ show otherSpan ++ ")"
            Nothing ->
              baseMessage ++ "(other in " ++ otherFile ++ ")" }
    Nothing ->
      put s
        { allDecls = decls
          { allOpDecls = Map.insert path decl ops } }

nameResolve :: [Module] -> CompileIO AllDecls
nameResolve mods = do
  baseModule <- gets (compilePackageName . compileOptions)
  let
    nr = nameResolveAll (Local baseModule) mods
    nrState = runReaderT nr defaultNames
    nameTable = toNameTable $ Map.singleton baseModule mods
  fmap allDecls $ execStateT nrState $ defaultNameState nameTable

nameResolveAll :: Path -> [Module] -> NR ()
nameResolveAll path mods = do
  forM_ mods $ nameResolveEach path
  unusedIds <- gets unusedIds
  forM_ (Map.elems unusedIds) $ \(file :/: span) ->
    lift $ lift $ addError CompileError
      { errorFile = Just file
      , errorSpan = Just span
      , errorKind = Warning
      , errorMessage = "unused import in `use` statement" }

nameResolveEach :: Path -> Module -> NR ()
nameResolveEach path mod =
  addUse path (Generated :/: meta UseAny) $
    foldl' (flip (addUse path)) go (modUses mod)
  where
    go = do
      forM_ (Map.toList $ modSubs mod) $ \(name, mods) ->
        forM_ mods $ nameResolveEach (path .|. name)
      mapM_ nameResolveOpType $ modOpTypes mod
      mapM_ nameResolveOpDecl $ Map.toList $ modOpDecls mod
      mapM_ nameResolveData $ Map.toList $ modDatas mod
      mapM_ nameResolveLet $ Map.toList $ modLets mod

    nameResolveOpType (file :/: ops) =
      case ops of
        OpLink path : [] ->
          lift $ lift $ addError CompileError
            { errorFile = Just file
            , errorSpan = metaSpan path
            , errorKind = Warning
            , errorMessage =
              "useless operator type declaration" ++
              case unpath $ unmeta path of
                [name] -> "\n(did you mean `operator type " ++ show name ++ "`?)"
                _ -> "" }
        OpLink path : rest -> do
          resolvedPath <- resMetaPath path
          afterLink (Just resolvedPath) rest
        other ->
          afterDeclare Nothing other
      where
        resPath = nameResolvePath file isOperatorType "an operator type"
        resMetaPath path = forM path $ resPath $ metaSpan path

        afterLink lower = \case
          OpDeclare name : rest -> do
            next <- getNext rest
            insertOpType ((path .|.) <$> name) (file :/: (lower, next))
            afterDeclare lower rest
          OpLink path : _ ->
            lift $ lift $ addError CompileError
              { errorFile = Just file
              , errorSpan = metaSpan path
              , errorKind = Error
              , errorMessage =
                "expected operator type declaration after link" ++
                case unpath $ unmeta path of
                  [name] -> "\n(did you mean `" ++ show name ++ "`, without parentheses?)"
                  _ -> "" }
          [] -> return ()

        afterDeclare lower = \case
          OpDeclare name : rest -> do
            next <- getNext rest
            insertOpType ((path .|.) <$> name) (file :/: (lower, next))
            afterDeclare lower rest
          OpLink path : rest -> do
            resolvedPath <- resMetaPath path
            afterLink (Just resolvedPath) rest
          [] -> return ()

        getNext = \case
          [] ->
            return Nothing
          (OpDeclare name : _) ->
            return $ Just ((path .|.) <$> name)
          (OpLink path : _) ->
            Just <$> resMetaPath path

    nameResolveOpDecl (name, file :/: decl) = do
      opType' <- resMetaPath $ opType decl
      let
        decl' = decl { opType = opType' }
        opPath = (path .|.) <$> name
      -- check that something that can be used as an operator exists at the path
      _ <- nameResolvePath file isInfixable "an operator" (metaSpan opPath) (unmeta opPath)
      insertOpDecl opPath (file :/: decl')
      where
        resPath = nameResolvePath file isOperatorType "an operator type"
        resMetaPath path = forM path $ resPath $ metaSpan path

    nameResolveData (name, file :/: decl) = do
      variants <- mapM (mapM nameResolveVariant) $ dataVariants decl
      let dataName = (path .|.) <$> name
      insertData dataName $ file :/: decl
        { dataVariants = variants }
      forM variants $ \var ->
        let
          (name, types) = unmeta var
          constructorPath
            | dataMod decl = unmeta dataName
            | otherwise = path
        in
          insertLet ((constructorPath .|.) <$> name) $ file :/: LetDecl
            { letBody =
              copySpan var $
                if null types then
                  EValue $ VDataCons (unmeta dataName) (unmeta name) []
                else
                  let count = length types in
                  EValue $ VFun [
                    ( replicate count $ meta $ PBind Nothing
                    , copySpan var $ EDataCons (unmeta dataName) (unmeta name) $
                      [0 .. count-1] <&> \n -> meta $ EIndex n Nothing )] }
      where
        nameResolveVariant (name, types) =
          (,) name <$> mapM (nameResolveType file) types

    nameResolveLet (name, file :/: decl) = do
      body <- nameResolveExpr path file $ letBody decl
      insertLet ((path .|.) <$> name) $ file :/: decl
        { letBody = body }

nameResolvePath :: FilePath -> (Item -> Bool) -> String -> Maybe Span -> Path -> NR Path
nameResolvePath file check kind span path@(Path parts@(head:rest)) = do
  nt <- gets nameTable
  case nameTableEntry head nt of
    Just item ->
      checkRec EmptyPath item $ return path
    Nothing -> do
      Names { finalNames, otherNames } <- ask
      case Map.lookup head finalNames of
        Just (Right (path, item, id)) ->
          checkRec path item $ do
            clearId id
            return $ Path (unpath path ++ parts)
        Just (Left paths) ->
          oneOfMany paths
        Nothing ->
          if null rest then
            notFound
          else
            case Map.lookup head otherNames of
              Just (Right (path, item, ())) ->
                checkRec path item $
                  return $ Path (unpath path ++ parts)
              Just (Left paths) ->
                oneOfMany paths
              Nothing ->
                notFound
  where
    checkRec basePath item ifRight =
      go (basePath .|. head) rest item
      where
        go _ [] item
          | check item = ifRight
          | otherwise  = wrongKind path kind
        go path (n:ns) item =
          let subPath = path .|. n in
          case itemSub item of
            Just sub ->
              case nameTableEntry n sub of
                Just item' ->
                  go subPath ns item'
                Nothing ->
                  let
                    subKind = case ns of
                      [] -> kind
                      _ -> "a module"
                  in pathErr $
                    "`" ++ show path ++ "` does not contain " ++ subKind ++ " named `" ++ show n ++ "`"
            Nothing ->
              wrongKind subPath "a module"

    clearId id =
      modify $ \s -> s
        { unusedIds = Map.delete id $ unusedIds s }

    pathErr msg = do
      lift $ lift $ addError CompileError
        { errorFile = Just file
        , errorSpan = span
        , errorKind = Error
        , errorMessage = msg }
      return EmptyPath

    oneOfMany paths = pathErr $
      "`" ++ show path ++ "` could refer to any one of the following:\n"
      ++ intercalate "\n" (map showExt $ Set.toList paths)
      where
        showExt (Path start) = show $ Path (start ++ parts)

    wrongKind path kind = pathErr $
      "`" ++ show path ++ "` is not " ++ kind

    notFound = pathErr $
      "cannot find `" ++ show path ++ "` in scope, did you forget to `use` it?"

nameResolveType :: FilePath -> Meta Type -> NR (Meta Type)
nameResolveType file = go
  where
    go ty =
      forM ty $ \case
        TNamed path ->
          TNamed <$> resPath (metaSpan ty) path
        TParen ty ->
          TParen <$> go ty
        TUnaryOp op ty ->
          TUnaryOp <$> resMetaPath op <*> go ty
        TBinOp op a b ->
          TBinOp <$> resMetaPath op <*> go a <*> go b
        TApp a b ->
          TApp <$> go a <*> go b
        other ->
          return other
      where
        resPath = nameResolvePath file isType "a type"
        resMetaPath path = forM path $ resPath $ metaSpan path

nameResolveExpr :: Path -> FilePath -> Meta Expr -> NR (Meta Expr)
nameResolveExpr path file = go
  where
    go expr =
      forM expr $ \case
        EValue (VFun cases) ->
          EValue . VFun <$> nameResolveCases cases
        EGlobal path ->
          EGlobal <$> resPath (metaSpan expr) path
        EParen expr ->
          EParen <$> go expr
        EUnaryOp op expr ->
          EUnaryOp <$> resMetaPath op <*> go expr
        EBinOp op a b ->
          EBinOp <$> resMetaPath op <*> go a <*> go b
        EApp a b ->
          EApp <$> go a <*> go b
        ESeq a b ->
          ESeq <$> go a <*> go b
        ELet pat val expr ->
          ELet <$> nameResolvePat path file pat <*> go val <*> go expr
        EMatchIn exprs cases ->
          EMatchIn <$> mapM go exprs <*> nameResolveCases cases
        EUse use expr ->
          addUse path (file :/: use) $ unmeta <$> go expr
        ETypeAscribe expr ty ->
          ETypeAscribe <$> go expr <*> nameResolveType file ty
        other ->
          return other
      where
        resPath = nameResolvePath file isValue "a value"
        resMetaPath path = forM path $ resPath $ metaSpan path
        nameResolveCases cases =
          forM cases $ \(pats, expr) ->
            (,) <$> mapM (nameResolvePat path file) pats <*> go expr

nameResolvePat :: Path -> FilePath -> Meta Pattern -> NR (Meta Pattern)
nameResolvePat path file = go
  where
    go pat =
      forM pat $ \case
        PParen pat ->
          PParen <$> go pat
        PUnaryOp op pat ->
          PUnaryOp <$> resMetaPath op <*> go pat
        PBinOp op a b ->
          PBinOp <$> resMetaPath op <*> go a <*> go b
        PCons path pats ->
          PCons <$> resMetaPath path <*> mapM go pats
        PTypeAscribe pat ty ->
          PTypeAscribe <$> go pat <*> nameResolveType file ty
        other ->
          return other
      where
        resPath = nameResolvePath file isPattern "a pattern"
        resMetaPath path = forM path $ resPath $ metaSpan path
