-- | Replaces all partial paths with the full path of the object to which they refer
module Analyze.NameResolve where

import Utility

import Data.List
import Data.Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.Reader
import Control.Monad.State.Strict

-- | 'ReaderT' for name resolution containing all names in scope and other state information
type NR = ReaderT Names (StateT NameState CompileIO)

-- | A type representing whether an import was explicitly listed or imported by an underscore
data Explicitness
  = Implicit
  | Explicit
  deriving Show

-- | A map of names in scope to the specific item they refer to, or to a set of ambiguous paths
type NameSet mark = Map Name (Either (Set Path) (Path, Item, Explicitness, mark))

-- | Records the names visible in the current scope
data Names = Names
  { -- | Names that were directly imported as the final name in a dot-separated path
    finalNames :: NameSet ImportId
    -- | Other names that can only be used as modules and take lower precedence for resolution
  , otherNames :: NameSet () }
  deriving Show

-- | A scope with no names present
defaultNames :: Names
defaultNames = Names
  { finalNames = Map.empty
  , otherNames = Map.empty }

-- | Adds a name associated with an item to a 'NameSet'
addName :: Explicitness -> mark -> Path -> (Name, Item) -> NameSet mark -> NameSet mark
addName exp id path (name, item) s =
  if Map.member name s then
    Map.adjust collide name s
  else
    Map.insert name new s
  where
    new = Right (path, item, exp, id)
    collide old =
      case old of
        Left paths
          | path `elem` paths -> Left paths
          | otherwise         -> Left $ Set.insert path paths
        Right (oldPath, oldItem, oldExp, _) ->
          if path == oldPath && item == oldItem then
            -- The only time a new import should take precedence over an older one is if the new one is implicit and
            -- the old one was explicit. This helps minimize the complexity of import statements.
            case (exp, oldExp) of
              (Implicit, Explicit) -> new
              _ -> old
          else
            Left $ Set.insert path $ Set.singleton oldPath

-- | Updates the names present in a scope
withNames :: Names -> NR a -> NR a
withNames names nr = lift $ runReaderT nr names

-- | An item is anything that has a name
data Item = Item
  { itemSub :: Maybe NameTable
  , isType :: Bool
  , isValue :: Bool
  , isEffect :: Bool
  , isPattern :: Bool
  , isOperatorType :: Bool }
  deriving (Show, Ord, Eq)

instance Semigroup Item where
  a <> b = Item
    { itemSub = itemSub a <> itemSub b
    , isType = isType a || isType b
    , isValue = isValue a || isValue b
    , isEffect = isEffect a || isEffect b
    , isPattern = isPattern a || isPattern b
    , isOperatorType = isOperatorType a || isOperatorType b }

instance Monoid Item where
  mempty = Item
    { itemSub = Nothing
    , isType = False
    , isValue = False
    , isEffect = False
    , isPattern = False
    , isOperatorType = False }
  mappend = (<>)

-- | An item is infixable if it is in a namespace that can be used in infix position (types, values, and patterns)
isInfixable :: Item -> Bool
isInfixable item =
  isType item
  || isValue item
  || isPattern item

-- | Checks if an item is a 'Module'
modItem :: NameTable -> Item
modItem nt = mempty
  { itemSub = Just nt }

-- | Checks if an item is a 'Type'
typeItem :: Item
typeItem = mempty
  { isType = True }

-- | Checks if an item is a value ('Expr')
valueItem :: Item
valueItem = mempty
  { isValue = True }

-- | Checks if an item is an 'Effect'
effectItem :: Item
effectItem = mempty
  { isEffect = True }

-- | Checks if an item is a 'Pattern'
patternItem :: Item
patternItem = mempty
  { isPattern = True }

-- | Checks if an item is an operator type
operatorTypeItem :: Item
operatorTypeItem = mempty
  { isOperatorType = True }

-- | Returns an item that can be used for anything but a module
anyItem :: Item
anyItem = Item
  { itemSub = Nothing
  , isType = True
  , isValue = True
  , isEffect = True
  , isPattern = True
  , isOperatorType = True }

-- | A mapping from names to items
newtype NameTable = NameTable
  { getNameTable :: Map Name Item }
  deriving (Show, Ord, Eq)

instance Semigroup NameTable where
  NameTable a <> NameTable b =
    NameTable $ Map.unionWith (<>) a b

instance Monoid NameTable where
  mempty = NameTable Map.empty
  mappend = (<>)

-- | The 'NameTable' for the Core package with intrinsic items
coreNameTable :: NameTable
coreNameTable = NameTable
  { getNameTable = Map.fromList
    [ (Identifier "Core", modItem $ NameTable $ Map.fromList
      [ (Operator "->", typeItem)
      , (Identifier "Pure", effectItem) ]) ] }

-- | The 'UseModule' to be used to import common items from Core
coreUse :: UseModule
coreUse =
  UseModule (meta $ Identifier "Core") $ UseAll [meta UseAny]

-- | Converts a set of named modules to a 'NameTable'
toNameTable :: Map Name [Module] -> NameTable
toNameTable =
  NameTable . fmap (modItem . foldr addModule mempty)

-- | Adds a new module to the 'NameTable'
addModule :: Module -> NameTable -> NameTable
addModule mod nt = nt
  <> toNameTable (modSubs mod)
  <> foldMap opTypeItem (modOpTypes mod)
  <> convert typeItem (modDatas mod)
  <> convert valueItem (modLets mod)
  <> convert effectItem (modEffects mod)
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

-- | Converts a 'NameTable' to a list of named items
nameTableToList :: NameTable -> [(Name, Item)]
nameTableToList = Map.toList . getNameTable

-- | Tries to get an item from a 'NameTable'
nameTableEntry :: Name -> NameTable -> Maybe Item
nameTableEntry name = Map.lookup name . getNameTable

-- | Checks if a given item is a member of a 'NameTable'
nameTableMember :: Name -> NameTable -> Bool
nameTableMember name = Map.member name . getNameTable

-- | A unique identifier for parts of a use declaration
type ImportId = Int

-- | An 'ImportId' that is untracked
hiddenImport :: ImportId
hiddenImport = -1

-- | State information that is kept while resolving declarations
data NameState = NameState
  { -- | Contains all resolved declarations
    allDecls :: AllDecls
    -- | Table with information about every item that may be used
  , nameTable :: NameTable
    -- | Map containing a location for every unused import so warnings can be emitted
  , unusedIds :: IntMap (InFile Span)
    -- | The next unique 'ImportId' that will be given out
  , importId :: ImportId }

-- | Creates a default 'NameState' from a given 'NameTable'
defaultNameState :: NameTable -> NameState
defaultNameState nameTable = NameState
  { allDecls = emptyDecls
  , nameTable
  , unusedIds = IntMap.empty
  , importId = 0 }

-- | Gets a unique identifier for an import and tracks its use
uniqueId :: FilePath -> Maybe Span -> NR ImportId
uniqueId file maybeSpan =
  case maybeSpan of
    Nothing ->
      return hiddenImport
    Just span -> do
      s <- get
      let id = importId s
      put s
        { unusedIds = IntMap.insert id (file :/: span) $ unusedIds s
        , importId = id + 1 }
      return id

-- | Prefix a use declaration with a given path
prefixUse :: [Name] -> Meta UseModule -> Meta UseModule
prefixUse []     use = use
prefixUse (n:ns) use =
  meta $ UseModule (meta n) $ UseDot $ prefixUse ns use

-- | Add all requested items into the scope for a sub-expression
addUse :: Path -> InFile (Meta UseModule) -> NR a -> NR a
addUse path (file :/: useWithMeta) nr =
  case useWithMeta of
    Meta { unmeta = UseAny, metaSpan = Just span } -> do
      -- The span is required here because the automatic `use _` doesn't have a span
      -- and we only want to catch imports made by the programmer
      addError CompileError
        { errorFile = Just file
        , errorSpan = Just span
        , errorKind = Warning
        , errorMessage = "`use _` does nothing since top level names are imported automatically" }
      nr
    Meta { unmeta = use, metaSpan } -> do
      case use of
        UseModule name (UseAll []) ->
          addError CompileError
            { errorFile = Just file
            , errorSpan = metaSpan
            , errorKind = Warning
            , errorMessage = "`use " ++ show name ++ "` cannot bring anything into scope" }
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
    isGenerated = file == Generated

    add :: Path -> NameTable -> Meta UseModule -> NR a -> NR a
    add path nt use nr = do
      names <- ask
      case unmeta use of
        UseAny -> do
          id <- uniqueId file $ metaSpan use
          let
            allowedImport (Underscore _, _) = isGenerated
            allowedImport _ = True
            finalNames' =
              foldr (addName Implicit id path) (finalNames names) $ filter allowedImport $ nameTableToList nt
            names' = names { finalNames = finalNames' }
          withNames names' nr
        UseModule Meta { unmeta = name, metaSpan } (UseDot rest) ->
          case nameTableEntry name nt of
            Just item@Item { itemSub = Just sub } ->
              let
                otherNames' = addName Explicit () path (name, item) $ otherNames names
                names' = names { otherNames = otherNames' }
              in
                withNames names' $ add (path .|. name) sub rest nr
            _ -> do
              addError CompileError
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
                finalNames' = addName Explicit id path (name, item) $ finalNames names
                names' = names { finalNames = finalNames' }
              withNames names' $ case rest of
                [] -> nr
                _ ->
                  let subPath = path .|. name in
                  case item of
                    Item { itemSub = Just sub } ->
                      foldr (add subPath sub) nr rest
                    _ -> do
                      addError CompileError
                        { errorFile = Just file
                        , errorSpan = metaSpan
                        , errorKind = Error
                        , errorMessage =
                          "cannot import items from `" ++ show subPath ++ "` because it is not a module" }
                      nr
            Nothing -> do
              addError CompileError
                { errorFile = Just file
                , errorSpan = metaSpan
                , errorKind = Error
                , errorMessage = "`" ++ show path ++ "` does not contain any items named `" ++ show name ++ "`" }
              -- Add a dummy item as if it did exist to suppress further errors
              withNames names { finalNames = addName Explicit hiddenImport path (name, anyItem) $ finalNames names } nr

-- | Create a message saying where a duplicate definition can be found
duplicateMessage :: (Meta Path, InFile a) -> String -> String
duplicateMessage (otherPath, otherFile :/: _) baseMessage =
  case metaSpan otherPath of
    Just otherSpan ->
      baseMessage ++ "(other at " ++ otherFile ++ ":" ++ show otherSpan ++ ")"
    Nothing ->
      baseMessage ++ "(other in " ++ otherFile ++ ")"

-- | Resolve an 'EffectDecl'
insertEffect :: Meta Path -> InFile EffectDecl -> NR ()
insertEffect path decl = do
  s <- get
  let
    decls = allDecls s
    effects = allEffects decls
  case Map.lookupIndex path effects of
    Just i ->
      addError CompileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          duplicateMessage (Map.elemAt i effects)
            ("duplicate effect declaration for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allEffects = Map.insert path decl effects } }

-- | Resolve a 'DataDecl'
insertData :: Meta Path -> InFile DataDecl -> NR ()
insertData path decl = do
  s <- get
  let
    decls = allDecls s
    datas = allDatas decls
  case Map.lookupIndex path datas of
    Just i ->
      addError CompileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          duplicateMessage (Map.elemAt i datas)
            ("duplicate data type declaration for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allDatas = Map.insert path decl datas } }

-- | Resolve a @LetDecl@
insertLet :: Meta Path -> InFile LetDecl -> NR ()
insertLet path decl = do
  s <- get
  let
    decls = allDecls s
    lets = allLets decls
  case Map.lookupIndex path lets of
    Just i ->
      addError CompileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          duplicateMessage (Map.elemAt i lets)
            ("duplicate let binding for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allLets = Map.insert path decl lets } }

-- | Resolve an operator type declaration
insertOpType :: Meta Path -> InFile OpTypeEnds -> NR ()
insertOpType path newOp = do
  s <- get
  let
    decls = allDecls s
    ops = allOpTypes decls
  case Map.lookupIndex path ops of
    Just i ->
      addError CompileError
        { errorFile = Just $ getFile newOp
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          duplicateMessage (Map.elemAt i ops)
            ("duplicate operator type declaration for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allOpTypes = Map.insert path newOp ops } }

-- | Resolve an 'OpDecl'
insertOpDecl :: Meta Path -> InFile OpDecl -> NR ()
insertOpDecl path decl = do
  s <- get
  let
    decls = allDecls s
    ops = allOpDecls decls
  case Map.lookupIndex path ops of
    Just i ->
      addError CompileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorKind = Error
        , errorMessage =
          duplicateMessage (Map.elemAt i ops)
            ("duplicate operator declaration for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allOpDecls = Map.insert path decl ops } }

-- | Resolve all names in a set of modules and return a flattened map of declarations
nameResolve :: [Module] -> CompileIO AllDecls
nameResolve mods = do
  baseModule <- gets (compilePackageName . compileOptions)
  let
    nr = nameResolveAll (Local baseModule) mods
    nrState = runReaderT nr defaultNames
    nameTable = coreNameTable <> (toNameTable $ Map.singleton baseModule mods)
  fmap allDecls $ execStateT nrState $ defaultNameState nameTable

-- | Resolve a set of modules
nameResolveAll :: Path -> [Module] -> NR ()
nameResolveAll path mods = do
  forM_ mods $ nameResolveEach path
  unusedIds <- gets unusedIds
  forM_ (IntMap.elems unusedIds) \(file :/: span) ->
    addError CompileError
      { errorFile = Just file
      , errorSpan = Just span
      , errorKind = Warning
      , errorMessage = "unused import in `use` statement" }

-- | Resolve a single 'Module'
nameResolveEach :: Path -> Module -> NR ()
nameResolveEach path mod =
  addUse path (Generated :/: meta UseAny)
    $ addUse path (Generated :/: meta coreUse)
    $ foldl' (flip (addUse path)) go (modUses mod)
  where
    go = do
      forM_ (Map.toList $ modSubs mod) \(name, mods) ->
        forM_ mods $ nameResolveEach (path .|. name)
      mapM_ nameResolveOpType $ modOpTypes mod
      mapM_ nameResolveOpDecl $ Map.toList $ modOpDecls mod
      mapM_ nameResolveEffect $ Map.toList $ modEffects mod
      mapM_ nameResolveData $ Map.toList $ modDatas mod
      mapM_ nameResolveLet $ Map.toList $ modLets mod

    nameResolveOpType (file :/: ops) =
      case ops of
        OpLink path : [] ->
          addError CompileError
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
        resPath = nameResolvePath file isOperatorType "operator type"
        resMetaPath path = forM path $ resPath $ metaSpan path

        afterLink lower = \case
          OpDeclare name : rest -> do
            next <- getNext rest
            insertOpType ((path .|.) <$> name) (file :/: (lower, next))
            afterDeclare lower rest
          OpLink path : _ ->
            addError CompileError
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
      -- Check that something that can be used as an operator exists at the path
      _ <- nameResolvePath file isInfixable "operator" (metaSpan opPath) (unmeta opPath)
      insertOpDecl opPath (file :/: decl')
      where
        resPath = nameResolvePath file isOperatorType "operator type"
        resMetaPath path = forM path $ resPath $ metaSpan path

    nameResolveEffect (name, file :/: EffectDecl { effectSuper }) = do
      super <-
        case effectSuper of
          Nothing ->
            return Nothing
          Just effect ->
            Just <$> (forM effect $ nameResolvePath file isEffect "effect" $ metaSpan effect)
      case super of
        Just Meta { unmeta = Core (Identifier "Pure"), metaSpan } ->
          addError CompileError
            { errorFile = Just file
            , errorSpan = metaSpan
            , errorKind = Error
            , errorMessage = "effect cannot be a subtype of `Pure`, try just using `effect " ++ show name ++ "`" }
        _ -> return ()
      insertEffect ((path .|.) <$> name) $ file :/: EffectDecl
        { effectSuper = super }

    nameResolveData (name, file :/: decl) = do
      variants <- mapM (mapM nameResolveVariant) $ dataVariants decl
      let dataName = (path .|.) <$> name
      insertData dataName $ file :/: decl
        { dataVariants = variants }
      forM variants \var ->
        let
          (name, types) = unmeta var
          constructorPath
            | dataMod decl = unmeta dataName
            | otherwise = path
          variantPath = constructorPath .|. unmeta name
        in
          insertLet (copySpan name variantPath) $ file :/: LetDecl
            { letBody =
              copySpan var $
                if null types then
                  EValue $ VDataCons variantPath []
                else
                  let count = length types in
                  EValue $ VFun [
                    ( replicate count $ meta $ PBind Nothing
                    , copySpan var $ EDataCons variantPath $
                      reverse [0 .. count-1] <&> \n -> meta $ EIndex n Nothing )]
            , letConstraints = [] }
      where
        nameResolveVariant (name, types) =
          (,) name <$> mapM (nameResolveAfter path file) types

    nameResolveLet (name, file :/: decl) = do
      body <- nameResolveAfter path file $ letBody decl
      insertLet ((path .|.) <$> name) $ file :/: decl
        { letBody = body }

-- | Resolve a single 'Path'
nameResolvePath :: FilePath -> (Item -> Bool) -> String -> Maybe Span -> Path -> NR Path
nameResolvePath file check kind span path@(Path parts@(head:rest)) = do
  nt <- gets nameTable
  case nameTableEntry head nt of
    Just item ->
      checkRec EmptyPath item $ return path
    Nothing -> do
      Names { finalNames, otherNames } <- ask
      case Map.lookup head finalNames of
        Just (Right (path, item, _, id)) ->
          checkRec path item do
            clearId id
            return $ Path (unpath path ++ parts)
        Just (Left paths) ->
          oneOfMany paths
        Nothing ->
          if null rest then
            notFound
          else
            case Map.lookup head otherNames of
              Just (Right (path, item, _, ())) ->
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
                      _ -> "module"
                  in pathErr $
                    "`" ++ show path ++ "` does not contain " ++ aOrAn subKind ++ " named `" ++ show n ++ "`"
            Nothing ->
              wrongKind subPath "module"

    clearId id =
      modify \s -> s
        { unusedIds = IntMap.delete id $ unusedIds s }

    pathErr msg = do
      addError CompileError
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
      "`" ++ show path ++ "` is not " ++ aOrAn kind

    notFound = pathErr $
      "cannot find `" ++ show path ++ "` in scope, did you forget to " ++
        case head of
          Underscore _ ->
            "define it or explicitly `use` it?\n"
            ++ "(private items starting with '_' must be explicitly imported from other modules)"
          _ ->
            "`use` it?"

-- | Resolve any kind of expression
nameResolveAfter :: After a => Path -> FilePath -> Meta a -> NR (Meta a)
nameResolveAfter basePath file = after aDefault
  { aUseExpr = handleUseExpr
  , aPath = updatePath }
  where
    handleUseExpr m use expr =
      addUse basePath (file :/: use) $ unmeta <$> after m expr

    updatePath k path = nameResolvePath file kIs (show k) (metaSpan path) (unmeta path)
      where
        kIs =
          case k of
            KValue   -> isValue
            KPattern -> isPattern
            KType    -> isType
            KEffect  -> isEffect

