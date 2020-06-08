-- | Replaces all partial paths with the full path of the object to which they refer
module Analyze.NameResolve where

import Utility

import Data.Char
import Data.List
import Data.Foldable
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Set (Set)
import qualified Data.Set as Set

import Text.EditDistance

import Control.Monad.Reader
import Control.Monad.State.Strict

-- | 'ReaderT' for name resolution containing all names in scope and other state information
type NR = ReaderT Names (StateT NameState CompileIO)

-- | A type representing whether an import was explicitly listed or imported by an underscore
data Explicitness
  = Implicit
  | Explicit

-- | A map of names in scope to the specific item they refer to, or to a set of ambiguous paths
type NameSet mark = Map Name (Either (Set Path) (Path, Item, Explicitness, mark))

-- | A unique identifier for parts of a use declaration
type ImportId = Int

-- | A class for possible marks for an import
class Eq mark => ImportMark mark where
  -- | An 'ImportId' that is untracked
  hiddenImport :: mark

instance ImportMark () where
  hiddenImport = ()

instance ImportMark ImportId where
  hiddenImport = -1

-- | Records the names visible in the current scope
data Names = Names
  { -- | Names that were directly imported as the final name in a dot-separated path
    finalNames :: NameSet ImportId
    -- | Other names that can only be used as modules and take lower precedence for resolution
  , otherNames :: NameSet ()
    -- | Local identifiers bound by patterns or as parameters for a data type
  , localNames :: Set String}

-- | A scope with no names present
defaultNames :: Names
defaultNames = Names
  { finalNames = Map.empty
  , otherNames = Map.empty
  , localNames = Set.empty }

-- | Adds a name associated with an item to a 'NameSet'
addName :: ImportMark mark => Explicitness -> mark -> Path -> (Name, Item) -> NameSet mark -> NameSet mark
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
        Right (oldPath, _, oldExp, oldId) ->
          -- It isn't necessary to compare the items if they have the same absolute path
          if path == oldPath then
            -- If one of the imports is hidden but not the other one, prefer the one that is hidden so that
            -- non-hidden imports will emit the unused import warnings that are silenced by the hidden ones.
            case (id == hiddenImport, oldId == hiddenImport) of
              (True, False) -> new
              (False, True) -> old
              _ ->
                -- The only time a new import should take precedence over an older one is if the new one is
                -- implicit and the old one was explicit. This helps minimize the complexity of import statements.
                case (exp, oldExp) of
                  (Implicit, Explicit) -> new
                  _ -> old
          else
            Left $ Set.insert path $ Set.singleton oldPath

-- | Updates the names present in a scope
withNames :: Names -> NR a -> NR a
withNames names nr = lift $ runReaderT nr names

-- | Adds a set of local variables in a scope
withLocals :: [String] -> NR a -> NR a
withLocals locals nr = do
  names <- ask
  withNames (names { localNames = foldr Set.insert (localNames names) locals }) nr

-- | An item is anything that has a name
data Item = Item
  { itemSub :: Maybe NameTable
  , isType :: Bool
  , isValue :: Bool
  , isEffect :: Bool
  , isPattern :: Bool
  , isOperatorType :: Bool }

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
    [ ( Identifier "Core"
      , modItem $ addModule coreModule $ NameTable $ Map.fromList
        [ -- The (->) function arrow
          (Operator "->", typeItem)
          -- The (unary ^) dereferencing operator
        , (Unary "^", valueItem <> patternItem)
          -- The (:=) reference assignment operator
        , (Operator ":=", valueItem)
          -- The (<-) reference update operator
        , (Operator "<-", valueItem) ] ) ] }

-- | Definitions for certain items in the Core package which have trivial implementations
coreModule :: Module
coreModule = defaultModule
  { -- operator type Assignment < Dereference
    modOpTypes = [Generated :/:
    [ OpDeclare $ meta assignment
    , OpDeclare $ meta dereference ]]
    -- operator (:=) (<-) : Assignment
    -- operator (unary ^) : Dereference
  , modOpDecls = Map.fromList
    [ (meta $ Operator ":=", assignmentDecl)
    , (meta $ Operator "<-", assignmentDecl)
    , (meta $ Unary "^", dereferenceDecl) ]
    -- effect Pure
  , modEffects = Map.fromList
    [ (meta $ Identifier "Pure", Generated :/: EffectDecl
      { effectSuper = [] }) ] }
  where
    assignment = Identifier "Assignment"
    dereference = Identifier "Dereference"

    assignmentDecl = Generated :/: OpDecl
      { opAssoc = ANon
      , opType = meta $ Core assignment }
    dereferenceDecl = Generated :/: OpDecl
      { opAssoc = ANon
      , opType = meta $ Core dereference }

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
      addError compileError
        { errorFile = Just file
        , errorSpan = Just span
        , errorKind = Warning
        , errorMessage = "`use _` does nothing since top level names are imported automatically" }
      nr
    Meta { unmeta = use, metaSpan } -> do
      case use of
        UseModule name (UseAll []) ->
          addError compileError
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
              addError compileError
                { errorFile = Just file
                , errorSpan = metaSpan
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
                      addError compileError
                        { errorFile = Just file
                        , errorSpan = metaSpan
                        , errorMessage =
                          "cannot import items from `" ++ show subPath ++ "` because it is not a module" }
                      nr
            Nothing -> do
              addError compileError
                { errorFile = Just file
                , errorSpan = metaSpan
                , errorMessage = "`" ++ show path ++ "` does not contain any items named `" ++ show name ++ "`" }
              -- Add a dummy item as if it did exist to suppress further errors
              withNames names { finalNames = addName Explicit hiddenImport path (name, anyItem) $ finalNames names } nr

-- | Create a message saying where a duplicate definition can be found
duplicateMessage :: (Maybe Span, InFile a) -> String -> String
duplicateMessage (metaSpan, otherFile :/: _) baseMessage =
  case metaSpan of
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
  case pathMapLookup' (unmeta path) effects of
    Just oldEntry ->
      addError compileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorMessage =
          duplicateMessage oldEntry
            ("duplicate effect declaration for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allEffects = pathMapInsert path decl effects } }

-- | Resolve a 'DataDecl'
insertData :: Meta Path -> InFile DataDecl -> NR ()
insertData path decl = do
  s <- get
  let
    decls = allDecls s
    datas = allDatas decls
  case pathMapLookup' (unmeta path) datas of
    Just oldEntry ->
      addError compileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorMessage =
          duplicateMessage oldEntry
            ("duplicate data type declaration for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allDatas = pathMapInsert path decl datas } }

-- | Resolve a @LetDecl@
insertLet :: Meta Path -> InFile LetDecl -> NR ()
insertLet path decl = do
  s <- get
  let
    decls = allDecls s
    lets = allLets decls
  case pathMapLookup' (unmeta path) lets of
    Just oldEntry ->
      addError compileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorMessage =
          duplicateMessage oldEntry
            ("duplicate let binding for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allLets = pathMapInsert path decl lets } }

-- | Resolve an operator type declaration
insertOpType :: Meta Path -> InFile OpTypeEnds -> NR ()
insertOpType path newOp = do
  s <- get
  let
    decls = allDecls s
    ops = allOpTypes decls
  case pathMapLookup' (unmeta path) ops of
    Just oldEntry ->
      addError compileError
        { errorFile = Just $ getFile newOp
        , errorSpan = metaSpan path
        , errorMessage =
          duplicateMessage oldEntry
            ("duplicate operator type declaration for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allOpTypes = pathMapInsert path newOp ops } }

-- | Resolve an 'OpDecl'
insertOpDecl :: Meta Path -> InFile OpDecl -> NR ()
insertOpDecl path decl = do
  s <- get
  let
    decls = allDecls s
    ops = allOpDecls decls
  case pathMapLookup' (unmeta path) ops of
    Just oldEntry ->
      addError compileError
        { errorFile = Just $ getFile decl
        , errorSpan = metaSpan path
        , errorMessage =
          duplicateMessage oldEntry
            ("duplicate operator declaration for path `" ++ show path ++ "`\n") }
    Nothing ->
      put s
        { allDecls = decls
          { allOpDecls = pathMapInsert path decl ops } }

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
  -- Add the core module's plain declarations
  nameResolveEach (Path [Identifier "Core"]) coreModule
  forM_ mods $ nameResolveEach path
  unusedIds <- gets unusedIds
  forM_ (IntMap.elems unusedIds) \(file :/: span) ->
    addError compileError
      { errorFile = Just file
      , errorSpan = Just span
      , errorKind = Warning
      , errorMessage = "unused import in `use` statement" }

-- | Resolve a single 'Module'
nameResolveEach :: Path -> Module -> NR ()
nameResolveEach path mod =
  foldl' (flip (addUse path)) go (modUses mod)
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
        [OpLink path] ->
          addError compileError
            { errorFile = Just file
            , errorSpan = metaSpan path
            , errorKind = Warning
            , errorExplain = Just $
              " In an operator type delcaration, parentheses have a special meaning; they indicate that" ++
              " you are only listing that operator type to define the relative precedence of the operators" ++
              " around it, rather than declaring a new operator type by that name. Therefore, just having" ++
              " this on its own is useless since you aren't declaring anything new."
            , errorMessage =
              "useless operator type declaration" ++
              case unpath $ unmeta path of
                [name] -> "\n(did you mean `operator type " ++ show name ++ "`?)"
                _ -> "" }
        OpLink path : rest -> do
          resolvedPath <- resMetaPath path
          afterLink resolvedPath rest
        other ->
          afterDeclare Nothing other
      where
        resPath = nameResolvePath file isOperatorType "operator type"
        resMetaPath path = forM path $ resPath $ metaSpan path

        afterLink lower = \case
          OpDeclare name : rest -> do
            next <- getNext rest
            insertOpType ((path .|.) <$> name) (file :/: (Just lower, next))
            afterDeclare (Just lower) rest
          OpLink path : rest -> do
            addError compileError
              { errorFile = Just file
              , errorSpan = metaSpan path
              , errorExplain = Just $
                " An operator type link (which does not declare a new operator type) must be followed by" ++
                " a new operator type to declare, not another link. If you want to specify a new lower" ++
                " precedence item, consider splitting this into a separate operator type declaration instead."
              , errorMessage =
                "expected operator type declaration after link" ++
                case unpath $ unmeta path of
                  [name] -> "\n(did you mean `" ++ show name ++ "`, without parentheses?)"
                  _ -> "" }
            resolvedPath <- resMetaPath path
            afterLink resolvedPath rest
          [] -> return ()

        afterDeclare lower = \case
          OpDeclare name : rest -> do
            next <- getNext rest
            insertOpType ((path .|.) <$> name) (file :/: (lower, next))
            afterDeclare lower rest
          OpLink path : rest -> do
            resolvedPath <- resMetaPath path
            afterLink resolvedPath rest
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
        forM effectSuper \effect ->
          (forM effect $ nameResolvePath file isEffect "effect" $ metaSpan effect)
      case find (\eff -> unmeta eff == Core (Identifier "Pure")) super of
        Just Meta { metaSpan } ->
          addError compileError
            { errorFile = Just file
            , errorSpan = metaSpan
            , errorExplain = Just $
              " Making an effect a subtype of `Pure` is not something that makes sense, since it" ++
              " represents the lack of side effects. If an effect were a subtype of `Pure`, it would" ++
              " be useless since it could always be left out when specifying an effect."
            , errorMessage =
              "effect cannot be a subtype of `Pure`, try just using `effect " ++ show name ++ "`" }
        _ -> return ()
      insertEffect ((path .|.) <$> name) $ file :/: EffectDecl
        { effectSuper = super }

    nameResolveData (name, file :/: decl@DataDecl { dataSig = DataSig { dataEffects, dataArgs } }) = do
      let parameters = map (unmeta . fst) dataEffects ++ map (unmeta . fst) dataArgs
      variants <- withLocals parameters $ mapM (mapM nameResolveVariant) $ dataVariants decl
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
            , letConstraints = []
            , letInferredType = ()
            , letInstanceArgs = [] }
      where
        nameResolveVariant (name, types) =
          (,) name <$> mapM (nameResolveRestrictedType path file) types

    nameResolveLet (name, file :/: decl) = do
      body <- nameResolveAfter path file $ letBody decl
      insertLet ((path .|.) <$> name) $ file :/: decl
        { letBody = body }

-- | Resolve a single 'Path'
nameResolvePath :: FilePath -> (Item -> Bool) -> String -> Maybe Span -> Path -> NR Path
nameResolvePath _ _ _ _ (Path []) =
  compilerBug "nameResolvePath called on empty path"
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
      addError compileError
        { errorFile = Just file
        , errorSpan = span
        , errorMessage = msg }
      return EmptyPath

    oneOfMany paths = pathErr $
      "`" ++ show path ++ "` could refer to any one of the following:\n"
      ++ intercalate "\n" (map showExt $ Set.toList paths)
      where
        showExt (Path start) = show $ Path (start ++ parts)

    wrongKind path kind = pathErr $
      "`" ++ show path ++ "` is not " ++ aOrAn kind

    notFound = do
      nearbyItems <- take 5 <$> getClosest head
      case head of
        Underscore _ ->
          case nearbyItems of
            [name] -> pathErr $
              " cannot find `" ++ show path ++ "` in scope, did you mean `" ++ show name ++ "`?"
            _ -> do
              addError compileError
                { errorFile = Just file
                , errorSpan = span
                , errorExplain = Just $
                  " Identifiers starting with an underscore are treated specially in Boat, since they" ++
                  " are meant to be used for private items in a module which are not part of the public" ++
                  " interface. Specifically, they are excluded by default when importing items from another" ++
                  " module using `use`. If you want to access an item starting with an underscore that isn't" ++
                  " in the current module, you must explicitly add it to the import list rather than using `_`."
                , errorMessage =
                  " cannot find `" ++ show path ++ "` in scope, did you forget to define it" ++
                  " or explicitly `use` it?\n" ++
                  " (private items starting with '_' must be explicitly imported from other modules)" }
              return EmptyPath
        _ -> pathErr $
          " cannot find `" ++ show path ++ "` in scope, " ++
          suggestionMessage "did you forget to `use` it?" nearbyItems

-- | Finds items in scope for which the requested name might be a typo
getClosest :: Name -> NR [Name]
getClosest target = do
  Names { finalNames, otherNames, localNames } <- ask
  let
    normalizedTarget = normalizeName target
    -- Get a set of all names that are in scope
    names =
      Map.keysSet finalNames
      <> Map.keysSet otherNames
      <> Set.mapMonotonic Identifier localNames
    -- Allow more differences in longer names
    maxDiff
      | length normalizedTarget < 3 =
        -- Since the target name is short, don't allow any normalized differences
        0
      | otherwise =
        -- Since the target name isn't too short, allow (ceil (length/5)) differences
        (4 + length (getNameString target)) `div` 5
    -- Find all of the names within the range of acceptable differences
    closeNames = filter (isClose normalizedTarget maxDiff) $ Set.toList names
  -- Return the list of names sorted by non-normalized edit distance
  return $ sortOn (levenshteinDistance defaultEditCosts (show target) . show) closeNames

-- | Checks if a name is within some number of edits of a requested string (after normalization)
isClose :: String -> Int -> Name -> Bool
isClose target maxDiff name =
  restrictedDamerauLevenshteinDistance defaultEditCosts target (normalizeName name) <= maxDiff

-- | Normalizes a name to account for capitalization and underscores in identifiers
normalizeName :: Name -> String
normalizeName = \case
  Identifier name -> removeUnderscoresAndCase name
  other -> show other
  where
    removeUnderscoresAndCase = \case
      [] -> []
      ('_':rest) ->
        removeUnderscoresAndCase rest
      (next:rest) ->
        toLower next : removeUnderscoresAndCase rest

-- | Creates a suggestion message for similar items in scope
suggestionMessage :: String -> [Name] -> String
suggestionMessage defaultMessage = \case
  [] ->
    defaultMessage
  [name] ->
    "did you mean `" ++ show name ++ "`?"
  names ->
    defaultMessage ++ "\n(similar names in scope: " ++ intercalate ", " (map show names) ++ ")"

-- | Resolve any kind of expression
nameResolveAfter :: After a => Path -> FilePath -> Meta a -> NR (Meta a)
nameResolveAfter basePath file =
  after $ nameResolveAfterMap basePath file

-- | Resolve a type given a list of valid type parameters
nameResolveRestrictedType :: Path -> FilePath -> Meta Type -> NR (Meta Type)
nameResolveRestrictedType basePath file =
  after (nameResolveAfterMap basePath file)
    { aType = updateType
    , aEffect = updateEffect }
  where
    checkLocal span local = do
      locals <- asks localNames
      when (not $ local `Set.member` locals) do
        nearbyItems <- take 5 <$> getClosest (Identifier local)
        addError compileError
          { errorFile = Just file
          , errorSpan = span
          , errorMessage =
            " cannot find parameter named `" ++ local ++ "`, " ++
            suggestionMessage "did you forget to declare it?" nearbyItems }

    updateType typeWithMeta = do
      case unmeta typeWithMeta of
        TPoly local ->
          checkLocal (metaSpan typeWithMeta) local
        _ ->
          return ()
      return typeWithMeta

    updateEffect effectWithMeta = do
      case unmeta effectWithMeta of
        EffectPoly local ->
          checkLocal (metaSpan effectWithMeta) local
        _ ->
          return ()
      return effectWithMeta

-- | A mapping that resolves all paths in an expression
nameResolveAfterMap :: Path -> FilePath -> AfterMap NR
nameResolveAfterMap basePath file = aDefault
  { aUseExpr = handleUseExpr
  , aWithBindings = withLocals
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

