-- | Infers types for all expressions in the program and checks for type and effect errors
module Analyze.InferTypes where

import Utility

import Analyze.InferVariance (lookupDecl, addMatchError, matchKinds)

import Data.List

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

data InferInfo = InferInfo
  { iAllDecls :: !AllDecls
  , iEffectSupers :: !(HashMap Path (HashSet Path))
  , iInitialAnonCount :: !AnonCount
  , iLocalEffectSupers :: !(HashMap String (HashSet Path))
  , iLocalTypeKinds :: !(HashMap String TypeKind)
  , iKnownDecls :: !(HashMap Path (MetaR TypeKind Type))
  , iUnknownDecls :: !(HashMap Path AnonCount) }

getInferInfo :: AllDecls -> CompileIO InferInfo
getInferInfo decls = do
  iEffectSupers <- execStateT (sortEffects $ allEffects decls) HashMap.empty
  iInitialAnonCount <- compileAnonCount <$> compileState
  return InferInfo
    { iAllDecls = decls
    , iEffectSupers
    , iInitialAnonCount
    , iLocalEffectSupers = HashMap.empty
    , iLocalTypeKinds = HashMap.empty
    , iKnownDecls = HashMap.empty
    , iUnknownDecls = HashMap.empty }

withDecls :: HashMap Path (MetaR TypeKind Type) -> HashMap Path AnonCount -> Infer a -> Infer a
withDecls iKnownDecls iUnknownDecls inner = ReaderT \i ->
  runReaderT inner i { iKnownDecls, iUnknownDecls }

type EffectSortState = StateT (HashMap Path (HashSet Path)) CompileIO

sortEffects :: PathMap EffectDecl -> EffectSortState ()
sortEffects =
  mapM_ addEffectSCC . topSort effectDeps

effectDeps :: (Path, Meta (InFile Span) EffectDecl) -> [Path]
effectDeps (_, EffectDecl { effectSuper } :&: _) =
  map unmeta effectSuper

addEffectSCC :: SCC (Path, Meta (InFile Span) EffectDecl) -> EffectSortState ()
addEffectSCC = \case
  AcyclicSCC (path, EffectDecl { effectSuper } :&: file :/: _) -> do
    m <- get
    let
      -- A list of all direct parents
      parents = map unmeta effectSuper
      -- A set of ancestors of the parents
      ancestors = HashSet.unions $ map (`hashMapGet` m) parents
      -- Warn for duplicate effects that are already covered by other effects
      mergeAndCheckDuplicates set [] = return set
      mergeAndCheckDuplicates set ((path :&: span) : rest)
        | path == EffectVoid =
          -- A warning will already have been emitted in "NameResolve", so just ignore `Void`
          mergeAndCheckDuplicates set rest
        | path `HashSet.member` set = do
          addError compileError
            { errorFile = file
            , errorSpan = span
            , errorKind = Warning
            , errorMessage =
              if path `elem` parents then
                "effect is unnecessary since it was already listed"
              else
                "effect is unnecessary since it is an ancestor of another parent effect" }
          mergeAndCheckDuplicates set rest
        | otherwise =
          mergeAndCheckDuplicates (HashSet.insert path set) rest
    superEffects <- mergeAndCheckDuplicates ancestors effectSuper
    put $ HashMap.insert path superEffects m
  CyclicSCC effs -> do
    let
      (_, _ :&: file :/: span) = head effs
      effList =
        intercalate ", " $ map (show . fst) effs
    addError compileError
      { errorFile = file
      , errorSpan = span
      , errorMessage =
        " cyclic subtyping for effect declarations\n" ++
        " (effects in cycle: " ++ effList ++ ")" }
    forM_ effs \(path, _) ->
      modify $ HashMap.insert path HashSet.empty

-- | Looks up a data type declaration's parameters
lookupDecl' :: Path -> Infer TypeKind
lookupDecl' = lookupDecl \path -> do
  decls <- asks (allDatas . iAllDecls)
  return $ HashMap.lookup path decls

-- | Looks up a data type declaration's parameters given an @AllDecls@ map
lookupDecl'' :: AddFatal m => AllDecls -> Path -> m TypeKind
lookupDecl'' decls = lookupDecl \path -> do
  return $ HashMap.lookup path $ allDatas decls

unifyTypeKind :: TypeKind -> TypeKind -> Maybe TypeKind
unifyTypeKind (TypeKind eEffs eArgs) (TypeKind aEffs aArgs)
  | length eArgs /= length aArgs = Nothing
  | otherwise =
    TypeKind <$> matchEffs eEffs aEffs <*> zipWithM matchArg eArgs aArgs
  where
    matchEffs [] as = Just as
    matchEffs es [] = Just es
    matchEffs (e:es) (a:as) =
      (:) <$> matchVariance e a <*> matchEffs es as

    matchArg (DataArg eVar eKind) (DataArg aVar aKind) =
      DataArg <$> matchVariance eVar aVar <*> unifyTypeKind eKind aKind

    matchVariance VInvariant act = Just act
    matchVariance exp VInvariant = Just exp
    matchVariance exp act
      | exp == act = Just exp
      | otherwise  = Nothing

type LetInfo = (HashSet Path, HashMap String (Meta Span (Maybe TypeKind)))

type LetComponent = (Path, Meta (InFile Span) LetDecl, LetInfo)

type CheckState = ReaderT (Maybe (HashMap String (Meta Span TypeKind))) (StateT LetInfo CompileIO)

checkAndDeps :: AllDecls
             -> (Path, Meta (InFile Span) LetDecl)
             -> CompileIO ([Path], LetComponent)
checkAndDeps decls (path, decl@(LetDecl { letTypeAscription, letConstraints, letBody } :&: file :/: _)) = do
  info <- flip execStateT (HashSet.empty, HashMap.empty) do
    polyArgs <-
      let
        addAll map [] = return map
        addAll map (c:cs) =
          case unmeta c of
            (name :&: span) `HasKind` kind ->
              case HashMap.lookup name map of
                Nothing ->
                  addAll (HashMap.insert name (kind :&: span) map) cs
                Just (oldKind :&: oldSpan) -> do
                  let
                    (map', suffix) =
                      case unifyTypeKind kind oldKind of
                        Nothing -> (map, " (and the kinds are incompatible!)")
                        Just k  -> (HashMap.insert name (k :&: oldSpan) map, "")
                  addError compileError
                    { errorFile = file
                    , errorSpan = span
                    , errorMessage =
                      "duplicate kind constraint for `" ++ name ++ "`" ++ suffix }
                  addAll map' cs
            _ ->
              addAll map cs
      in
        addAll HashMap.empty letConstraints
    flip runReaderT (Just polyArgs) $ mapM_ checkType letTypeAscription
    (deps, vars) <- get
    let difference = HashMap.difference polyArgs vars
    put (deps, vars <> HashMap.map (\(k :&: s) -> Just k :&:s) difference)
    flip runReaderT Nothing $ check letBody
    forM_ difference \(_ :&: span) -> do
      addError compileError
        { errorFile = file
        , errorSpan = span
        , errorKind = SpecialError SecondaryError
        , errorMessage =
          "type variable present in constraint but not used in type of `" ++ show letName ++ "`" }
  return (HashSet.toList $ fst info, (path, decl, info))
  where
    letName :: Name
    letName = last $ unpath path

    addPath :: Path -> CheckState ()
    addPath path = modify \(d, v) ->
      (HashSet.insert path d, v)

    checkType :: MetaR Span Type -> CheckState ()
    checkType =
      expectKindMatchKinds [] VOutput NullaryKind
      where
        unusedInType :: ExprKind -> Meta Span String -> CheckState ()
        unusedInType kind (name :&: span) =
          addError compileError
            { errorFile = file
            , errorSpan = span
            , errorExplain = Just $
              " All " ++ show kind ++ " variables that are used in the body of a let declaration must first" ++
              " be used in the type signature or in a constraint. Either add this " ++ show kind ++ " variable" ++
              " to the type signature of `" ++ show letName ++ "`, or replace it with `_` if you don't care" ++
              " what type should go here."
            , errorMessage =
              show kind ++ " variable `" ++ name ++ "` must also be used in type signature or constraint" }

        kindMismatch :: ExprKind -> ExprKind -> Meta Span String -> CheckState ()
        kindMismatch kind oldKind (name :&: span) =
          addError compileError
            { errorFile = file
            , errorSpan = span
            , errorMessage =
              show oldKind ++ " parameter `" ++ name ++ "` cannot also be used as " ++ aOrAn (show kind) }

        getVar :: Meta Span String -> MaybeT CheckState TypeKind
        getVar (name :&: span) =
          ask >>= \case
            Nothing -> do
              -- The type signature has alredy been infererd, so check there for the variable
              vars <- gets snd
              case HashMap.lookup name vars of
                Nothing -> MaybeT do
                  -- The variable wasn't used in the type, so it isn't allowed
                  unusedInType KType (name :&: span)
                  return Nothing
                Just (Nothing :&: _) -> MaybeT do
                  -- The variable was used as an effect, so it isn't allowed
                  kindMismatch KType KEffect (name :&: span)
                  return Nothing
                Just (Just kind :&: _) ->
                  return kind
            Just polyArgs ->
              -- The type signature has not been inferred, so the variable must appear in a constraint
              case HashMap.lookup name polyArgs of
                Nothing -> MaybeT do
                  -- The variable wasn't used in a constraint, so it isn't allowed
                  vars <- gets snd
                  let
                    noConstraintErr suffix =
                      addError compileError
                        { errorFile = file
                        , errorSpan = span
                        , errorCategory = [ECVariance]
                        , errorExplain = Just $
                          " Any type variables that are used in place of a type constructor (like `m` in `m Nat`)" ++
                          " must be used in a constraint that specifies their kind. If the type variable is not" ++
                          " already being used in a constraint, a special constraint can be used to only specify " ++
                          " the kind but not introduce any other requirements. For instance, `f (-) (+)` or `m _`" ++
                          " could be added in a `with` clause to give those specific kinds to the arguments to" ++
                          " `f` and `m`."
                        , errorMessage =
                          "cannot determine kind of `" ++ name ++ "` from constraints" ++ suffix }
                  case HashMap.lookup name vars of
                    Nothing ->
                      -- The variable wasn't used before this, so there is no suggestion about the kind
                      noConstraintErr ""
                    Just (Nothing :&: _) ->
                      -- The variable was used as an effect, so use that error message instead
                      kindMismatch KType KEffect (name :&: span)
                    Just (Just NullaryKind :&: _) ->
                      -- The variable was used, but just as a regular type so it wouldn't give a good suggestion
                      noConstraintErr ""
                    Just (Just kind :&: _) ->
                      -- The variable was used before, so give a suggestion about what its kind might be
                      noConstraintErr ("\n(try adding a constraint of `" ++ showWithName name kind ++ "`)")
                  return Nothing
                Just (kind :&: _) ->
                  return kind

        addVar :: Meta Span String -> (Maybe TypeKind) -> CheckState ()
        addVar (name :&: span) kind = do
          (deps, vars) <- get
          let
            insert entry = put (deps, HashMap.insert name (entry :&: span) vars)
            err msg =
              addError compileError
                { errorFile = file
                , errorSpan = span
                , errorCategory = [ECVariance]
                , errorMessage = msg }
          case kind of
            Nothing ->
              -- This is being used as an effect variable
              case HashMap.lookup name vars of
                Nothing ->
                  -- It wasn't used previously
                  ask >>= \case
                    Nothing ->
                      -- It wasn't used in the type signature
                      unusedInType KEffect (name :&: span)
                    Just _ ->
                      insert Nothing
                Just (Nothing :&: _) ->
                  return ()
                _ ->
                  -- It was previously used as a type
                  kindMismatch KEffect KType (name :&: span)
            Just kind ->
              -- This is being used as a type variable
              case HashMap.lookup name vars of
                Nothing ->
                  -- It wasn't used previously
                  ask >>= \case
                    Nothing ->
                      -- It wasn't used in the type signature
                      unusedInType KType (name :&: span)
                    Just polyArgs ->
                      -- It's being used in the type signature, so check for constraints
                      case HashMap.lookup name polyArgs of
                        Nothing ->
                          -- There was no constraint, so just insert it
                          insert $ Just kind
                        Just (constraintKind :&: _) ->
                          -- There was a constraint, so check if it matches
                          case unifyTypeKind kind constraintKind of
                            Just newKind ->
                              -- The constraint matched, so add the new kind
                              insert $ Just newKind
                            Nothing ->
                              -- The constraint didn't match, so add an error
                              err case kind of
                                NullaryKind ->
                                  " type constrained by `" ++ showWithName name constraintKind ++ "`" ++
                                  " cannot be used without arguments"
                                _ ->
                                  "type constrained by`" ++ showWithName name constraintKind ++ "`\n" ++
                                  "  cannot be used as `" ++ showWithName name kind ++ "`"
                Just (Just oldKind :&: _) ->
                  -- It was already used as a type, so there's a type kind to check
                  ask >>= \case
                    Nothing ->
                      -- It was used in the signature, so just check if it matches
                      matchKinds' span kind oldKind
                    Just _ ->
                      -- It's being used in the type signature, so unify it with the previous usage
                      case unifyTypeKind kind oldKind of
                        Just newKind ->
                          -- The kinds matched successfully, so update the type kind
                          insert $ Just newKind
                        Nothing ->
                          -- The kinds didn't match, so add an error
                          err case (oldKind, kind) of
                            (NullaryKind, _) ->
                              " parameter first used without arguments" ++
                              " cannot also be used as `" ++ showWithName name kind ++ "`"
                            (_, NullaryKind) ->
                              " parameter first used as kind `" ++ showWithName name oldKind ++ "`" ++
                              " cannot also be used without arguments"
                            _ ->
                              "parameter first used as kind `" ++ showWithName name oldKind ++ "`\n" ++
                              "      cannot also be used as `" ++ showWithName name kind ++ "`"
                _ ->
                  -- It was previously used as an effect
                  kindMismatch KType KEffect (name :&: span)

        matchKinds' :: Span -> TypeKind -> TypeKind -> CheckState ()
        matchKinds' actualSpan expected actual =
          matchKinds missingVariance expected actual >>= \case
            Nothing -> return ()
            Just err ->
              addMatchError file actualSpan err
          where
            missingVariance _ _ =
              compilerBug "matchKinds' called with uninferred variance during type inference"

        expectKindMatchKinds :: [String] -> TypeVariance -> TypeKind -> MetaR Span Type -> CheckState ()
        expectKindMatchKinds locals var args typeWithMeta = do
          runMaybeT (expectKind locals var (Just args) typeWithMeta) >>= \case
            Nothing ->
              return ()
            Just actual ->
              matchKinds' (getSpan typeWithMeta) args actual

        expectKind :: [String] -> TypeVariance -> Maybe TypeKind -> MetaR Span Type -> MaybeT CheckState TypeKind
        expectKind locals var args typeWithMeta =
          -- NOTE: A large portion of this code is similar to the type checking code in InferVariance
          case unmeta typeWithMeta of
            TNamed name ->
              lookupDecl'' decls name
            TPoly name
              | name `elem` locals -> MaybeT do
                addError compileError
                  { errorFile = file
                  , errorSpan = getSpan typeWithMeta
                  , errorMessage = "quantified effect `" ++ name ++ "` cannot be used as a type" }
                return Nothing
              | otherwise ->
                case args of
                  Nothing ->
                    getVar (name <$ typeWithMeta)
                  Just expected -> do
                    lift $ addVar (name <$ typeWithMeta) $ Just expected
                    return expected
            TAnon _ ->
              case args of
                Nothing -> MaybeT do
                  addError compileError
                    { errorFile = file
                    , errorSpan = getSpan typeWithMeta
                    , errorMessage = "type constructor name cannot be left blank" }
                  return Nothing
                Just expected ->
                  return expected
            TApp a b -> do
              TypeKind effs args <- expectKind locals var Nothing a
              case args of
                [] -> MaybeT do
                  let (base, _, argCount) = findBase a
                  addError compileError
                    { errorFile = file
                    , errorSpan = getSpan b
                    , errorMessage =
                      "`" ++ show base ++ "` " ++
                        if argCount == 0 then
                          "does not accept any type arguments"
                        else
                          "only accepts " ++ plural argCount  "type argument" }
                  return Nothing
                DataArg { argVariance, argKind } : rest -> lift do
                  expectKindMatchKinds locals (var <> argVariance) argKind b
                  return $ TypeKind effs rest
            TEffApp ty e -> do
              TypeKind effs args <- expectKind locals var Nothing ty
              lift $ addEffs e
              case effs of
                [] -> MaybeT do
                  let (base, effCount, _) = findBase ty
                  addError compileError
                    { errorFile = file
                    , errorSpan = getSpan e
                    , errorMessage =
                      "`" ++ show base ++ "` " ++
                        if effCount == 0 then
                          "does not accept any effect arguments"
                        else
                          "only accepts " ++ plural effCount  "effect argument" }
                  return Nothing
                _ : rest -> lift do
                  return $ TypeKind rest args
            TForEff e ty -> do
              lift $ expectKindMatchKinds (unmeta e : locals) var NullaryKind ty
              return NullaryKind
            _ ->
              return NullaryKind
          where
            addEffs effs =
              forM_ (esToList $ unmeta effs) \eff ->
                case unmeta eff of
                  EffectPoly name ->
                    addVar (name <$ eff) Nothing
                  _ ->
                    return ()

    check exprWithMeta =
      case unmeta exprWithMeta of
        EValue (VFun cases) ->
          checkCases cases
        EGlobal path ->
          addPath path
        EApp a b ->
          check a >> check b
        ESeq a b ->
          check a >> check b
        ELet pat val expr ->
          checkPat pat >> check val >> check expr
        EMatchIn exprs cases ->
          mapM_ (check) exprs >> checkCases cases
        EUse _ a ->
          check a
        ETypeAscribe a ty ->
          check a >> checkType ty
        EDataCons path exprs ->
          addPath path >> mapM_ (check) exprs
        _ ->
          return ()
      where
        checkCases =
          mapM_ \(pats, expr) ->
            forM_ pats checkPat >> check expr

    checkPat patternWithMeta =
      case unmeta patternWithMeta of
        PCons _ xs ->
          mapM_ (checkPat) xs
        PTypeAscribe a ty ->
          checkPat a >> checkType ty
        _ ->
          return ()

data ContextLocation
  = CFunctionArgument (Maybe Path) Int
  | CLetBinding (Maybe String)
  | CMatchBranch Int
  | CMatchInput Int

instance Show ContextLocation where
  show = \case
    CFunctionArgument path index ->
      ordinal index ++ " argument of " ++
        case path of
          Nothing ->
            "function"
          Just path ->
            "`" ++ show (last $ unpath path) ++ "`"
    CLetBinding name ->
      "let binding" ++
        case name of
          Nothing -> ""
          Just name ->
            " for `" ++ name ++ "`"
    CMatchBranch index ->
      ordinal index ++ " match case"
    CMatchInput index ->
      ordinal index ++ " input for match expression"

newLocal :: MonadCompile m => m Effect
newLocal = EffectLocal <$> getNewAnon

inferTypes :: AllDecls -> CompileIO InferredDecls
inferTypes decls = do
  sortedLets <- topSortExt (checkAndDeps decls) $ allLets decls
  inferInfo <- getInferInfo decls
  liftIO do
    putStrLn "\nEffect ancestors:\n"
    forM_ (HashMap.toList $ iEffectSupers inferInfo) \(path, supers) ->
      putStrLn $ show path ++
        if HashSet.null supers then
          ""
        else
          " : " ++ intercalate ", " (map show $ HashSet.toList supers)
  exitIfErrors
  let
    runInfer = do
      mapM_ (inferDecls . flattenSCC) sortedLets
      restoreAnonCount
  inferState <- execStateT (runReaderT runInfer inferInfo) defaultInferState
  return InferredDecls
    { iDatas = allDatas decls
    , iLets = iResolvedDecls inferState }

type Infer = ReaderT InferInfo (StateT InferState CompileIO)

data InferState = InferState
  { iResolvedDecls :: !(PathMap InferredLetDecl)
  , iFailedDecls :: !(HashSet Path)
  , iAnonEffectSubs :: !(Map AnonCount (EffectSet ()))
  , iAnonEffectBounds :: !(Map AnonCount (EffectSet ()))
  , iAnonTypeSubs :: !(Map AnonCount (MetaR TypeKind Type))
  , iAnonTypeBounds :: !(Map AnonCount (Set AnonCount))
  , iAnonTypeKinds :: !(Map AnonCount TypeKind) }

defaultInferState :: InferState
defaultInferState = InferState
  { iResolvedDecls = HashMap.empty
  , iFailedDecls = HashSet.empty
  , iAnonEffectSubs = Map.empty
  , iAnonEffectBounds = Map.empty
  , iAnonTypeSubs = Map.empty
  , iAnonTypeBounds = Map.empty
  , iAnonTypeKinds = Map.empty }

restoreAnonCount :: Infer ()
restoreAnonCount = do
  compileAnonCount <- asks iInitialAnonCount
  compileModify \s -> s
    { compileAnonCount }

type TypedComponent = (LetComponent, MetaR TypeKind Type)

splitComponents :: (([TypedComponent], [TypedComponent]) -> Infer ())
                -> [LetComponent]
                -> Infer ()
splitComponents inner = go HashMap.empty HashMap.empty [] []
  where
    go known unknown anonList polyList = \case
      [] ->
        -- Sort by location so that there is a consistent and reasonable order
        let getLocation ((_, _ :&: location, _), _) = location in
        withDecls known unknown $ inner (sortOn getLocation anonList, polyList)
      (component@(path, LetDecl { letTypeAscription } :&: _, (deps, vars)) : rest) -> do
        i <- get
        if HashSet.null $ deps `HashSet.intersection` iFailedDecls i then
          case letTypeAscription of
            Nothing -> do
              anon <- getNewAnon
              let
                unknown' = HashMap.insert path anon unknown
                anonList' = (component, TAnon anon :&: NullaryKind) : anonList
              go known unknown' anonList' polyList rest
            Just ty -> do
              ty <- resolveKind ty
              let known' = HashMap.insert path ty known
              if HashMap.null vars then
                -- Since there were no variables used, infer it with any declarations without signatures
                go known' unknown ((component, ty) : anonList) polyList rest
              else
                go known' unknown anonList ((component, ty) : polyList) rest
        else do
          -- Since a dependency failed, don't even try to resolve this
          put i { iFailedDecls = HashSet.insert path $ iFailedDecls i }
          return ()

inferDecls :: [LetComponent] -> Infer ()
inferDecls =
  splitComponents \(anonList, polyList) -> do
    liftIO $ putStrLn ""

    -- First, infer all non-polymorphic declarations
    when (not $ null anonList) do
      forM_ anonList inferComponent
      forM_ anonList generalizeComponent
      forM_ anonList finalizeComponent
      resetVariables

    -- Infer each polymorphic binding independently
    forM_ polyList \poly -> do
      inferComponent poly
      finalizeComponent poly
      resetVariables
  where
    resetVariables = do
      liftIO $ putStrLn "**"
      modify \i -> i
        { iAnonEffectSubs = Map.empty
        , iAnonEffectBounds = Map.empty
        , iAnonTypeSubs = Map.empty
        , iAnonTypeBounds = Map.empty
        , iAnonTypeKinds = Map.empty }
      restoreAnonCount

inferComponent :: TypedComponent -> Infer ()
inferComponent ((path, _, _), _) =
  liftIO $ putStrLn $ ">> " ++ show path

generalizeComponent :: TypedComponent -> Infer ()
generalizeComponent ((path, _, _), _) =
  liftIO $ putStrLn $ "-- " ++ show path

finalizeComponent :: TypedComponent -> Infer ()
finalizeComponent ((path, _, _), _) =
  liftIO $ putStrLn $ "<< " ++ show path

inferExpr :: MetaR Span Expr -> Infer (MetaR (Typed Span) Expr)
inferExpr = undefined

-- (A + a?) : (B + b)
--   b ~ (A - B) + b'
--   a? ~ a0 + a1 + a2 with a0 : A, a1 : B, a2 : b'
-- (A + a?) : B
--   assert(A : B)
--   a? : B

unifyKinds :: TypeKind -> TypeKind -> MaybeT Infer TypeKind
unifyKinds exp act =
  MaybeT $ return $ unifyTypeKind exp act

matchKinds' :: TypeKind -> TypeKind -> MaybeT Infer ()
matchKinds' expected actual =
  matchKinds missingVariance expected actual >>= \case
    Nothing -> return ()
    Just _ -> empty
  where
    missingVariance _ _ =
      compilerBug "matchKinds' called with uninferred variance during type inference"

unifyAnonKinds :: AnonCount -> AnonCount -> MaybeT Infer TypeKind
unifyAnonKinds exp act = do
  i@InferState { iAnonTypeKinds } <- get
  let
    expKind = mapGet exp iAnonTypeKinds
    actKind = mapGet act iAnonTypeKinds
  kind <- unifyKinds expKind actKind
  put i
    { iAnonTypeKinds = Map.insert exp kind $ Map.insert act kind iAnonTypeKinds }
  return kind

substituteForall :: String -> Effect -> MetaR TypeKind Type -> MetaR TypeKind Type
substituteForall name sub = goTy
  where
    eff = EffectPoly name
    goTy =
      fmap \case
        TApp a b ->
          TApp (goTy a) (goTy b)
        TEffApp ty (es :&: info) ->
          let
            es' | esMember eff es = esInsert (sub :&: NullaryKind) $ esDelete eff es
                | otherwise       = es
          in
            TEffApp (goTy ty) (es' :&: info)
        TForEff e ty
          | unmeta e == name ->
            TForEff e ty
          | otherwise ->
            TForEff e (goTy ty)
        other -> other

resolveKind :: MetaR a Type -> Infer (MetaR TypeKind Type)
resolveKind (ty :&: _) =
  case ty of
    TApp a b -> do
      a <- resolveKind a
      b <- resolveKind b
      forM

(<:) :: MetaR TypeKind Type -> MetaR TypeKind Type -> MaybeT Infer ()
lower <: upper = do
  -- TODO unify kinds
  lower <- subAnon lower
  upper <- subAnon upper
  checkSubstituted lower upper
  where
    subAnon ty =
      case unmeta ty of
        TAnon anon -> do
          subs <- gets iAnonTypeSubs
          case Map.lookup anon subs of
            Nothing -> return ty
            Just ty -> return ty
        _ -> return ty

checkSubstituted :: MetaR TypeKind Type -> MetaR TypeKind Type -> MaybeT Infer ()
checkSubstituted lower upper =
  case (unmeta lower, unmeta upper) of
    (TAnon a, TAnon b) -> do
      modify \i -> i
        { iAnonTypeBounds = Map.insertWith (<>) a (Set.singleton b) $ iAnonTypeBounds i }
      void $ unifyAnonKinds a b
    (TAnon a, _) -> do
      lower <- lift $ copyStructure upper
      checkSubstituted lower upper
      substitute a lower
    (_, TAnon b) -> do
      upper <- lift $ copyStructure lower
      checkSubstituted lower upper
      substitute b upper
    (TForEff (e :&: _) ty, _) -> do
      anon <- getNewAnon
      substituteForall e (EffectAnon anon) ty <: upper
    (_, TForEff (e :&: _) ty) -> do
      anon <- getNewAnon
      lower <: substituteForall e (EffectLocal anon) ty
    (a, b) ->
      guard $ a == b

substitute :: AnonCount -> MetaR TypeKind Type -> MaybeT Infer ()
substitute _ (TAnon _ :&: _) =
  compilerBug "substitute called with two anonymous type variables"
substitute anon ty = do
  i <- get
  -- TODO check if this is the right "unify"
  kind <- unifyKinds (getInfo ty) $ mapGet anon $ iAnonTypeKinds i
  put i
    { iAnonTypeSubs = Map.insert anon ty $ iAnonTypeSubs i
    , iAnonTypeBounds = Map.delete anon $ iAnonTypeBounds i
    , iAnonTypeKinds = Map.insert anon kind $ iAnonTypeKinds i }
  case Map.lookup anon $ iAnonTypeBounds i of
    Nothing ->
      return ()
    Just bounds ->
      forM_ bounds \bound -> do
        ty <- lift $ copyStructure ty
        iAnonTypeKinds <- gets iAnonTypeKinds
        checkSubstituted ty (TAnon bound :&: mapGet bound iAnonTypeKinds)
        substitute bound ty

copyStructure :: MetaR TypeKind Type -> Infer (MetaR TypeKind Type)
copyStructure typeWithMeta =
  evalStateT (copyTy typeWithMeta) Map.empty
  where
    copyTy (ty :&: kind) =
      case ty of
        TAnon anon -> do
          m <- get
          case Map.lookup anon m of
            Nothing -> do
              anon' <- getNewAnon
              put $ Map.insert anon anon' m
              lift do
                i@InferState { iAnonTypeKinds } <- get
                let kind = mapGet anon iAnonTypeKinds
                put i
                  { iAnonTypeKinds = Map.insert anon' kind iAnonTypeKinds }
                return $ withInfo kind $ TAnon anon'
            Just anon' -> lift do
              kind <- mapGet anon' <$> gets iAnonTypeKinds
              return $ withInfo kind $ TAnon anon'
        TApp a b -> do
          a <- copyTy a
          b <- copyTy b
          return $ withInfo kind $ TApp a b
        TEffApp ty _ -> do
          ty <- copyTy ty
          e <- newEff
          return $ withInfo kind $ TEffApp ty e
        TForEff _ ty ->
          copyTy ty
        other ->
          return $ withInfo kind other

    newEff = withInfo NullaryKind . esSingleton . withInfo NullaryKind . EffectAnon <$> getNewAnon

