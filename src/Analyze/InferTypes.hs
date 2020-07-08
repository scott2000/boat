-- | Infers types for all expressions in the program and checks for type and effect errors
module Analyze.InferTypes where

import Utility

import Analyze.InferVariance (lookupDecl, addMatchError, matchKinds)

import Data.Maybe
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Set (Set)

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

-- (A + a?) : (B + b)
--   b ~ (A - B) + a? + b'
-- (A + a?) : B
--   assert(A : B)
--   a? ~ (B - A)
--
-- (A + a) = (B + b) => A + B + c
--   a ~ (B - A) + c
--   b ~ (A - B) + c
-- (A + a) = B => A + B
--   assert(A : B)
--   a ~ (B - A)
-- A = (B + b) => A + B
--   assert(B : A)
--   b ~ (A - B)
-- A = B => A + B
--   assert(A : B)
--   assert(B : A)

type Infer = ReaderT InferInfo (StateT InferState CompileIO)

data InferInfo = InferInfo
  { iAllDecls :: !AllDecls
  , iEffectExpansions :: !(HashMap Path (Set Effect)) }

data InferState = InferState
  { iResolvedDecls :: !(PathMap InferredLetDecl)
  , iUnresolvedDecls :: !(PathMap (Type ()))
  , iConstraints :: !(Map (Constraint ()) ConstraintSource) }

defaultInferState :: InferState
defaultInferState = InferState
  { iResolvedDecls = HashMap.empty
  , iUnresolvedDecls = HashMap.empty
  , iConstraints = Map.empty }

data ConstraintSource = ConstraintSource
  { csLocation :: Maybe ContextLocation
  , csSpan :: InFile Span }

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

-- | Looks up a data type declaration's parameters
lookupDecl' :: Path -> Infer TypeKind
lookupDecl' = lookupDecl \path -> do
  decls <- asks (allDatas . iAllDecls)
  return $ HashMap.lookup path decls

-- | Looks up a data type declaration's parameters given an @AllDecls@ map
lookupDecl'' :: AddFatal m => AllDecls -> Path -> m TypeKind
lookupDecl'' decls = lookupDecl \path -> do
  return $ HashMap.lookup path $ allDatas decls

matchTypeKind :: TypeKind -> TypeKind -> Maybe TypeKind
matchTypeKind (TypeKind eEffs eArgs) (TypeKind aEffs aArgs)
  | length eArgs /= length aArgs = Nothing
  | otherwise =
    TypeKind <$> matchEffs eEffs aEffs <*> zipWithM matchArg eArgs aArgs
  where
    matchEffs [] as = Just as
    matchEffs es [] = Just es
    matchEffs (e:es) (a:as) =
      (:) <$> matchVariance e a <*> matchEffs es as

    matchArg (DataArg eVar eKind) (DataArg aVar aKind) =
      DataArg <$> matchVariance eVar aVar <*> matchTypeKind eKind aKind

    matchVariance VInvariant act = Just act
    matchVariance exp VInvariant = Just exp
    matchVariance exp act
      | exp == act = Just exp
      | otherwise  = Nothing

type CheckState = StateT (HashSet Path, Map (Meta Span String) (ExprKind, Maybe DataArg)) CompileIO

checkAndDeps :: AllDecls
             -> (Path, Meta (InFile Span) LetDecl)
             -> CompileIO ([Path], (Path, Meta (InFile Span) LetDecl, Set (Meta Span String)))
checkAndDeps decls (path, decl@(LetDecl { letTypeAscription, letConstraints, letBody } :&: file :/: _)) = do
  (deps, vars) <- execStateT checkAll (HashSet.empty, Map.empty)
  return (HashSet.toList deps, (path, decl, Map.keysSet vars))
  where
    checkAll :: CheckState ()
    checkAll = do
      mapM_ checkType letTypeAscription
      check letBody

    addPath :: Path -> CheckState ()
    addPath path = modify \(d, v) ->
      (HashSet.insert path d, v)

    checkType :: MetaR Span Type -> CheckState ()
    checkType =
      expectKindMatchKinds [] VOutput NullaryKind

    polyArgs :: Map String TypeKind
    polyArgs =
      Map.fromList $ mapMaybe getArgKind letConstraints
      where
        getArgKind constraint =
          case unmeta constraint of
            name `HasKind` args ->
              Just (unmeta name, args)
            _ ->
              Nothing

    matchVar :: DataArg -> DataArg -> Maybe DataArg
    matchVar (DataArg eVar eKind) (DataArg aVar aKind) =
      DataArg (eVar <> aVar) <$> matchTypeKind eKind aKind

    getVar :: Meta Span String -> MaybeT CheckState TypeKind
    getVar name =
      case Map.lookup (unmeta name) polyArgs of
        Nothing -> MaybeT do
          addError compileError
            { errorFile = file
            , errorSpan = getSpan name
            , errorCategory = Just ECInferVariance
            , errorExplain = Just $
              " Any type variables that are used in place of a type constructor (like `m` in `m Nat`)" ++
              " must be used in a constraint that specifies their kind. If the type variable is not already" ++
              " being used in a constraint, a special constraint can be used to only specify the kind but" ++
              " not introduce any other requirements. For instance, `f (-) (+)` or `m _` could be added" ++
              " in a `with` clause to give those specific kinds to the arguments to `f` and `m`."
            , errorMessage = "cannot determine kind of `" ++ unmeta name ++ "` from constraints" }
          return Nothing
        Just args ->
          return args

    addVar :: Meta Span String -> ExprKind -> DataArg -> CheckState ()
    addVar name kind dataArg = do
      (deps, vars) <- get
      let
        err msg = do
          addError compileError
            { errorFile = file
            , errorSpan = getSpan name
            , errorMessage = msg }
          return Nothing
        kindMismatch oldKind =
          err (show oldKind ++ " parameter `" ++ unmeta name ++ "` cannot also be used as " ++ aOrAn (show kind))
      newEntry <-
        case Map.lookup name vars of
          Nothing ->
            case Map.lookup (unmeta name) polyArgs of
              Just constraintKind
                | kind /= KType ->
                  kindMismatch KType
                | otherwise ->
                  case matchTypeKind (argKind dataArg) constraintKind of
                    Just newKind ->
                      return $ Just dataArg { argKind = newKind }
                    Nothing ->
                      err $
                        "type constrained to kind `" ++ show constraintKind ++ "`\n" ++
                        "  cannot also be used as `" ++ show dataArg ++ "`"
              Nothing ->
                return $ Just dataArg
          Just (oldKind, _) | kind /= oldKind -> do
            kindMismatch oldKind
          Just (_, Nothing) ->
            return Nothing
          Just (_, Just oldDataArg) ->
            case matchVar dataArg oldDataArg of
              Just newDataArg ->
                return $ Just newDataArg
              Nothing -> do
                err $
                  "parameter first used as kind `" ++ show oldDataArg ++ "`\n" ++
                  "      cannot also be used as `" ++ show dataArg ++ "`"
      put (deps, Map.insert name (kind, newEntry) vars)

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
                lift $ addVar (name <$ typeWithMeta) KType $ DataArg var expected
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
          case effs of
            [] -> MaybeT do
              matchEff e VInvariant
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
            argVariance : rest -> lift do
              matchEff e $ var <> argVariance
              return $ TypeKind rest args
        TForEff e ty -> do
          lift $ expectKindMatchKinds (unmeta e : locals) var NullaryKind ty
          return NullaryKind
        _ ->
          return NullaryKind
      where
        matchEff effs var =
          forM_ (setEffects $ unmeta effs) \eff ->
            case unmeta eff of
              EffectPoly name ->
                addVar (name <$ eff) KEffect $ NullaryArg var
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
        EParen a ->
          check a
        EUnaryOp path a ->
          addPath (unmeta path) >> check a
        EBinOp path a b ->
          check a >> addPath (unmeta path) >> check b
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
        PParen a ->
          checkPat a
        PUnaryOp _ a ->
          checkPat a
        PBinOp _ a b ->
          checkPat a >> checkPat b
        _ ->
          return ()

hasBlank :: MetaR Span Type -> Bool
hasBlank typeWithMeta =
  case unmeta typeWithMeta of
    TAnon _ ->
      True
    TApp a b ->
      hasBlank a || hasBlank b
    TEffApp ty e ->
      hasBlank ty || any isBlank (setEffects $ unmeta e)
    TForEff _ ty ->
      hasBlank ty
    _ ->
      False
  where
    isBlank eff =
      case unmeta eff of
        EffectAnon _ -> True
        _ -> False

newLocal :: MonadCompile m => m Effect
newLocal = EffectLocal <$> getNewAnon

inferTypes :: AllDecls -> CompileIO InferredDecls
inferTypes decls = do
  _sortedLets <- topSortExt (checkAndDeps decls) $ allLets decls
  exitIfErrors
  -- let
  --   inferInfo = InferInfo
  --     { iAllDecls = decls
  --     , iEffectExpansions = expansions }
  -- i <- execStateT (runReaderT (mapM_ inferDeclSCC sortedLets) inferInfo) defaultInferState
  -- return decls { allLets = iResolvedDecls i }
  addFatal compileError
    { errorMessage = "type inference not yet implemented" }

