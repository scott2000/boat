-- | Infers types for all expressions in the program and checks for type and effect errors
module Analyze.InferTypes where

import Utility

import Analyze.InferVariance (lookupDecl, addMatchError, matchArgs)

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
lookupDecl' :: Path -> Infer ([TypeVariance], [DataArg])
lookupDecl' = lookupDecl \path -> do
  decls <- asks (allDatas . iAllDecls)
  return $ HashMap.lookup path decls

-- | Looks up a data type declaration's parameters given an @AllDecls@ map
lookupDecl'' :: AddFatal m => AllDecls -> Path -> m ([TypeVariance], [DataArg])
lookupDecl'' decls = lookupDecl \path -> do
  return $ HashMap.lookup path $ allDatas decls

matchDataArg :: DataArg -> DataArg -> Maybe DataArg
matchDataArg (DataArg var0 args0) (DataArg var1 args1)
  | length args0 /= length args1 = Nothing
  | otherwise =
    DataArg (var0 <> var1) <$> zipWithM matchDataArg args0 args1

type CheckState = StateT (HashSet Path, Map (Meta Span String) (ExprKind, Maybe DataArg)) CompileIO

checkAndDeps :: AllDecls
             -> (Path, Meta (InFile Span) LetDecl)
             -> CompileIO ([Path], (Path, Meta (InFile Span) LetDecl, Set (Meta Span String)))
checkAndDeps decls (path, decl@(LetDecl { letBody, letConstraints } :&: file :/: _)) = do
  (deps, vars) <- execStateT (check letBody) (HashSet.empty, Map.empty)
  return (HashSet.toList deps, (path, decl, Map.keysSet vars))
  where
    addPath :: Path -> CheckState ()
    addPath path = modify \(d, v) ->
      (HashSet.insert path d, v)

    checkType :: MetaR Span Type -> CheckState ()
    checkType =
      expectKindMatchArgs [] VOutput []

    polyArgs :: Map String [DataArg]
    polyArgs =
      Map.fromList $ mapMaybe getArgKind letConstraints
      where
        getArgKind constraint =
          case unmeta constraint of
            name `HasArguments` args ->
              Just (unmeta name, args)
            _ ->
              Nothing

    getVar :: Meta Span String -> MaybeT CheckState [DataArg]
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
      case Map.lookup name vars of
        Nothing ->
          put (deps, Map.insert name (kind, Just dataArg) vars)
        Just (oldKind, _) | kind /= oldKind ->
          addError compileError
            { errorFile = file
            , errorSpan = getSpan name
            , errorMessage =
              show oldKind ++ " parameter `" ++ unmeta name ++ "` cannot also be used as " ++ aOrAn (show kind) }
        Just (_, Nothing) -> return ()
        Just (_, Just oldDataArg) ->
          case matchDataArg oldDataArg dataArg of
            Just newDataArg ->
              put (deps, Map.insert name (kind, Just newDataArg) vars)
            Nothing ->
              addError compileError
                { errorFile = file
                , errorSpan = getSpan name
                , errorMessage =
                  "parameter first used as kind `" ++ show oldDataArg ++ "`\n" ++
                  "      cannot also be used as `" ++ show dataArg ++ "`" }

    matchArgs' :: Span -> [DataArg] -> [DataArg] -> CheckState ()
    matchArgs' actualSpan expected actual =
      matchArgs missingVariance expected actual >>= \case
        Nothing -> return ()
        Just err ->
          addMatchError file actualSpan err
      where
        missingVariance _ _ =
          compilerBug "matchArgs' called with uninferred variance during type inference"

    expectKindMatchArgs :: [String] -> TypeVariance -> [DataArg] -> MetaR Span Type -> CheckState ()
    expectKindMatchArgs locals var args typeWithMeta = do
      runMaybeT (expectKind locals var (Just args) typeWithMeta) >>= \case
        Nothing ->
          return ()
        Just actual ->
          matchArgs' (getSpan typeWithMeta) args actual

    expectKind :: [String] -> TypeVariance -> Maybe [DataArg] -> MetaR Span Type -> MaybeT CheckState [DataArg]
    expectKind locals var args typeWithMeta =
      -- NOTE: A large portion of this code is similar to the type checking code in InferVariance
      case unmeta typeWithMeta of
        TNamed effs name -> do
          (dataEffects, dataArgs) <- lookupDecl'' decls $ unmeta name
          let effCount = length dataEffects
          case drop effCount effs of
            [] -> return ()
            (eff:_) ->
              addError compileError
                { errorFile = file
                , errorSpan = getSpan eff
                , errorMessage =
                  "`" ++ show name ++ "` " ++
                    if effCount == 0 then
                      "does not accept any effect arguments"
                    else
                      "only accepts " ++ plural effCount "effect argument" }
          lift $ zipWithM_ matchEff effs dataEffects
          return dataArgs
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
        TApp a b ->
          expectKind locals var Nothing a >>= \case
            [] -> MaybeT do
              let (base, baseCount) = findBase a
              addError compileError
                { errorFile = file
                , errorSpan = getSpan b
                , errorMessage =
                  "`" ++ show base ++ "` " ++
                    if baseCount == 0 then
                      "does not accept any arguments"
                    else
                      "only accepts " ++ plural baseCount "argument" }
              return Nothing
            DataArg { argVariance, argParams } : rest -> lift do
              expectKindMatchArgs locals (var <> argVariance) argParams b
              return rest
        TForEff e ty -> do
          lift $ expectKindMatchArgs (unmeta e : locals) var [] ty
          return []
        _ ->
          return []
      where
        matchEff effs argVariance =
          forM_ (setEffects $ unmeta effs) \eff ->
            case unmeta eff of
              EffectPoly name ->
                addVar (name <$ eff) KEffect $ NullaryArg (var <> argVariance)
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
    TNamed effs _ ->
      any (any isBlank . setEffects . unmeta) effs
    TAnon _ ->
      True
    TApp a b ->
      hasBlank a || hasBlank b
    TForEff _ ty ->
      hasBlank ty
    _ ->
      False
  where
    isBlank eff =
      case unmeta eff of
        EffectAnon _ -> True
        _ -> False

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

