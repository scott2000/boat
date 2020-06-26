-- | Infers types for all expressions in the program and checks for type and effect errors
module Analyze.InferTypes where

import Utility

import Analyze.InferVariance (lookupDecl, addMatchError, matchArgs)

import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

type Infer = ReaderT InferInfo (StateT InferState CompileIO)

data InferInfo = InferInfo
  { iAllDecls :: !AllDecls
  , iDeclExplicitPoly :: !(Map ReversedPath (Set String))
  , iEffectExpansions :: !(Map ReversedPath (Set Effect)) }

data InferState = InferState
  { iResolvedDecls :: !(PathMap LetDeclInferred)
  , iUnresolvedDecls :: !(PathMap Type)
  , iConstraints :: !(Map ConstraintNoSpan ConstraintSource) }

defaultInferState :: InferState
defaultInferState = InferState
  { iResolvedDecls = pathMapEmpty
  , iUnresolvedDecls = pathMapEmpty
  , iConstraints = Map.empty }

data ConstraintSource = ConstraintSource
  { csLocation :: Maybe ContextLocation
  , csSpan :: InFile (Maybe Span) }

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
  return $ pathMapLookup path decls

-- | Looks up a data type declaration's parameters given an @AllDecls@ map
lookupDecl'' :: AddFatal m => AllDecls -> Path -> m ([TypeVariance], [DataArg])
lookupDecl'' decls = lookupDecl \path -> do
  return $ pathMapLookup path $ allDatas decls

matchDataArg :: DataArg -> DataArg -> Maybe DataArg
matchDataArg (DataArg var0 args0) (DataArg var1 args1)
  | length args0 /= length args1 = Nothing
  | otherwise =
    DataArg (var0 <> var1) <$> zipWithM matchDataArg args0 args1

type CheckState = StateT (Set Path, Map (Meta String) (ExprKind, Maybe DataArg)) CompileIO

checkAndDeps :: AllDecls -> InFile LetDecl -> CompileIO ([Path], Set (Meta String))
checkAndDeps decls (file :/: decl) = do
  (deps, vars) <- execStateT (check $ letBody decl) (Set.empty, Map.empty)
  return (Set.toList deps, Map.keysSet vars)
  where
    addPath :: Path -> CheckState ()
    addPath path = modify \(d, v) ->
      (Set.insert path d, v)

    checkType :: Meta Type -> CheckState ()
    checkType =
      expectKindMatchArgs [] VOutput []

    polyArgs :: Map String [DataArg]
    polyArgs =
      Map.fromList $ mapMaybe getArgKind $ letConstraints decl
      where
        getArgKind constraint =
          case unmeta constraint of
            name `HasArguments` args ->
              Just (unmeta name, args)
            _ ->
              Nothing

    getVar :: Meta String -> MaybeT CheckState [DataArg]
    getVar name =
      case Map.lookup (unmeta name) polyArgs of
        Nothing -> MaybeT do
          addError compileError
            { errorFile = Just file
            , errorSpan = metaSpan name
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

    addVar :: Meta String -> ExprKind -> DataArg -> CheckState ()
    addVar name kind dataArg = do
      (deps, vars) <- get
      case Map.lookup name vars of
        Nothing ->
          put (deps, Map.insert name (kind, Just dataArg) vars)
        Just (oldKind, _) | kind /= oldKind ->
          addError compileError
            { errorFile = Just file
            , errorSpan = metaSpan name
            , errorMessage =
              show oldKind ++ " parameter `" ++ unmeta name ++ "` cannot also be used as " ++ aOrAn (show kind) }
        Just (_, Nothing) -> return ()
        Just (_, Just oldDataArg) ->
          case matchDataArg oldDataArg dataArg of
            Just newDataArg ->
              put (deps, Map.insert name (kind, Just newDataArg) vars)
            Nothing ->
              addError compileError
                { errorFile = Just file
                , errorSpan = metaSpan name
                , errorMessage =
                  "parameter first used as kind `" ++ show oldDataArg ++ "`\n" ++
                  "      cannot also be used as `" ++ show dataArg ++ "`" }

    matchArgs' :: Maybe Span -> [DataArg] -> [DataArg] -> CheckState ()
    matchArgs' actualSpan expected actual =
      matchArgs missingVariance expected actual >>= \case
        Nothing -> return ()
        Just err ->
          addMatchError file actualSpan err
      where
        missingVariance _ _ =
          compilerBug "matchArgs' called with uninferred variance during type inference"

    expectKindMatchArgs :: [String] -> TypeVariance -> [DataArg] -> Meta Type -> CheckState ()
    expectKindMatchArgs locals var args typeWithMeta = do
      runMaybeT (expectKind locals var (Just args) typeWithMeta) >>= \case
        Nothing ->
          return ()
        Just actual ->
          matchArgs' (metaSpan typeWithMeta) args actual

    expectKind :: [String] -> TypeVariance -> Maybe [DataArg] -> Meta Type -> MaybeT CheckState [DataArg]
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
                { errorFile = Just file
                , errorSpan = metaSpan eff
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
              { errorFile = Just file
              , errorSpan = metaSpan typeWithMeta
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
                { errorFile = Just file
                , errorSpan = metaSpan typeWithMeta
                , errorMessage = "type constructor name cannot be left blank" }
              return Nothing
            Just expected ->
              return expected
        TApp a b ->
          expectKind locals var Nothing a >>= \case
            [] -> MaybeT do
              let (base, baseCount) = findBase a
              addError compileError
                { errorFile = Just file
                , errorSpan = metaSpan b
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

inferTypes :: AllDecls -> CompileIO AllDeclsInferred
inferTypes decls = do
  (_sortedLets, _iDeclExplicitPoly) <- topSortExt (checkAndDeps decls) (allLets decls)
  exitIfErrors
  -- let
  --   inferInfo = InferInfo
  --     { iAllDecls = decls
  --     , iDeclExplicitPoly
  --     , iEffectExpansions = expansions }
  -- i <- execStateT (runReaderT (mapM_ inferDeclSCC sortedLets) inferInfo) defaultInferState
  -- return decls { allLets = iResolvedDecls i }
  addFatal compileError
    { errorMessage = "type inference not yet implemented" }

