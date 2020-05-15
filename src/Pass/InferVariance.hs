module Pass.InferVariance (inferVariance) where

import Utility.Basics
import Utility.ErrorPrint
import Utility.TopSort
import Utility.AST
import Utility.Program

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Control.Monad.Trans.Maybe

data VarianceConstraint = VarianceConstraint
  { vBase :: TypeVariance
  , vDeps :: [AnonCount] }

defaultConstraint :: VarianceConstraint
defaultConstraint = VarianceConstraint
  { vBase = VOutput
  , vDeps = [] }

addStep :: TypeVariance -> VarianceConstraint -> VarianceConstraint
addStep (VAnon anon) cs =
  cs { vDeps = anon : vDeps cs }
addStep other cs =
  cs { vBase = other <> vBase cs }

type DeclMap = Map (Meta Path) (InFile DataDecl)

declDeps :: InFile DataDecl -> [Meta Path]
declDeps (_ :/: DataDecl { dataVariants }) =
  Set.toList $ execWriter $ mapM_ variantDeps dataVariants
  where
    variantDeps = mapM_ typeDeps . snd . unmeta

    typeDeps ty =
      case unmeta ty of
        TAnyFuncArrow _ ->
          return ()
        TNamed _ name ->
          tell $ Set.singleton name
        TApp a b ->
          typeDeps a >> typeDeps b
        _ ->
          return ()

data InferVariable
  = InvariantVariable
  | InferVariable
    { outputVariables :: Set [AnonCount]
    , inputVariables :: Set [AnonCount] }

emptyInferVariable :: InferVariable
emptyInferVariable = InferVariable
  { outputVariables = Set.empty
  , inputVariables = Set.empty }

-- TODO add short circuiting for (Out [], In []) -> Inv
addConstraint :: VarianceConstraint -> InferVariable -> InferVariable
addConstraint _ InvariantVariable = InvariantVariable
addConstraint VarianceConstraint { vBase, vDeps } i =
  case vBase of
    VOutput ->
      i { outputVariables = Set.insert vDeps $ outputVariables i }
    VInput ->
      i { inputVariables = Set.insert vDeps $ inputVariables i }
    VInvariant ->
      InvariantVariable

data InferState = InferState
  { iResolvedDecls :: !DeclMap
  , iUnresolvedDecls :: !DeclMap
  , iUnresolvedVars :: !(Map AnonCount InferVariable) }

defaultInferState :: InferState
defaultInferState = InferState
  { iResolvedDecls = Map.empty
  , iUnresolvedDecls = Map.empty
  , iUnresolvedVars = Map.empty }

type Infer = StateT InferState CompileIO

removeNames :: DataSig -> ([TypeVariance], [DataArg])
removeNames DataSig { dataEffects, dataArgs } =
  (map snd dataEffects, map snd dataArgs)

lookupDecl :: Meta Path -> Infer ([TypeVariance], [DataArg])
lookupDecl Meta { unmeta = Core (Operator "->") } =
  return ([VOutput], [DataArg VInput [], DataArg VOutput []])
lookupDecl path = do
  InferState { iResolvedDecls, iUnresolvedDecls } <- get
  case Map.lookup path iUnresolvedDecls of
    Just decl -> return $ removeNames $ dataSig $ unfile decl
    Nothing ->
      case Map.lookup path iResolvedDecls of
        Just decl -> return $ removeNames $ dataSig $ unfile decl
        Nothing -> lift $ compilerBug $ "lookupDecl couldn't find `" ++ show path ++ "`"

insertConstraint :: AnonCount -> VarianceConstraint -> Infer ()
insertConstraint anon c = do
  modify $ \i -> i { iUnresolvedVars = Map.alter update anon $ iUnresolvedVars i }
  where
    update old = Just $ addConstraint c $
      case old of
        Nothing -> emptyInferVariable
        Just old -> old

inferVariance :: AllDecls -> CompileIO AllDecls
inferVariance decls = do
  i <- execStateT runInfer defaultInferState
  return decls { allDatas = iResolvedDecls i }
  where
    runInfer =
      mapM_ inferDeclSCC $ topSortMap declDeps $ allDatas decls

inferDeclSCC :: SCC (Meta Path, InFile DataDecl) -> Infer ()
inferDeclSCC scc = do
  modify $ \i -> i { iUnresolvedDecls = unresolved }
  lift $ forM_ (Map.toList unresolved) $ \(name, file :/: _) ->
    addError CompileError
      { errorFile = Just file
      , errorSpan = metaSpan name
      , errorKind = Info
      , errorMessage = (if hasCycles then "" else "not ") ++ "involved in cycle" }
  -- TODO finish
  where
    (hasCycles, unresolved) =
      case scc of
        AcyclicSCC (name, decl) ->
          (False, Map.singleton name decl)
        CyclicSCC decls ->
          (True, Map.fromList decls)

type DataInfo = Map String (ExprKind, DataArg)

getAnon :: DataArg -> AnonCount
getAnon DataArg { argVariance = VAnon anon } = anon
getAnon _ = error "getAnon called with inferred variance"

inferVariant :: FilePath -> DataInfo -> Meta DataVariant -> Infer ()
inferVariant file dataInfo Meta { unmeta = (_, types) } =
  void $ runMaybeT $ forM_ types $ inferTypeNoArg defaultConstraint
  where
    lookupNamed :: ExprKind -> Maybe Span -> String -> MaybeT Infer DataArg
    lookupNamed expected span name =
      case Map.lookup name dataInfo of
        Just (eff, arg)
          | eff == expected -> return arg
          | otherwise -> MaybeT $ lift $ do
            addError CompileError
              { errorFile = Just file
              , errorSpan = span
              , errorKind = Error
              , errorMessage =
                show eff ++ " parameter `" ++ name ++ "` cannot be used as " ++ aOrAn (show expected) }
            return Nothing
        Nothing -> MaybeT $ lift $ do
          addError CompileError
            { errorFile = Just file
            , errorSpan = span
            , errorKind = Error
            , errorMessage =
            "cannot find parameter `" ++ name ++ "` in scope, " ++
            if length name > 3 then
              -- most type variables are short, so if it's longer than 3 characters it's probably wrong
              "did you mean to capitalize it?"
            else
              "did you forget to declare it?" }
          return Nothing

    inferTypeNoArg c ty = do
      args <- inferType c ty
      matchArgs [] (metaSpan ty) args

    matchArgs :: [DataArg] -> Maybe Span -> [DataArg] -> MaybeT Infer ()
    matchArgs expected actualSpan actual
      | actual == expected = return ()
      | otherwise = MaybeT $ lift $ do
        addError CompileError
          { errorFile = Just file
          , errorSpan = actualSpan
          , errorKind = Error
          , errorMessage =
            case length actual `compare` length expected of
              LT -> "type requires " ++ plural (length expected - length actual) "more argument"
              GT -> "type must accept " ++ plural (length actual - length expected) "more argument"
              EQ ->
                "type expected an argument of kind `" ++ showKind expected ++ "`\n" ++
                "but was given an argument of kind `" ++ showKind actual ++ "`" }
        return Nothing
      where
        showKind kindList = show DataArg
          { argVariance = VInvariant
          , argParams = kindList }

    inferType :: VarianceConstraint -> Meta Type -> MaybeT Infer [DataArg]
    inferType c ty =
      case unmeta ty of
        TNamed effs name -> do
          (dataEffects, dataArgs) <- lift $ lookupDecl name
          zipWithM_ matchEff effs dataEffects
          return dataArgs
        TPoly name -> do
          arg <- lookupNamed KType (metaSpan ty) name
          lift $ insertConstraint (getAnon arg) c
          return $ argParams arg
        TApp a b ->
          inferType c a >>= \case
            [] -> MaybeT $ lift $ do
              let (base, baseCount) = findBase a
              addError CompileError
                { errorFile = Just file
                , errorSpan = metaSpan b
                , errorKind = Error
                , errorMessage =
                "`" ++ show base ++ "` " ++
                  if baseCount == 0 then
                    "does not accept any arguments"
                  else
                    "only accepts " ++ plural baseCount "argument" }
              return Nothing
            DataArg { argVariance, argParams } : rest -> do
              actual <- inferType (addStep argVariance c) b
              matchArgs argParams (metaSpan b) actual
              return rest
        _ ->
          return []
      where
        matchEff effs argVariance =
          forM_ (setEffects $ unmeta effs) $ \eff ->
            case unmeta eff of
              EffectPoly name -> do
                arg <- lookupNamed KEffect (metaSpan eff) name
                lift $ insertConstraint (getAnon arg) effC
              EffectAnon _ -> lift $ lift $
                addError CompileError
                  { errorFile = Just file
                  , errorSpan = metaSpan eff
                  , errorKind = Error
                  , errorMessage = "all effects in data type declarations must be specified" }
              _ -> return ()
          where
            effC = addStep argVariance c

