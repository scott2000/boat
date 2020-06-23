module Analyze.InferTypes where

import Utility

import Analyze.InferVariance (lookupDecl, MatchArgsError (..), addMatchError, matchArgs)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

data InferInfo = InferInfo
  { iAllDecls :: !AllDecls
  , iEffectExpansions :: !(Map ReversedPath (Set Effect)) }

data InferState = InferState
  { iResolvedDecls :: !(PathMap (LetDeclWith Type))
  , iUnresolvedDecls :: !(PathMap Type)
  , iTypeBounds :: !(Map AnonCount TypeBound)
  , iEffectBounds :: !(Map AnonCount EffectBound)
  , iConstraints :: !(Map Constraint ConstraintSource) }

type Infer = ReaderT InferInfo (StateT InferState CompileIO)

inferTypes :: AllDecls -> CompileIO (AllDeclsWith Type)
inferTypes = undefined

data ConstraintSource = ConstraintSource
  { csLocation :: Maybe ContextLocation
  , csSpan :: InFile (Maybe Span) }

addBound :: Unify a
         => UnifyContext
         -> AnonCount
         -> (UnifyContext -> a -> b -> MaybeT Infer b)
         -> b
         -> a
         -> Map AnonCount b
         -> MaybeT Infer (Map AnonCount b)
addBound context anon insert empty item m = do
  bound <- insert context item $ Map.findWithDefault empty anon m
  return $ Map.insert anon bound m

addEffectBound :: UnifyContext
               -> AnonCount
               -> (UnifyContext -> EffectSet -> EffectBound -> MaybeT Infer EffectBound)
               -> EffectSet
               -> MaybeT Infer ()
addEffectBound context anon insert effs = do
  s <- get
  let m = iEffectBounds s
  m <- addBound context anon insert eEmptyBound effs m
  put s { iEffectBounds = m }

data EffectBound = EffectBound
  { eLowerBound :: EffectSet
  , eUpperBound :: Maybe EffectSet }

eEmptyBound :: EffectBound
eEmptyBound = EffectBound
  { eLowerBound = emptyEffectSet
  , eUpperBound = Nothing }

eInsertLowerBound :: UnifyContext -> EffectSet -> EffectBound -> MaybeT Infer EffectBound
eInsertLowerBound context effs b
  | Set.null $ setEffects effs = return b
  | Set.null $ setEffects $ eLowerBound b =
    return b { eLowerBound = effs }
  | otherwise = do
    eLowerBound <- unify context UnifyPlain VOutput (eLowerBound b) effs
    return b { eLowerBound }

eInsertUpperBound :: UnifyContext -> EffectSet -> EffectBound -> MaybeT Infer EffectBound
eInsertUpperBound context effs b
  | meta EffectVoid `Set.member` setEffects effs = return b
  | otherwise =
    case eUpperBound b of
      Nothing ->
        return b { eUpperBound = Just effs }
      Just upper -> do
        upper <- unify context UnifyPlain VInput upper effs
        return b { eUpperBound = Just upper }

data TypeBound
  = SubstituteType Type
  | TypeBound
    { tLowerBounds :: Set AnonCount
    , tUpperBounds :: Set AnonCount }

tEmptyBound :: TypeBound
tEmptyBound = TypeBound
  { tLowerBounds = Set.empty
  , tUpperBounds = Set.empty }

data UnifyContext = UnifyContext
  { contextLocation :: Maybe ContextLocation
  , contextSpan :: InFile (Maybe Span)
  , contextExpected :: Type
  , contextActual :: Type }

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

addUnifyError :: UnifyContext -> UnifyKind -> MaybeT Infer a
addUnifyError UnifyContext { contextLocation, contextSpan = file :/: span, contextActual, contextExpected } kind =
  MaybeT do
    case kind of
      UnifyPlain ->
        addError compileError
          { errorFile = Just file
          , errorSpan = span
          , errorMessage =
            "            cannot unify type: " ++ show contextActual ++ "\n" ++
            "with previously inferred type: " ++ show contextExpected ++
            case contextLocation of
              Nothing -> ""
              Just loc ->
                "\n(in " ++ show loc ++ ")" }
      UnifyExpect ->
        addError compileError
          { errorFile = Just file
          , errorSpan = span
          , errorMessage =
            "cannot use type `" ++ show contextActual ++ "`\n" ++
            "     where type `" ++ show contextExpected ++ "` is expected" ++
            case contextLocation of
              Nothing -> ""
              Just loc ->
                "\n(in " ++ show loc ++ ")" }
    return Nothing

lookupDecl' :: Path -> Infer ([TypeVariance], [DataArg])
lookupDecl' = lookupDecl \path -> do
  decls <- asks (allDatas . iAllDecls)
  return $ pathMapLookup path decls

getSubEffects :: Map ReversedPath (Set Effect) -> Meta Effect -> Set (Meta Effect)
getSubEffects expansions effectWithMeta =
  case unmeta effectWithMeta of
    EffectNamed path -> do
      case Map.lookup (reversePath path) expansions of
        Nothing ->
          Set.empty
        Just effs ->
          Set.mapMonotonic (copySpan effectWithMeta) effs
    _ ->
      Set.empty

getSubEffectSet :: Set (Meta Effect) -> Infer (Set (Meta Effect))
getSubEffectSet s = do
  expansions <- asks iEffectExpansions
  return $ Set.unions $ map (getSubEffects expansions) $ Set.toList s

expandEffectSet :: Set (Meta Effect) -> Infer (Set (Meta Effect))
expandEffectSet s =
  Set.union s <$> getSubEffectSet s

simplifyEffectSet :: Set (Meta Effect) -> Infer (Set (Meta Effect))
simplifyEffectSet s =
  Set.difference s <$> getSubEffectSet s

unifyEffs :: UnifyContext
          -> UnifyKind
          -> TypeVariance
          -> [TypeVariance]
          -> [Meta EffectSet]
          -> [Meta EffectSet]
          -> MaybeT Infer [Meta EffectSet]
unifyEffs context kind variance = go
  where
    splitEffs []     = (meta emptyEffectSet, [])
    splitEffs (e:es) = (e, es)

    go _ [] [] =
      return []
    go (v:vs) allE allA =
      (:) <$> unify context kind (variance <> v) e a <*> go vs es as
      where
        (e, es) = splitEffs allE
        (a, as) = splitEffs allA
    go _ _ _ =
      compilerBug "unifyEffs called with too many effects"

containsAnon :: Set (Meta Effect) -> Bool
containsAnon = any hasAnon . Set.toList
  where
    hasAnon eff =
      case unmeta eff of
        EffectAnon _ -> True
        EffectIntersection (EffectSet lhs) (EffectSet rhs) ->
          containsAnon lhs || containsAnon rhs
        _ -> False

addConstraint :: UnifyContext -> Constraint -> Infer ()
addConstraint UnifyContext { contextLocation, contextSpan } constraint =
  modify \s -> s
    { iConstraints = insertIfNotPresent $ iConstraints s }
  where
    cs = ConstraintSource { csLocation = contextLocation, csSpan = contextSpan }
    insertIfNotPresent m
      | constraint `Map.member` m = m
      | otherwise = Map.insert constraint cs m

addExpectConstraint :: UnifyContext -> Set (Meta Effect) -> Meta Effect -> MaybeT Infer ()
addExpectConstraint context expected actual
  | actual `Set.member` expected = return ()
  | otherwise = do
    expansions <- asks iEffectExpansions
    let actualSubs = getSubEffects expansions actual
    if expected `Set.isSubsetOf` actualSubs then
      addUnifyError context UnifyExpect
    else
      lift $ addConstraint context (actual `IsSubEffectOf` EffectSet expected)

{-

a + b : c
  => a : c
     b : c

a : b + c
  => .

a & b : c
  => .

-- IMPORTANT
a : b & c
  => a : b
  => a : c

-}

constrainEffect :: UnifyContext -> Bool -> Set (Meta Effect) -> Meta Effect -> MaybeT Infer ()
constrainEffect context requiresConstraint expected actual = do
  case unmeta actual of
    EffectAnon anon ->
      addEffectBound context anon eInsertUpperBound $ EffectSet expected
    _ ->
      when requiresConstraint $
        addExpectConstraint context expected actual

constrainEffects :: UnifyContext -> Set (Meta Effect) -> Set (Meta Effect) -> MaybeT Infer ()
constrainEffects context expected actual = do
  eExp <- lift $ expandEffectSet expected
  sAct <- lift $ simplifyEffectSet actual
  let nonTrivialMissingAct = Set.difference sAct eExp
  requiresConstraint <-
    if Set.size eExp == 1 then
      case unmeta $ Set.findMin eExp of
        -- TODO support intersection
        EffectAnon anon -> do
          forM_ sAct $
            addEffectBound context anon eInsertLowerBound . EffectSet . Set.singleton
          return False
        _ ->
          return True
    else
      return True
  forM_ nonTrivialMissingAct $ constrainEffect context requiresConstraint eExp

constrainEqual :: UnifyContext -> Set (Meta Effect) -> Set (Meta Effect) -> MaybeT Infer ()
constrainEqual context expected actual = do
  constrainEffects context expected actual
  constrainEffects context actual expected

data UnifyKind
  = UnifyPlain
  | UnifyExpect

class Unify a where
  unify :: UnifyContext -> UnifyKind -> TypeVariance -> a -> a -> MaybeT Infer a

instance Unify a => Unify (Meta a) where
  unify context kind variance expected actual =
    meta <$> unify context kind variance (unmeta expected) (unmeta actual)

instance Unify EffectSet where
  unify context kind variance (EffectSet expected) (EffectSet actual) =
    case (kind, variance) of
      (UnifyPlain, VOutput) ->
        -- Find the simple union of the effect sets
        return $ EffectSet $ Set.union expected actual
      (UnifyPlain, VInput)
        | containsAnon expected || containsAnon actual ->
          -- Since there is an unresolved variable, delay the intersection calculation
          return $ singletonEffectSet $ meta $ EffectIntersection (EffectSet actual) (EffectSet expected)
        | otherwise -> do
          -- Find the intersection of the expansions of the effect sets
          eExp <- lift $ expandEffectSet expected
          eAct <- lift $ expandEffectSet actual
          return $ EffectSet $ Set.intersection eExp eAct
      _ -> do
        -- Match the expected effects to the actual effects using the variance
        case variance of
          VOutput ->
            constrainEffects context expected actual
          VInput ->
            constrainEffects context actual expected
          _ ->
            constrainEqual context expected actual
        return $ EffectSet expected

instance Unify Type where
  unify context kind variance expected actual =
    case (expected, actual) of
      (TUnit, TUnit) ->
        return TUnit

      (TNamed eEffs ePath, TNamed aEffs aPath)
        | aPath == ePath ->
          addUnifyError context kind
        | otherwise -> do
          (dataEffs, _) <- lift $ lookupDecl' $ unmeta ePath
          effs <- unifyEffs context kind variance dataEffs eEffs aEffs
          return $ TNamed effs ePath

      (TPoly eName, TPoly aName)
        | aName == eName ->
          addUnifyError context kind
        | otherwise -> do
          return $ TPoly eName

      (TAnon e, TAnon a)
        | e == a ->
          return $ TAnon e
        | otherwise ->
          undefined -- TODO

      (TApp eLhs eRhs, TApp aLhs aRhs) -> do
        lhs <- unify context kind variance eLhs aLhs
        rhs <- unify context kind variance eRhs aRhs
        return $ TApp lhs rhs

      (TAnon _, _) ->
        -- If the expected value is a variable and the actual value isn't, flip it and change the variance
        unify context kind (VInput <> variance) actual expected

      -- TODO Other TAnon's

      _ ->
        addUnifyError context kind

