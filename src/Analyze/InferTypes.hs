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
  , iTypeBounds :: !(Map AnonCount (Bound Type))
  , iEffectBounds :: !(Map AnonCount (Bound EffectSet))
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
         -> (UnifyContext -> a -> Bound a -> MaybeT Infer (Bound a))
         -> a
         -> Map AnonCount (Bound a)
         -> MaybeT Infer (Map AnonCount (Bound a))
addBound context anon insert item m = do
  bound <- insert context item $ Map.findWithDefault emptyBound anon m
  return $ Map.insert anon bound m

-- addTypeBound :: UnifyContext
--              -> AnonCount
--              -> (UnifyContext -> Type -> Bound Type -> MaybeT Infer (Bound Type))
--              -> Type
--              -> MaybeT Infer ()
-- addTypeBound context anon insert ty = do
--   s <- get
--   let m = iTypeBounds s
--   m <- addBound context anon insert ty m
--   put s { iTypeBounds = m }

addEffectBound :: UnifyContext
               -> AnonCount
               -> (UnifyContext -> EffectSet -> Bound EffectSet -> MaybeT Infer (Bound EffectSet))
               -> EffectSet
               -> MaybeT Infer ()
addEffectBound context anon insert effs = do
  s <- get
  let m = iEffectBounds s
  m <- addBound context anon insert effs m
  put s { iEffectBounds = m }

data Bound a = Bound
  { lowerBound :: Maybe a
  , upperBound :: Maybe a }

emptyBound :: Bound a
emptyBound = Bound
  { lowerBound = Nothing
  , upperBound = Nothing }

insertLowerBound :: Unify a => UnifyContext -> a -> Bound a -> MaybeT Infer (Bound a)
insertLowerBound context item b =
  case lowerBound b of
    Nothing -> return b
      { lowerBound = Just item }
    Just oldItem -> do
      newItem <- unify context UnifyPlain VOutput oldItem item
      return b
        { lowerBound = Just newItem }

insertUpperBound :: Unify a => UnifyContext -> a -> Bound a -> MaybeT Infer (Bound a)
insertUpperBound context item b =
  case upperBound b of
    Nothing -> return b
      { upperBound = Just item }
    Just oldItem -> do
      newItem <- unify context UnifyPlain VInput oldItem item
      return b
        { upperBound = Just newItem }

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

addUnifyError :: AddError m => UnifyContext -> m ()
addUnifyError UnifyContext { contextLocation, contextSpan = file :/: span, contextActual, contextExpected } =
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

addExpectError :: AddError m => UnifyContext -> m ()
addExpectError UnifyContext { contextLocation, contextSpan = file :/: span, contextActual, contextExpected } =
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

lookupDecl' :: Path -> Infer ([TypeVariance], [DataArg])
lookupDecl' = lookupDecl \path -> do
  decls <- asks (allDatas . iAllDecls)
  return $ pathMapLookup path decls

expandEffect :: Meta Effect -> Infer (Set (Meta Effect))
expandEffect effectWithMeta =
  case unmeta effectWithMeta of
    EffectNamed path ->
      lookupEffect effectWithMeta $ reversePath path
    EffectPoly name ->
      lookupEffect effectWithMeta $ ReversedPath [Identifier name]
    _ ->
      return $ Set.singleton effectWithMeta
  where
    lookupEffect effect path = do
      expansions <- asks iEffectExpansions
      return $
        case Map.lookup path expansions of
          Nothing ->
            Set.singleton effect
          Just effs ->
            Set.mapMonotonic (copySpan effect) effs

expandEffectSet :: Set (Meta Effect) -> Infer (Set (Meta Effect))
expandEffectSet s =
  Set.unions <$> mapM expandEffect (Set.toList s)

unifyEffs :: UnifyContext -> UnifyKind -> [TypeVariance] -> [EffectSet] -> [EffectSet] -> MaybeT Infer [EffectSet]
unifyEffs _ _ _ [] [] =
  return []
unifyEffs context kind (v:vs) allE allA =
  (:) <$> unify context kind v e a <*> unifyEffs context kind vs es as
  where
    splitEffs []     = (emptyEffectSet, [])
    splitEffs (e:es) = (e, es)
    (e, es) = splitEffs allE
    (a, as) = splitEffs allA
unifyEffs _ _ _ _ _ =
  compilerBug "unifyEffs called with too many effects"

addConstraint :: UnifyContext -> Constraint -> Infer ()
addConstraint UnifyContext { contextLocation, contextSpan } constraint =
  modify \s -> s
    { iConstraints = insertIfNotPresent $ iConstraints s }
  where
    cs = ConstraintSource { csLocation = contextLocation, csSpan = contextSpan }
    insertIfNotPresent m
      | constraint `Map.member` m = m
      | otherwise = Map.insert constraint cs m

constrainEffect :: UnifyContext -> Bool -> Set (Meta Effect) -> Meta Effect -> MaybeT Infer ()
constrainEffect context requiresConstraint expected actual = do
  case unmeta actual of
    EffectAnon anon ->
      addEffectBound context anon insertUpperBound $ EffectSet expected
    _ ->
      when requiresConstraint $
        lift $ addConstraint context (actual `IsSubEffectOf` EffectSet expected)

constrainEffects :: UnifyContext -> Set (Meta Effect) -> Set (Meta Effect) -> MaybeT Infer ()
constrainEffects context expected actual = do
  requiresConstraint <-
    if Set.size expected == 1 then
      case unmeta $ Set.findMin expected of
        EffectAnon anon -> do
          forM_ actual $
            addEffectBound context anon insertLowerBound . EffectSet . Set.singleton
          return False
        _ ->
          return True
    else
      return True
  forM_ actual $ constrainEffect context requiresConstraint expected

constrainEqual :: UnifyContext -> Set (Meta Effect) -> Set (Meta Effect) -> MaybeT Infer ()
constrainEqual context expected actual
  | Set.null expected, Set.null actual = return ()
  | anyAnon expected || anyAnon actual = do
    constrainEffects context expected actual
    constrainEffects context actual expected
  | otherwise = MaybeT do
    addUnifyError context
    return Nothing
  where
    anyAnon = any \case
      Meta { unmeta = EffectAnon _ } -> True
      _ -> False

data UnifyKind
  = UnifyPlain
  | UnifyExpect

class Unify a where
  unify :: UnifyContext -> UnifyKind -> TypeVariance -> a -> a -> MaybeT Infer a

instance Unify EffectSet where
  unify context kind variance (EffectSet expected) (EffectSet actual) =
    case (kind, variance) of
      (UnifyPlain, VOutput) ->
        -- Just return a simple union of the effects
        return $ EffectSet $ Set.union expected actual
      _ -> do
        -- Everything else requires effect expansion, so do it now
        exp <- lift $ expandEffectSet expected
        act <- lift $ expandEffectSet actual
        case (kind, variance) of
          (UnifyPlain, VInput) ->
            -- Just return the intersection of the expanded effects
            return $ EffectSet $ Set.intersection exp act
          _ -> do
            -- The simple unification kinds are done, so effect differences are required
            let
              exp' = Set.difference exp act
              act' = Set.difference act exp
            case variance of
              VOutput ->
                constrainEffects context exp' act'
              VInput ->
                constrainEffects context act' exp'
              _ ->
                -- Whenever invariant is passed, require them to be equal
                constrainEqual context exp' act'
            return $ EffectSet exp

