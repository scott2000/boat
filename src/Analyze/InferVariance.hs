-- | Infers variance information for data type declarations for use in type inference
module Analyze.InferVariance where

import Utility

import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Control.Monad.Trans.Maybe

-- | A constraint that can be placed on a data type parameter
data VarianceConstraint = VarianceConstraint
  { vBase :: TypeVariance
  , vDeps :: [AnonCount] }

-- | The constraint given to parameters used directly in variants
defaultConstraint :: VarianceConstraint
defaultConstraint = VarianceConstraint
  { vBase = VOutput
  , vDeps = [] }

-- | Modifies a constraint to be contained in another constrained parameter
addStep :: TypeVariance -> VarianceConstraint -> VarianceConstraint
addStep (VAnon anon) cs =
  cs { vDeps = anon : vDeps cs }
addStep other cs =
  cs { vBase = other <> vBase cs }

-- | A map of data type declarations
type DeclMap = Map (Meta Path) (InFile DataDecl)

-- | Finds the data types used by each data type so they can be sorted
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

-- | A record of the constraints placed on a given inference variable
data InferVariable
  = InvariantVariable
  | InferVariable
    { outputVariables :: Set [AnonCount]
    , inputVariables :: Set [AnonCount] }

-- | An inference variable with no constraints
emptyInferVariable :: InferVariable
emptyInferVariable = InferVariable
  { outputVariables = Set.empty
  , inputVariables = Set.empty }

-- | Adds a constraint to an inference variable
addConstraint :: VarianceConstraint -> InferVariable -> InferVariable
addConstraint _ InvariantVariable = InvariantVariable
addConstraint VarianceConstraint { vBase, vDeps } i =
  case vBase of
    VOutput
      | null vDeps && Set.member [] (inputVariables i) ->
        InvariantVariable
      | otherwise ->
        i { outputVariables = Set.insert vDeps $ outputVariables i }
    VInput
      | null vDeps && Set.member [] (outputVariables i) ->
        InvariantVariable
      | otherwise ->
        i { inputVariables = Set.insert vDeps $ inputVariables i }
    VInvariant ->
      InvariantVariable

-- | Find the inference variables that constraint a given variable
variableDeps :: InferVariable -> [AnonCount]
variableDeps InvariantVariable = []
variableDeps InferVariable { outputVariables, inputVariables } =
  Set.toList $ add outputVariables $ add inputVariables $ Set.empty
  where
    add vars s = foldr (Set.union . Set.fromList) s vars

-- | Makes a new 'InferVariable', but simplifies conflicting constraints to be invariant
simplifyInferVariable :: Set [AnonCount] -> Set [AnonCount] -> InferVariable
simplifyInferVariable outputVariables inputVariables
  | [] `Set.member` outputVariables && [] `Set.member` inputVariables = InvariantVariable
  | otherwise = InferVariable { outputVariables, inputVariables }

-- | Substitutes a set of inferred variables into a set of constraints
substituteVars :: Map AnonCount TypeVariance -> InferVariable -> InferVariable
substituteVars _ InvariantVariable = InvariantVariable
substituteVars m InferVariable { outputVariables, inputVariables } =
  foldr updateConstraint emptyInferVariable $
    getConstraints VOutput outputVariables ++ getConstraints VInput inputVariables
  where
    getConstraints var s =
      Set.toList s <&> \list -> VarianceConstraint
        { vBase = var
        , vDeps = list }

    updateConstraint VarianceConstraint { vBase, vDeps } =
      addConstraint $ foldr sub VarianceConstraint { vBase, vDeps = [] } vDeps
      where
        sub anon c =
          let
            step =
              case Map.lookup anon m of
                Nothing -> VAnon anon
                Just var -> var
          in
            addStep step c

-- | 'StateT' for storing information about uninferred variables
type Infer = StateT InferState CompileIO

-- | Stores information about which declarations have been resolved and what constraints exists
data InferState = InferState
  { -- | A map of declarations that have already been resolved
    iResolvedDecls :: !DeclMap
    -- | A map of declarations that are currently being resolved and aren't fully known
  , iUnresolvedDecls :: !DeclMap
    -- | A map of resolved inference variables that may be substituted
  , iResolvedVars :: !(Map AnonCount TypeVariance)
    -- | A map of unresolved inference variables that have yet to be substituted
  , iUnresolvedVars :: !(Map AnonCount InferVariable) }

-- | The default state with nothing inferred yet
defaultInferState :: InferState
defaultInferState = InferState
  { iResolvedDecls = Map.empty
  , iUnresolvedDecls = Map.empty
  , iResolvedVars = Map.empty
  , iUnresolvedVars = Map.empty }

-- | Removes the unneeded parameter names from a 'DataSig'
removeNames :: DataSig -> ([TypeVariance], [DataArg])
removeNames DataSig { dataEffects, dataArgs } =
  (map snd dataEffects, map snd dataArgs)

-- | Looks up a data type declaration's parameters
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

-- | Inserts a new constraint to an inference variable
insertConstraint :: AnonCount -> VarianceConstraint -> Infer ()
insertConstraint anon c =
  modify \i -> i
    { iUnresolvedVars = Map.adjust (addConstraint c) anon $ iUnresolvedVars i }

-- | Infers variance information for the parameters of every data type declaration
inferVariance :: AllDecls -> CompileIO AllDecls
inferVariance decls = do
  i <- execStateT runInfer defaultInferState
  return decls { allDatas = iResolvedDecls i }
  where
    runInfer =
      mapM_ inferDeclSCC $ topSortMap declDeps $ allDatas decls

-- | Infers variance information for a single 'SCC' of the graph of data types
inferDeclSCC :: SCC (Meta Path, InFile DataDecl) -> Infer ()
inferDeclSCC scc = do
  let anonMap = foldr addAnons Map.empty unresolvedList
  modify \i -> i
    { iUnresolvedDecls = unresolvedMap
    , iResolvedVars = Map.empty
    , iUnresolvedVars = Map.map (const emptyInferVariable) anonMap }
  forM_ unresolvedList \(_, file :/: decl) -> do
    dataInfo <- lift $ makeDataInfo file $ dataSig decl
    forM_ (dataVariants decl) $ generateConstraints file dataInfo
  unresolvedVars <- gets iUnresolvedVars
  if isSCCAcyclic scc then
    -- The SCC is acyclic so there cannot be cyclic constraints
    mapM_ (inferConstraintSCC anonMap . AcyclicSCC) $ Map.toList unresolvedVars
  else
    -- There may be cyclic constraints so a second sort is needed
    mapM_ (inferConstraintSCC anonMap) $ topSortMap variableDeps unresolvedVars
  resolvedVars <- gets iResolvedVars
  modify \i -> i
    { iResolvedDecls = foldr (addResolved resolvedVars) (iResolvedDecls i) unresolvedList }
  where
    unresolvedList = flattenSCC scc
    unresolvedMap = Map.fromList unresolvedList

    addAnons (_, file :/: DataDecl { dataSig = DataSig { dataEffects, dataArgs } }) m =
      foldr addEff (foldr addArg m dataArgs) dataEffects
      where
        -- Ignore arguments that weren't specified by name
        addEff (UnnamedArg, _) = id
        addEff (name, VAnon var) = Map.insert var (file :/: metaSpan name)
        addArg (UnnamedArg, _) = id
        addArg (name, arg) = Map.insert (getAnon arg) (file :/: metaSpan name)

    addResolved rvars (name, file :/: decl) =
      Map.insert name $ file :/: decl
        { dataSig = resDataSig $ dataSig decl }
      where
        resDataSig DataSig { dataEffects, dataArgs } = DataSig
          { dataEffects = map resEff dataEffects
          , dataArgs = map resArg dataArgs }
        resEff eff@(UnnamedArg, _) = eff
        resEff (name, VAnon var) = (name, mapGet var rvars)
        resArg arg@(UnnamedArg, _) = arg
        resArg (name, DataArg (VAnon var) args) = (name, DataArg (mapGet var rvars) args)

-- | Information about all parameters of a data type declaration
type DataInfo = Map String (Maybe (ExprKind, DataArg))

-- | Constructs a 'DataInfo' map from a 'DataSig'
makeDataInfo :: AddError m => FilePath -> DataSig -> m DataInfo
makeDataInfo file DataSig { dataEffects, dataArgs } =
  execStateT addAll Map.empty
  where
    addAll = do
      forM_ dataEffects \(name, variance) ->
        add name $ Just (KEffect, NullaryArg variance)
      forM_ dataArgs \(name, arg) ->
        add name $ Just (KType, arg)

    add UnnamedArg _ = return ()
    add Meta { unmeta = name, metaSpan } info = do
      m <- get
      if Map.member name m then do
        lift $ addError CompileError
          { errorFile = Just file
          , errorSpan = metaSpan
          , errorKind = Error
          , errorMessage = "the name `" ++ name ++ "` has already been taken by another parameter" }
        put $ Map.insert name Nothing m
      else
        put $ Map.insert name info m

-- | Gets the 'AnonCount' of an uninferred parameter
getAnon :: DataArg -> AnonCount
getAnon DataArg { argVariance = VAnon anon } = anon
getAnon _ = error "getAnon called with inferred variance"

-- | Represents an error from 'matchArgs'
data MatchArgsError
  = RequiresArgs Int
  | MustAcceptArgs Int
  | GeneralMismatch [DataArg] [DataArg]

instance Show MatchArgsError where
  show = \case
    RequiresArgs n -> "type requires " ++ plural n "more argument"
    MustAcceptArgs n -> "type must accept " ++ plural n "more argument"
    GeneralMismatch expected actual ->
      "type argument of kind:              " ++ showKind actual ++ "\n" ++
      "cannot be passed to type expecting: " ++ showKind expected
    where
      showKind kindList = show DataArg
        { argVariance = VInvariant
        , argParams = kindList }

-- | Emits a 'MatchArgsError' in the given file at the given span
addMatchError :: AddError m => FilePath -> Maybe Span -> MatchArgsError -> m ()
addMatchError file span err =
  add CompileError
    { errorFile = Just file
    , errorSpan = span
    , errorKind = Error
    , errorMessage = show err }
  where
    add =
      case err of
        GeneralMismatch _ _ ->
          -- Use a secondary error since this error is potentially complex and may be caused by a previous error
          addSecondaryError
        _ ->
          -- Basic errors such as forgetting an argument are simple to understand so use a primary error
          addError

-- | Matches the expected arguments with the actual arguments for a type
matchArgs :: Monad m
          => (TypeVariance -> AnonCount -> m ()) -- ^ Specifies what to do for uninferred variance
          -> [DataArg]                           -- ^ The arguments that the type is expected to accept
          -> [DataArg]                           -- ^ The arguments that the type actually accepts
          -> m (Maybe MatchArgsError)            -- ^ The error produced by unification (if any)
matchArgs resolveAnon expected actual =
  -- This might seem backwards because the lists correspond to missing arguments, not given ones
  case length expected `compare` length actual of
    LT ->
      return $ Just $ RequiresArgs $ length actual - length expected
    GT ->
      return $ Just $ MustAcceptArgs $ length expected - length actual
    EQ -> do
      (actual, mismatches) <- runWriterT $ zipWithM unifyArg expected actual
      return $
        if getAny mismatches then
          Just $ GeneralMismatch expected actual
        else
          Nothing
  where
    unifyFail =
      tell $ Any True

    unifyArg (DataArg expVar expArg) (DataArg actVar actArg) = do
      var <- unifyVar expVar actVar
      args <-
        if length expArg == length actArg then
          zipWithM unifyArg expArg actArg
        else
          unifyFail >> return actArg
      return $ DataArg var args

    unifyVar (VAnon _) _ =
      error "matchArgs called with uninferred expected type"
    unifyVar VInvariant other =
      return other
    unifyVar exp (VAnon anon) = do
      lift $ resolveAnon exp anon
      return exp
    unifyVar exp act
      | act == exp = return exp
      | otherwise = unifyFail >> return act

-- | Adds constraints for a data type's variant
generateConstraints :: FilePath -> DataInfo -> Meta DataVariant -> Infer ()
generateConstraints file dataInfo Meta { unmeta = (_, types) } =
  forM_ types $ runMaybeT . inferTypeNoArg defaultConstraint
  where
    lookupNamed :: ExprKind -> Maybe Span -> String -> MaybeT Infer DataArg
    lookupNamed expected span name =
      case Map.lookup name dataInfo of
        Just (Just (eff, arg))
          | eff == expected -> return arg
          | otherwise -> MaybeT $ lift do
            addError CompileError
              { errorFile = Just file
              , errorSpan = span
              , errorKind = Error
              , errorMessage =
                show eff ++ " parameter `" ++ name ++ "` cannot be used as " ++ aOrAn (show expected) }
            return Nothing
        Just Nothing ->
          -- Indicates that there were multiple parameters with this name so nothing can be done
          MaybeT $ return Nothing
        Nothing -> MaybeT $ lift do
          addError CompileError
            { errorFile = Just file
            , errorSpan = span
            , errorKind = Error
            , errorMessage =
            "cannot find parameter `" ++ name ++ "` in scope, " ++
            if length name > 3 then
              -- Most type variables are short, so if it's longer than 3 characters it's probably wrong
              "did you mean to capitalize it?"
            else
              "did you forget to declare it?" }
          return Nothing

    matchArgs' :: Maybe Span -> [DataArg] -> [DataArg] -> MaybeT Infer ()
    matchArgs' actualSpan expected actual =
      matchArgs resolveAnon expected actual >>= \case
        Nothing -> return ()
        Just err -> MaybeT do
          lift $ addMatchError file actualSpan err
          return Nothing
      where
        resolveAnon exp anon =
          lift $ insertConstraint anon $ addStep exp defaultConstraint

    inferTypeNoArg :: VarianceConstraint -> Meta Type -> MaybeT Infer ()
    inferTypeNoArg c ty = do
      args <- inferType c ty
      matchArgs' (metaSpan ty) [] args

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
        TAnon _ -> MaybeT do
          lift $ addError CompileError
            { errorFile = Just file
            , errorSpan = metaSpan ty
            , errorKind = Error
            , errorMessage = "type in data type variant cannot be left blank" }
          return Nothing
        TApp a b ->
          inferType c a >>= \case
            [] -> MaybeT do
              runMaybeT $ inferType (addStep VInvariant c) b
              let (base, baseCount) = findBase a
              lift $ addError CompileError
                { errorFile = Just file
                , errorSpan = metaSpan b
                , errorKind = Error
                , errorMessage =
                "parameter `" ++ show base ++ "` " ++
                  if baseCount == 0 then
                    "does not accept any arguments"
                  else
                    "only accepts " ++ plural baseCount "argument" }
              return Nothing
            DataArg { argVariance, argParams } : rest -> lift do
              runMaybeT (inferType (addStep argVariance c) b) >>= \case
                Nothing -> return ()
                Just actual ->
                  void $ runMaybeT $ matchArgs' (metaSpan b) argParams actual
              return rest
        _ ->
          return []
      where
        matchEff effs argVariance =
          forM_ (setEffects $ unmeta effs) \eff ->
            case unmeta eff of
              EffectPoly name -> do
                arg <- lookupNamed KEffect (metaSpan eff) name
                lift $ insertConstraint (getAnon arg) effC
              EffectAnon _ -> lift $ lift $
                addError CompileError
                  { errorFile = Just file
                  , errorSpan = metaSpan eff
                  , errorKind = Error
                  , errorMessage = "effect in data type variant cannot be left blank" }
              _ -> return ()
          where
            effC = addStep argVariance c

-- | Describes the states a set of dependencies of an 'InferVariable' can have
data UnwrapState
  -- | There were no constraints added to the set
  = NoConstraints
  -- | There is a single constraint with no dependencies (@[]@)
  | FullyDetermined
  -- | There is some other set of constraints
  | NotInferred

-- | Tries to get a 'TypeVariance' out of an 'InferVariable' that is expected to be inferred
unwrapVariable :: InFile (Maybe Span) -> InferVariable -> Infer TypeVariance
unwrapVariable _ InvariantVariable = return VInvariant
unwrapVariable (file :/: span) InferVariable { outputVariables, inputVariables } =
  case (check outputVariables, check inputVariables) of
    (FullyDetermined, NoConstraints) -> return VOutput
    (NoConstraints, FullyDetermined) -> return VInput
    (NoConstraints, NoConstraints) -> do
      lift $ addError CompileError
        { errorFile = Just file
        , errorSpan = span
        , errorKind = Error
        , errorMessage =
          "cannot infer variance of unused parameter, use (+), (-), or _ instead" }
      return VInvariant
    (FullyDetermined, FullyDetermined) ->
      lift $ compilerBug "unwrapVariable called on unsimplified inference variable"
    _ ->
      lift $ compilerBug "unwrapVariable called on uninferrable inference variable"
  where
    check s =
      case Set.lookupMax s of
        Nothing -> NoConstraints
        Just [] -> FullyDetermined
        _ -> NotInferred

-- | Checks for occurances of even or odd numbers of lists with only self-references
checkSelfEvenOdd :: AnonCount -> (Bool, Bool) -> Set [AnonCount] -> (Bool, Bool)
checkSelfEvenOdd self = Set.foldr check
  where
    check _ status@(True, True) = status
    check xs status = checkEven xs status

    checkEven [] (_, odd) =
      (True, odd)
    checkEven (x:xs) status
      | x == self = checkOdd xs status
      | otherwise = status

    checkOdd [] (even, _) =
      (even, True)
    checkOdd (x:xs) status
      | x == self = checkEven xs status
      | otherwise = status

-- | Checks if an inference variable only refers to itself
onlyRefersToSelf :: AnonCount -> InferVariable -> Bool
onlyRefersToSelf _ InvariantVariable = True
onlyRefersToSelf self InferVariable { outputVariables, inputVariables } =
  Set.foldr check True $ Set.union outputVariables inputVariables
  where
    check _ False = False
    check xs _ = all (self ==) xs

-- | Normalizes an inference variable's constraint set for comparison
normalizeVariables :: Set [AnonCount] -> Set [AnonCount]
normalizeVariables = Set.map (simplifyRepeats . sort)
  where
    simplifyRepeats = \case
      (x : y : rest@(v : w : _))
        | x == y, y == v, v == w ->
          simplifyRepeats rest
      (x : y : rest@(z : _))
        | x == y, y == z ->
          simplifyRepeats rest
      other ->
        other

-- | Check whether the inference variable has completely disjoint sets of constraints
expensiveCheckDisjoint :: InferVariable -> Bool
expensiveCheckDisjoint InferVariable { outputVariables, inputVariables } =
  Set.disjoint (normalizeVariables outputVariables) (normalizeVariables inputVariables)

-- | An inference variable with its associated 'AnonCount'
type InferEntry = (AnonCount, InferVariable)

-- | Describes the possible results of trying to resolve a cycle
data CycleState
  -- | An invariant variable has been found, making the whole cycle invariant
  = CycleInvariant
  -- | There were no matches so the cycle is ambiguous
  | CycleNoMatches
  -- | There was a variable found that could be used to infer the rest of the variables
  | CycleMatchFound TypeVariance InferEntry [InferEntry]

-- | Tries to infer an 'SCC' of variables with constraints
inferConstraintSCC :: Map AnonCount (InFile (Maybe Span)) -> SCC InferEntry -> Infer ()
inferConstraintSCC anonMap scc = do
  s <- get
  let m = iResolvedVars s
  case scc of
    AcyclicSCC (anon, i) -> do
      var <- unwrapVariable (getLoc anon) $ substituteVars m i
      put s { iResolvedVars = Map.insert anon var m }
    CyclicSCC vars -> do
      failed <- inferFailed m vars []
      when failed $
        setResolved $ foldr (flip Map.insert VInvariant . fst) m vars
  where
    getLoc anon = mapGet anon anonMap

    setResolved m =
      modify \i -> i
        { iResolvedVars = m }

    checkForInvariant m = any (isInvariant . substituteVars m)
      where
        isInvariant = \case
          InvariantVariable -> True
          _ -> False

    inferFailed m [] toCheck =
      if checkForInvariant m toCheck then
        -- Although all constraints were solved, they are inconsistent so they must be invariant
        return True
      else do
        -- The constraints were all solved and they are consistent, so they should be used
        setResolved m
        return False
    inferFailed m vars toCheck =
      case inferCycle m vars [] of
        CycleInvariant ->
          return True
        CycleNoMatches -> do
          -- Emit an error about not being able to infer anything
          let
            (file :/: span) =
              getLoc $ case find (uncurry onlyRefersToSelf) vars of
                Just (anon, _) ->
                  -- If a variable only refers to itself, pick it because it is easier to fix
                  anon
                Nothing ->
                  -- Otherwise, just pick the first entry in the cycle
                  fst $ head vars
          lift $ addError CompileError
            { errorFile = Just file
            , errorSpan = span
            , errorKind = Error
            , errorMessage =
              "parameter is never used concretely so its variance cannot be inferred\n" ++
              "(consider removing the parameter if possible or using it concretely somewhere)" }
          return True
        CycleMatchFound var (anon, i) rest -> do
          inferFailed (Map.insert anon var m) rest (i : toCheck)

    inferCycle _ [] toCheck
      | not $ all (expensiveCheckDisjoint . snd) toCheck =
        -- There was an inference variable with a positive and negative version of the same constraint
        CycleInvariant
      | otherwise =
        -- There is nothing making it invariant and not enough information to make any guesses
        CycleNoMatches
    inferCycle m (var@(anon, i) : rest) toCheck = do
      case substituteVars m i of
        InvariantVariable -> CycleInvariant
        InferVariable { outputVariables, inputVariables } ->
          case ( fst $ checkSelfEvenOdd anon (False, True) outputVariables
               , checkSelfEvenOdd anon (False, False) inputVariables ) of
            (_, (_, True)) ->
              -- There is an odd input constraint, so the only possible solution is invariant
              CycleInvariant
            (True, (True, _)) ->
              -- The solution must be compatible with both input and output, so it must be invariant
              CycleInvariant
            (True, _) ->
              -- There was an even output constraint, so it is assumed to have output variance
              CycleMatchFound VOutput var rest
            (_, (True, _)) ->
              -- There was an even input constraint, so it is assumed to have input variance
              CycleMatchFound VInput var rest
            _ ->
              -- There was no useful information so look at the rest of the variables
              inferCycle m rest (var : toCheck)

