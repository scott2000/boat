-- | Infers variance information for data type declarations for use in type inference
module Analyze.InferVariance where

import Utility

import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Applicative
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

-- | Finds the data types used by each data type so they can be sorted
declDeps :: InFile DataDecl -> [Path]
declDeps =
  Set.toList . execWriter . mapM_ variantDeps . dataVariants . unfile
  where
    variantDeps = mapM_ typeDeps . snd . unmeta

    typeDeps ty =
      case unmeta ty of
        TAnyFuncArrow _ ->
          return ()
        TNamed _ name ->
          tell $ Set.singleton $ unmeta name
        TApp a b ->
          typeDeps a >> typeDeps b
        TForEff _ ty ->
          typeDeps ty
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
    _ ->
      error "addConstraint called with VAnon"

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
    iResolvedDecls :: !(PathMap DataDecl)
    -- | A map of declarations that are currently being resolved and aren't fully known
  , iUnresolvedDecls :: !(PathMap DataDecl)
    -- | A map of resolved inference variables that may be substituted
  , iResolvedVars :: !(Map AnonCount TypeVariance)
    -- | A map of unresolved inference variables that have yet to be substituted
  , iUnresolvedVars :: !(Map AnonCount InferVariable) }

-- | The default state with nothing inferred yet
defaultInferState :: InferState
defaultInferState = InferState
  { iResolvedDecls = pathMapEmpty
  , iUnresolvedDecls = pathMapEmpty
  , iResolvedVars = Map.empty
  , iUnresolvedVars = Map.empty }

-- | Removes the unneeded parameter names from a 'DataSig'
removeNames :: DataSig -> ([TypeVariance], [DataArg])
removeNames DataSig { dataEffects, dataArgs } =
  (map snd dataEffects, map snd dataArgs)

-- | Looks up a data type declaration's parameters using a provided lookup function
lookupDecl :: AddFatal m => (Path -> m (Maybe DataDecl)) -> Path -> m ([TypeVariance], [DataArg])
lookupDecl _ (Core (Operator "->")) =
  return ([VOutput], [DataArg VInput [], DataArg VOutput []])
lookupDecl lookup path = do
  lookup path >>= \case
    Just decl ->
      return $ removeNames $ dataSig decl
    Nothing ->
      compilerBug $ "lookupDecl couldn't find `" ++ show path ++ "`"

-- | Looks up a data type declaration's parameters
lookupDecl' :: Path -> Infer ([TypeVariance], [DataArg])
lookupDecl' = lookupDecl \path -> do
  InferState { iResolvedDecls, iUnresolvedDecls } <- get
  return $ pathMapLookup path iResolvedDecls <|> pathMapLookup path iUnresolvedDecls

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
      mapM_ inferDeclSCC $ topSort declDeps $ allDatas decls

-- | Infers variance information for a single 'SCC' of the graph of data types
inferDeclSCC :: SCC (ReversedPath, (Maybe Span, InFile DataDecl)) -> Infer ()
inferDeclSCC scc = do
  let anonMap = foldr addAnons Map.empty unresolvedList
  modify \i -> i
    { iUnresolvedDecls = unresolvedMap
    , iResolvedVars = Map.empty
    , iUnresolvedVars = Map.map (const emptyInferVariable) anonMap }
  forM_ unresolvedList \(_, (_, file :/: decl)) -> do
    dataInfo <- makeDataInfo file $ dataSig decl
    forM_ (dataVariants decl) $ generateConstraints file dataInfo
  unresolvedVars <- gets iUnresolvedVars
  if isSCCAcyclic scc then
    -- The SCC is acyclic so there cannot be cyclic constraints
    mapM_ (inferConstraintSCC anonMap . AcyclicSCC) $ Map.toList unresolvedVars
  else
    -- There may be cyclic constraints so a second sort is needed
    mapM_ (inferConstraintSCC anonMap) $ topSort variableDeps unresolvedVars
  resolvedVars <- gets iResolvedVars
  modify \i -> i
    { iResolvedDecls = foldr (addResolved resolvedVars) (iResolvedDecls i) unresolvedList }
  where
    unresolvedList = flattenSCC scc
    unresolvedMap = PathMap $ Map.fromList unresolvedList

    addAnons (_, (_, file :/: DataDecl { dataSig = DataSig { dataEffects, dataArgs } })) m =
      foldr addEff (foldr addArg m dataArgs) dataEffects
      where
        -- Ignore arguments that weren't specified by name
        addEff (name, VAnon var) = Map.insert var (file :/: metaSpan name)
        addEff _ = id
        addArg (UnnamedArg, _) = id
        addArg (name, arg) = Map.insert (getAnon arg) (file :/: metaSpan name)

    addResolved rvars (name, (span, file :/: decl)) =
      pathMapInsert' name (span, file :/: decl
        { dataSig = resDataSig $ dataSig decl })
      where
        resDataSig DataSig { dataEffects, dataArgs } = DataSig
          { dataEffects = map resEff dataEffects
          , dataArgs = map resArg dataArgs }
        resEff (name, VAnon var) = (name, mapGet var rvars)
        resEff eff = eff
        resArg (name, DataArg (VAnon var) args) = (name, DataArg (mapGet var rvars) args)
        resArg arg = arg

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
        addError compileError
          { errorFile = Just file
          , errorSpan = metaSpan
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
      "cannot pass type argument of kind `" ++ showKind actual ++ "`\n" ++
      "  to a type constructor expecting `" ++ showKind expected ++ "`"
    where
      showKind kindList = show DataArg
        { argVariance = VInvariant
        , argParams = kindList }

-- | Emits a 'MatchArgsError' in the given file at the given span
addMatchError :: AddError m => FilePath -> Maybe Span -> MatchArgsError -> m ()
addMatchError file span err =
  addError compileError
    { errorFile = Just file
    , errorSpan = span
    , errorKind =
      case err of
        GeneralMismatch _ _ ->
          -- Use a secondary error since this error is potentially complex and may be caused by a previous error
          SpecialError SecondaryError
        _ ->
          -- Basic errors such as forgetting an argument are simple to understand so use a primary error
          Error
    , errorCategory = Just ECInferVariance
    , errorMessage = show err }

-- | Matches the expected arguments with the actual arguments for a type
matchArgs :: AddFatal m
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
      compilerBug "matchArgs called with uninferred expected type"
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
  forM_ types $ inferTypeMatchArgs [] defaultConstraint []
  where
    lookupNamed :: ExprKind -> Maybe Span -> String -> MaybeT Infer DataArg
    lookupNamed expected span name =
      case mapGet name dataInfo of
        Just (actualKind, arg)
          | actualKind == expected -> return arg
          | otherwise -> MaybeT do
            addError compileError
              { errorFile = Just file
              , errorSpan = span
              , errorMessage =
                show actualKind ++ " parameter `" ++ name ++ "` cannot be used as " ++ aOrAn (show expected) }
            return Nothing
        Nothing ->
          -- Indicates that there were multiple parameters with this name so nothing can be done
          MaybeT $ return Nothing

    matchArgs' :: Maybe Span -> [DataArg] -> [DataArg] -> Infer ()
    matchArgs' actualSpan expected actual =
      matchArgs resolveAnon expected actual >>= \case
        Nothing -> return ()
        Just err ->
          addMatchError file actualSpan err
      where
        resolveAnon exp anon =
          insertConstraint anon $ addStep exp defaultConstraint

    inferTypeMatchArgs :: [String] -> VarianceConstraint -> [DataArg] -> Meta Type -> Infer ()
    inferTypeMatchArgs locals c args typeWithMeta = do
      runMaybeT (inferType locals c typeWithMeta) >>= \case
        Nothing ->
          return ()
        Just actual ->
          matchArgs' (metaSpan typeWithMeta) args actual

    inferType :: [String] -> VarianceConstraint -> Meta Type -> MaybeT Infer [DataArg]
    inferType locals c typeWithMeta =
      -- NOTE: A large portion of this code is similar to the type checking code in InferTypes
      case unmeta typeWithMeta of
        TNamed effs name -> do
          (dataEffects, dataArgs) <- lift $ lookupDecl' $ unmeta name
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
          zipWithM_ matchEff effs dataEffects
          return dataArgs
        TPoly name
          | name `elem` locals -> MaybeT do
            addError compileError
              { errorFile = Just file
              , errorSpan = metaSpan typeWithMeta
              , errorMessage = "quantified effect `" ++ name ++ "` cannot be used as a type" }
            return Nothing
          | otherwise -> do
            arg <- lookupNamed KType (metaSpan typeWithMeta) name
            lift $ insertConstraint (getAnon arg) c
            return $ argParams arg
        TAnon _ -> MaybeT do
          addError compileError
            { errorFile = Just file
            , errorSpan = metaSpan typeWithMeta
            , errorMessage = "type in data type variant cannot be left blank" }
          return Nothing
        TApp a b ->
          inferType locals c a >>= \case
            [] -> MaybeT do
              runMaybeT $ inferType locals (addStep VInvariant c) b
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
              inferTypeMatchArgs locals (addStep argVariance c) argParams b
              return rest
        TForEff e typeWithMeta -> do
          lift $ inferTypeMatchArgs (unmeta e : locals) c [] typeWithMeta
          return []
        _ ->
          return []
      where
        matchEff effs argVariance =
          forM_ (setEffects $ unmeta effs) \eff ->
            case unmeta eff of
              EffectPoly name
                | name `elem` locals -> return ()
                | otherwise -> do
                  arg <- lookupNamed KEffect (metaSpan eff) name
                  lift $ insertConstraint (getAnon arg) effC
              EffectAnon _ ->
                addError compileError
                  { errorFile = Just file
                  , errorSpan = metaSpan eff
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
      addError compileError
        { errorFile = Just file
        , errorSpan = span
        , errorCategory = Just ECInferVariance
        , errorExplain = Just $
          " Since this parameter is not used, it is not necessary to give it a name." ++
          " Instead, you can directly replace it with whichever variance you want it to have."
        , errorMessage =
          "cannot infer variance of unused parameter, use (+), (-), or _ instead" }
      return VInvariant
    (FullyDetermined, FullyDetermined) ->
      compilerBug "unwrapVariable called on unsimplified inference variable"
    _ ->
      compilerBug "unwrapVariable called on uninferrable inference variable"
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
expensiveCheckDisjoint InvariantVariable = False
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
          addError compileError
            { errorFile = Just file
            , errorSpan = span
            , errorCategory = Just ECInferVariance
            , errorExplain = Just $
              " The Boat compiler looks at how a parameter is used in order to determine its variance" ++
              " so that programs don't need to explicitly state it in most cases. However, in this case" ++
              " the parameter is never actually used directly in any data types (it is just being passed" ++
              " to another data type recursively). Because of this, the compiler doesn't have enough" ++
              " information to determine how the parameter is supposed to be used.\n\n" ++
              " If it is possible, remove the parameter from the data type or replace its uses in the" ++
              " data type variants with a specific type instead of a parameter. Otherwise, you may have" ++
              " to use it directly in some way in order to resolve this issue. One solution is to make a" ++
              " type like `data Phantom (+) = Phantom` that ignores its argument but gives it a variance" ++
              " and then add it as a parameter to a variant of the data type."
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

