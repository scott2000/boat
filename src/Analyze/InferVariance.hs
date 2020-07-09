-- | Infers variance information for data type declarations for use in type inference
module Analyze.InferVariance where

import Utility

import Data.List
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Control.Monad.Trans.Maybe

-- | A constraint that can be placed on a data type parameter
data VarianceConstraint = VarianceConstraint
  { vBase :: TypeVariance
  , vDeps :: [AnonCount] }

-- | The constraint given to parameters used directly in variants
defaultConstraint :: TypeVariance -> VarianceConstraint
defaultConstraint vBase = VarianceConstraint
  { vBase = vBase
  , vDeps = [] }

-- | Modifies a constraint to be contained in another constrained parameter
addStep :: TypeVariance -> VarianceConstraint -> VarianceConstraint
addStep (VAnon anon) cs =
  cs { vDeps = anon : vDeps cs }
addStep other cs =
  cs { vBase = other <> vBase cs }

-- | Finds the data types used by each data type so they can be sorted
declDeps :: (Path, Meta (InFile Span) DataDecl) -> [Path]
declDeps =
  HashSet.toList . execWriter . mapM_ variantDeps . dataVariants . unmeta . snd
  where
    variantDeps = mapM_ typeDeps . snd . unmeta

    typeDeps ty =
      case unmeta ty of
        TFuncArrow ->
          return ()
        TNamed name ->
          tell $ HashSet.singleton name
        TApp a b ->
          typeDeps a >> typeDeps b
        TEffApp ty _ ->
          typeDeps ty
        TForEff _ ty ->
          typeDeps ty
        _ ->
          return ()

-- | A record of the constraints placed on a given inference variable
data InferVariable
  = InvariantVariable
  | InferVariable
    { outputVariables :: HashSet [AnonCount]
    , inputVariables :: HashSet [AnonCount] }

-- | An inference variable with no constraints
emptyInferVariable :: InferVariable
emptyInferVariable = InferVariable
  { outputVariables = HashSet.empty
  , inputVariables = HashSet.empty }

-- | Adds a constraint to an inference variable
addConstraint :: VarianceConstraint -> InferVariable -> InferVariable
addConstraint _ InvariantVariable = InvariantVariable
addConstraint VarianceConstraint { vBase, vDeps } i =
  case vBase of
    VOutput
      | null vDeps && HashSet.member [] (inputVariables i) ->
        InvariantVariable
      | otherwise ->
        i { outputVariables = HashSet.insert vDeps $ outputVariables i }
    VInput
      | null vDeps && HashSet.member [] (outputVariables i) ->
        InvariantVariable
      | otherwise ->
        i { inputVariables = HashSet.insert vDeps $ inputVariables i }
    VInvariant ->
      InvariantVariable
    _ ->
      error "addConstraint called with VAnon"

-- | Find the inference variables that constraint a given variable
variableDeps :: (AnonCount, InferVariable) -> [AnonCount]
variableDeps (_, InvariantVariable) = []
variableDeps (_, InferVariable { outputVariables, inputVariables }) =
  HashSet.toList $ add outputVariables $ add inputVariables $ HashSet.empty
  where
    add vars s = foldr (HashSet.union . HashSet.fromList) s vars

-- | Makes a new 'InferVariable', but simplifies conflicting constraints to be invariant
simplifyInferVariable :: HashSet [AnonCount] -> HashSet [AnonCount] -> InferVariable
simplifyInferVariable outputVariables inputVariables
  | [] `HashSet.member` outputVariables && [] `HashSet.member` inputVariables = InvariantVariable
  | otherwise = InferVariable { outputVariables, inputVariables }

-- | Substitutes a set of inferred variables into a set of constraints
substituteVars :: HashMap AnonCount TypeVariance -> InferVariable -> InferVariable
substituteVars _ InvariantVariable = InvariantVariable
substituteVars m InferVariable { outputVariables, inputVariables } =
  foldr updateConstraint emptyInferVariable $
    getConstraints VOutput outputVariables ++ getConstraints VInput inputVariables
  where
    getConstraints var s =
      HashSet.toList s <&> \list -> VarianceConstraint
        { vBase = var
        , vDeps = list }

    updateConstraint VarianceConstraint { vBase, vDeps } =
      addConstraint $ foldr sub VarianceConstraint { vBase, vDeps = [] } vDeps
      where
        sub anon c =
          let
            step =
              case HashMap.lookup anon m of
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
  , iResolvedVars :: !(HashMap AnonCount TypeVariance)
    -- | A map of unresolved inference variables that have yet to be substituted
  , iUnresolvedVars :: !(HashMap AnonCount InferVariable) }

-- | The default state with nothing inferred yet
defaultInferState :: InferState
defaultInferState = InferState
  { iResolvedDecls = HashMap.empty
  , iUnresolvedDecls = HashMap.empty
  , iResolvedVars = HashMap.empty
  , iUnresolvedVars = HashMap.empty }

-- | Looks up a data type declaration's parameters using a provided lookup function
lookupDecl :: AddFatal m => (Path -> m (Maybe (Meta (InFile Span) DataDecl))) -> Path -> m TypeKind
lookupDecl _ (Core (Operator "->")) =
  return TypeKind
    { kindEffs = [VOutput]
    , kindArgs =
      [ NullaryArg VInput
      , NullaryArg VOutput ] }
lookupDecl lookup path = do
  lookup path >>= \case
    Just decl ->
      return $ dataSigToTypeKind $ dataSig $ unmeta decl
    Nothing ->
      compilerBug $ "lookupDecl couldn't find `" ++ show path ++ "`"

-- | Looks up a data type declaration's parameters
lookupDecl' :: Path -> Infer TypeKind
lookupDecl' = lookupDecl \path -> do
  InferState { iResolvedDecls, iUnresolvedDecls } <- get
  return $ HashMap.lookup path iResolvedDecls <|> HashMap.lookup path iUnresolvedDecls

-- | Inserts a new constraint to an inference variable
insertConstraint :: AnonCount -> VarianceConstraint -> Infer ()
insertConstraint anon c =
  modify \i -> i
    { iUnresolvedVars = HashMap.adjust (addConstraint c) anon $ iUnresolvedVars i }

-- | Infers variance information for the parameters of every data type declaration
inferVariance :: AllDecls -> CompileIO AllDecls
inferVariance decls = do
  i <- execStateT runInfer defaultInferState
  return decls { allDatas = iResolvedDecls i }
  where
    runInfer =
      mapM_ inferDeclSCC $ topSort declDeps $ allDatas decls

-- | Infers variance information for a single 'SCC' of the graph of data types
inferDeclSCC :: SCC (Path, Meta (InFile Span) DataDecl) -> Infer ()
inferDeclSCC scc = do
  let anonMap = foldr addAnons HashMap.empty unresolvedList
  modify \i -> i
    { iUnresolvedDecls = unresolvedMap
    , iResolvedVars = HashMap.empty
    , iUnresolvedVars = HashMap.map (const emptyInferVariable) anonMap }
  forM_ unresolvedList \(_, decl :&: file :/: _) -> do
    dataInfo <- makeDataInfo file $ dataSig decl
    forM_ (dataVariants decl) $ generateConstraints file dataInfo
  unresolvedVars <- gets iUnresolvedVars
  if isSCCAcyclic scc then
    -- The SCC is acyclic so there cannot be cyclic constraints
    mapM_ (inferConstraintSCC anonMap . AcyclicSCC) $ HashMap.toList unresolvedVars
  else
    -- There may be cyclic constraints so a second sort is needed
    mapM_ (inferConstraintSCC anonMap) $ topSort variableDeps unresolvedVars
  resolvedVars <- gets iResolvedVars
  modify \i -> i
    { iResolvedDecls = foldr (addResolved resolvedVars) (iResolvedDecls i) unresolvedList }
  where
    unresolvedList = flattenSCC scc
    unresolvedMap = HashMap.fromList unresolvedList

    addAnons (_, DataDecl { dataSig = DataSig { dataEffs, dataArgs } } :&: file :/: _) m =
      foldr addEff (foldr addArg m dataArgs) dataEffs
      where
        -- Ignore arguments that weren't specified by name
        addEff (_ :&: span, VAnon var) = HashMap.insert var (file :/: span)
        addEff _ = id
        addArg (UnnamedArg, _) = id
        addArg (_ :&: span, arg) = HashMap.insert (getAnon arg) (file :/: span)

    addResolved rvars (name, decl :&: info) =
      HashMap.insert name $ withInfo info decl
        { dataSig = resDataSig $ dataSig decl }
      where
        resDataSig DataSig { dataEffs, dataArgs } = DataSig
          { dataEffs = map resEff dataEffs
          , dataArgs = map resArg dataArgs }
        resEff (name, VAnon var) = (name, hashMapGet var rvars)
        resEff eff = eff
        resArg (name, DataArg (VAnon var) args) = (name, DataArg (hashMapGet var rvars) args)
        resArg arg = arg

-- | Information about all parameters of a data type declaration
type DataInfo = HashMap String (Maybe (ExprKind, DataArg))

-- | Constructs a 'DataInfo' map from a 'DataSig'
makeDataInfo :: AddError m => FilePath -> DataSig -> m DataInfo
makeDataInfo file DataSig { dataEffs, dataArgs } =
  execStateT addAll HashMap.empty
  where
    addAll = do
      forM_ dataEffs \(name, variance) ->
        add name $ Just (KEffect, NullaryArg variance)
      forM_ dataArgs \(name, arg) ->
        add name $ Just (KType, arg)

    add UnnamedArg _ = return ()
    add (name :&: span) info = do
      m <- get
      if HashMap.member name m then do
        addError compileError
          { errorFile = file
          , errorSpan = span
          , errorMessage = "the name `" ++ name ++ "` has already been taken by another parameter" }
        put $ HashMap.insert name Nothing m
      else
        put $ HashMap.insert name info m

-- | Gets the 'AnonCount' of an uninferred parameter
getAnon :: DataArg -> AnonCount
getAnon DataArg { argVariance = VAnon anon } = anon
getAnon _ = error "getAnon called with inferred variance"

-- | Represents an error from 'matchKinds'
data MatchKindsError
  = RequiresArgs Int
  | MustAcceptArgs ExprKind Int
  | GeneralMismatch TypeKind TypeKind

instance Show MatchKindsError where
  show = \case
    RequiresArgs n ->
      "type requires " ++ plural n "more argument"
    MustAcceptArgs kind n ->
      "type must accept " ++ plural n ("more " ++ show kind ++ " argument")
    GeneralMismatch expected actual ->
      "cannot pass type argument of kind `" ++ show actual ++ "`\n" ++
      "  to a type constructor expecting `" ++ show expected ++ "`"

-- | Emits a 'MatchKindsError' in the given file at the given span
addMatchError :: AddError m => FilePath -> Span -> MatchKindsError -> m ()
addMatchError file span err =
  addError compileError
    { errorFile = file
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
matchKinds :: Monad m
           => (TypeVariance -> AnonCount -> m ()) -- ^ Specifies what to do for uninferred variance
           -> TypeKind                            -- ^ The arguments that the type is expected to accept
           -> TypeKind                            -- ^ The arguments that the type actually accepts
           -> m (Maybe MatchKindsError)           -- ^ The error produced by unification (if any)
matchKinds resolveAnon expected@(TypeKind eEffs eArgs) (TypeKind aEffs aArgs) =
  -- This might seem backwards because the lists correspond to missing arguments, not given ones
  if length eEffs > length aEffs then
    return $ Just $ MustAcceptArgs KEffect $ length eEffs - length aEffs
  else
    case length eArgs `compare` length aArgs of
      LT ->
        return $ Just $ RequiresArgs $ length aArgs - length eArgs
      GT ->
        return $ Just $ MustAcceptArgs KType $ length eArgs - length aArgs
      EQ -> do
        (actual, mismatches) <- runWriterT $
          TypeKind <$> zipWithM unifyVar eEffs aEffs <*> zipWithM unifyArg eArgs aArgs
        return $
          if getAny mismatches then
            Just $ GeneralMismatch expected actual
          else
            Nothing
  where
    unifyFail =
      tell $ Any True

    unifyArg (DataArg expVar (TypeKind eEffs eArgs)) (DataArg actVar actual@(TypeKind aEffs aArgs)) = do
      var <- unifyVar expVar actVar
      kind <-
        if length eEffs <= length aEffs && length eArgs == length aArgs then
          TypeKind <$> zipWithM unifyVar eEffs aEffs <*> zipWithM unifyArg eArgs aArgs
        else
          unifyFail >> return actual
      return $ DataArg var kind

    unifyVar (VAnon _) _ =
      error "matchKinds called with uninferred expected type"
    unifyVar VInvariant other =
      return other
    unifyVar exp (VAnon anon) = do
      lift $ resolveAnon exp anon
      return exp
    unifyVar exp act
      | act == exp = return exp
      | otherwise = unifyFail >> return act

-- | Adds constraints for a data type's variant
generateConstraints :: FilePath -> DataInfo -> Meta Span DataVariant -> Infer ()
generateConstraints file dataInfo ((_, types) :&: _) =
  forM_ types $ inferTypeMatchKinds [] (defaultConstraint VOutput) NullaryKind
  where
    lookupNamed :: ExprKind -> Span -> String -> MaybeT Infer DataArg
    lookupNamed expected span name =
      case hashMapGet name dataInfo of
        Just (actualKind, arg)
          | actualKind == expected -> return arg
          | otherwise -> MaybeT do
            addError compileError
              { errorFile = file
              , errorSpan = span
              , errorMessage =
                show actualKind ++ " parameter `" ++ name ++ "` cannot be used as " ++ aOrAn (show expected) }
            return Nothing
        Nothing ->
          -- Indicates that there were multiple parameters with this name so nothing can be done
          MaybeT $ return Nothing

    matchKinds' :: Span -> TypeKind -> TypeKind -> Infer ()
    matchKinds' actualSpan expected actual =
      matchKinds resolveAnon expected actual >>= \case
        Nothing -> return ()
        Just err ->
          addMatchError file actualSpan err
      where
        resolveAnon exp anon =
          insertConstraint anon $ addStep exp $ defaultConstraint VOutput

    inferTypeMatchKinds :: [String] -> VarianceConstraint -> TypeKind -> MetaR Span Type -> Infer ()
    inferTypeMatchKinds locals c args typeWithMeta = do
      runMaybeT (inferType locals c typeWithMeta) >>= \case
        Nothing ->
          return ()
        Just actual ->
          matchKinds' (getSpan typeWithMeta) args actual

    inferType :: [String] -> VarianceConstraint -> MetaR Span Type -> MaybeT Infer TypeKind
    inferType locals c typeWithMeta =
      -- NOTE: A large portion of this code is similar to the type checking code in InferTypes
      case unmeta typeWithMeta of
        TNamed name ->
          lift $ lookupDecl' name
        TPoly name
          | name `elem` locals -> MaybeT do
            addError compileError
              { errorFile = file
              , errorSpan = getSpan typeWithMeta
              , errorMessage = "quantified effect `" ++ name ++ "` cannot be used as a type" }
            return Nothing
          | otherwise -> do
            arg <- lookupNamed KType (getSpan typeWithMeta) name
            lift $ insertConstraint (getAnon arg) c
            return $ argKind arg
        TAnon _ -> MaybeT do
          addError compileError
            { errorFile = file
            , errorSpan = getSpan typeWithMeta
            , errorMessage = "type in data type variant cannot be left blank" }
          return Nothing
        TApp a b -> do
          TypeKind effs args <- inferType locals c a
          case args of
            [] -> MaybeT do
              runMaybeT $ inferType locals (defaultConstraint VInvariant) b
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
              inferTypeMatchKinds locals (addStep argVariance c) argKind b
              return $ TypeKind effs rest
        TEffApp ty e -> do
          TypeKind effs args <- inferType locals c ty
          case effs of
            [] -> MaybeT do
              runMaybeT $ matchEff e $ defaultConstraint VInvariant
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
              runMaybeT $ matchEff e $ addStep argVariance c
              return $ TypeKind rest args
        TForEff e typeWithMeta -> do
          lift $ inferTypeMatchKinds (unmeta e : locals) c NullaryKind typeWithMeta
          return NullaryKind
        _ ->
          return NullaryKind
      where
        matchEff effs c =
          forM_ (setEffects $ unmeta effs) \eff ->
            case unmeta eff of
              EffectPoly name
                | name `elem` locals -> return ()
                | otherwise -> do
                  arg <- lookupNamed KEffect (getSpan eff) name
                  lift $ insertConstraint (getAnon arg) c
              EffectAnon _ ->
                addError compileError
                  { errorFile = file
                  , errorSpan = getSpan eff
                  , errorMessage = "effect in data type variant cannot be left blank" }
              _ -> return ()

-- | Describes the states a set of dependencies of an 'InferVariable' can have
data UnwrapState
  -- | There were no constraints added to the set
  = NoConstraints
  -- | There is a single constraint with no dependencies (@[]@)
  | FullyDetermined
  -- | There is some other set of constraints
  | NotInferred

-- | Tries to get a 'TypeVariance' out of an 'InferVariable' that is expected to be inferred
unwrapVariable :: InFile Span -> InferVariable -> Infer TypeVariance
unwrapVariable _ InvariantVariable = return VInvariant
unwrapVariable (file :/: span) InferVariable { outputVariables, inputVariables } =
  case (check outputVariables, check inputVariables) of
    (FullyDetermined, NoConstraints) -> return VOutput
    (NoConstraints, FullyDetermined) -> return VInput
    (NoConstraints, NoConstraints) -> do
      addError compileError
        { errorFile = file
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
      case HashSet.toList s of
        []   -> NoConstraints
        [[]] -> FullyDetermined
        _    -> NotInferred

-- | Checks for occurances of even or odd numbers of lists with only self-references
checkSelfEvenOdd :: AnonCount -> (Bool, Bool) -> HashSet [AnonCount] -> (Bool, Bool)
checkSelfEvenOdd self = HashSet.foldr check
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
  HashSet.foldr check True $ outputVariables <> inputVariables
  where
    check _ False = False
    check xs _ = all (self ==) xs

-- | Normalizes an inference variable's constraint set for comparison
normalizeVariables :: HashSet [AnonCount] -> HashSet [AnonCount]
normalizeVariables = HashSet.map (simplifyRepeats . sort)
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
  HashSet.null $ HashSet.intersection (normalizeVariables outputVariables) (normalizeVariables inputVariables)

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
inferConstraintSCC :: HashMap AnonCount (InFile Span) -> SCC InferEntry -> Infer ()
inferConstraintSCC anonMap scc = do
  s <- get
  let m = iResolvedVars s
  case scc of
    AcyclicSCC (anon, i) -> do
      var <- unwrapVariable (getLoc anon) $ substituteVars m i
      put s { iResolvedVars = HashMap.insert anon var m }
    CyclicSCC vars -> do
      failed <- inferFailed m vars []
      when failed $
        setResolved $ foldr (flip HashMap.insert VInvariant . fst) m vars
  where
    getLoc anon = hashMapGet anon anonMap

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
            { errorFile = file
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
          inferFailed (HashMap.insert anon var m) rest (i : toCheck)

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

