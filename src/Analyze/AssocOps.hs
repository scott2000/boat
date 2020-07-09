-- | Associates all operators based on their declared precedence relations and associativities
module Analyze.AssocOps where

import Utility

import Data.List
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

-- | 'StateT' for storing information about the operator type graph
type Assoc = StateT AssocState CompileIO

-- | Each vertex in the graph is represented by its index in the sequence
type Vertex = Int

-- | The graph is stored as a set of lower precedence vertices for each vertex
type Graph = Seq IntSet

-- | Stores information about which operator types are lower in precedence than others
data AssocState = AssocState
  { -- | Directed acyclic graph describing the ordering between each vertex
    assocGraph :: Graph
    -- | Map from operator type path to its vertex in the graph
  , assocPaths :: HashMap Path Vertex }

-- | An 'AssocState' with no operator types
defaultAssocState :: AssocState
defaultAssocState = AssocState
  { assocGraph = Seq.empty
  , assocPaths = HashMap.empty }

-- | Associates all operators in every expression based on their operator types
assocOps :: AllDecls -> CompileIO AllDecls
assocOps decls = do
  opTypes <- getSortedAcyclic decls
  exitIfErrors
  assocState <- execStateT (mapM_ addToGraph opTypes) defaultAssocState
  exitIfErrors
  updateExprs assocState decls

-- | Adds a path to the graph and returns the index where the vertex will be added
addPath :: Path -> Assoc Vertex
addPath path = do
  s <- get
  let index = Seq.length $ assocGraph s
  put s { assocPaths = HashMap.insert path index $ assocPaths s }
  return index

-- | Looks up a path and returns the index of the vertex
lookupPath :: Path -> Assoc Vertex
lookupPath path =
  hashMapGet path <$> gets assocPaths

-- | Adds a vertex to the graph with a set of lower precedence vertices
addVertex :: IntSet -> Assoc ()
addVertex v = modify \s -> s
  { assocGraph = assocGraph s |> v }

-- | Updates the set of lower precedence vertices for a given vertex
updateVertex :: Vertex -> (IntSet -> IntSet) -> Assoc ()
updateVertex index f = modify \s -> s
  { assocGraph = Seq.adjust' f index $ assocGraph s }

-- | Finds the ordering between two vertices in a graph, if it exists
checkVertexOrdering :: Graph -> Vertex -> Vertex -> Maybe Ordering
checkVertexOrdering graph a b =
  if a == b then
    Just EQ
  else if a <: b then
    Just LT
  else if b <: a then
    Just GT
  else
    Nothing
  where
    (<:) target = go
      where
        go index
          | index == target = True
          | otherwise =
            IntSet.foldl' goAll False $ Seq.index graph index
        goAll a b = a || go b

-- | Sorts the operator types into the order they should be added to the graph
getSortedAcyclic :: AllDecls -> CompileIO [(Path, Meta (InFile Span) OpTypeEnds)]
getSortedAcyclic AllDecls { allOpTypes } =
  checkForCycles $ topSort concatEnds allOpTypes
  where
    concatEnds (_, ends :&: _) =
      case ends of
        (Nothing, Nothing) -> []
        (Nothing, Just b)  -> [unmeta b]
        (Just a,  Nothing) -> [unmeta a]
        (Just a,  Just b)  -> [unmeta a, unmeta b]

    checkForCycles = \case
      [] ->
        return []
      AcyclicSCC node : rest ->
        (node :) <$> checkForCycles rest
      CyclicSCC nodes : rest -> do
        let
          (_, _ :&: file :/: span) = head nodes
          nodeList =
            intercalate ", " $ map (show . fst) nodes
        addError compileError
          { errorFile = file
          , errorSpan = span
          , errorCategory = [ECAssocOps]
          , errorExplain = Just $
            " The links to other operator types in an operator type declaration cannot rely on any of" ++
            " the operator types currently being defined in their definitions. If this were allowed," ++
            " it would be possible to make a loop of operator precedences where an operator is both above" ++
            " and below another operator in precedence, which would be ambiguous. Make sure that each" ++
            " operator type declaration only links to previously defined operator types."
          , errorMessage =
            " cyclic dependencies for operator type declarations\n" ++
            " (nodes in cycle: " ++ nodeList ++ ")" }
        checkForCycles rest

-- | Adds a new operator type declaration to the graph
addToGraph :: (Path, Meta (InFile Span) OpTypeEnds) -> Assoc ()
addToGraph (path, ends :&: file :/: span) =
  case ends of
    (Nothing, Nothing) -> do
      addPath path
      addVertex IntSet.empty
    (Nothing, Just (higher :&: _)) -> do
      index <- addPath path
      higherVertex <- lookupPath higher
      updateVertex higherVertex $ IntSet.insert index
      addVertex IntSet.empty
    (Just (lower :&: _), Nothing) -> do
      addPath path
      lowerVertex <- lookupPath lower
      addVertex $ IntSet.singleton lowerVertex
    (Just (lower :&: _), Just (higher :&: _)) -> do
      lowerVertex <- lookupPath lower
      higherVertex <- lookupPath higher
      graph <- gets assocGraph
      let
        ordering = checkVertexOrdering graph lowerVertex higherVertex
        showLast = show . last . unpath
        l = showLast lower
        h = showLast higher
        p = showLast path
        showErr msg =
          addFatal compileError
            { errorFile = file
            , errorSpan = span
            , errorCategory = [ECAssocOps]
            , errorExplain = Just $
              " When specifying the precedence of an operator type, an upper and lower bound may be" ++
              " specified by placing them in parentheses. These upper and lower bounds must already" ++
              " have an established ordering between them if they are both included, and the upper" ++
              " bound must have higher precedence than the lower bound. This ensures that if you don't" ++
              " specify the relative ordering of two operator types, that they will never have a" ++
              " defined ordering between them."
            , errorMessage = ' ' : msg
              ++ ", so `" ++ p ++ "` cannot be added in between" }
      case ordering of
        Nothing ->
          showErr $
            "there is no existing ordering between `" ++ l ++ "` and `" ++ h ++ "`"
        Just GT ->
          showErr $
            "the precedence of `" ++ l ++  "` is greater than that of `" ++ h ++ "`"
        Just EQ ->
          showErr $
            "the upper and lower link are both `" ++ l ++ "` (the same precedence)"
        Just LT -> do
          index <- addPath path
          updateVertex higherVertex $
            IntSet.insert index . IntSet.delete lowerVertex
          addVertex $ IntSet.singleton lowerVertex

-- | Updates all expressions using the precedence graph created from the operator types
updateExprs :: AssocState -> AllDecls -> CompileIO AllDecls
updateExprs
  AssocState { assocGraph, assocPaths }
  decls@AllDecls { allOpDecls }
  = do
    allDatas <- mapM updateData $ allDatas decls
    allLets <- mapM updateLet $ allLets decls
    return decls { allDatas, allLets }
    where
      comparePaths :: Path -> Path -> Maybe Ordering
      comparePaths a b =
        checkVertexOrdering assocGraph (v a) (v b)
        where
          v path = hashMapGet path assocPaths

      allow :: ContainsOp a => FilePath -> Maybe (Meta Span Path) -> Meta Span a -> MaybeT CompileIO Bool
      allow file current next =
        case current of
          Nothing ->
            return True
          Just current ->
            case ( HashMap.lookup (unmeta current) allOpDecls
                 , getPath next >>= \next -> HashMap.lookup (unmeta next) allOpDecls ) of
              (Nothing, Nothing) -> MaybeT do
                missing current
                missing next
                return Nothing
              (Nothing, _) -> MaybeT do
                missing current
                return Nothing
              (_, Nothing) -> MaybeT do
                missing next
                return Nothing
              (Just (a :&: _), Just (b :&: _)) ->
                let
                  aOp = unmeta $ opType a
                  bOp = unmeta $ opType b
                in case comparePaths aOp bOp of
                  Nothing -> notAllowed $
                    "there is no established precedence between `" ++ show aOp
                    ++ "` and `" ++ show bOp ++ "`"
                  Just GT -> return False
                  Just LT -> return True
                  Just EQ ->
                    case (opAssoc a, opAssoc b) of
                      (ALeft, ALeft)   -> return False
                      (ARight, ARight) -> return True
                      (ANon, ANon) -> notAllowed $
                        "operators `" ++ show aOp ++ "` and `" ++ show bOp
                        ++ "` are non-associative, so explicit grouping is required"
                      (aAssoc, bAssoc) -> notAllowed $
                        "operator `" ++ show bOp
                        ++ "` has a different associativity than `" ++ show aOp
                        ++ "` (" ++ show aAssoc ++ " != " ++ show bAssoc ++ ")"
        where
          notAllowed msg = MaybeT do
            addError compileError
              { errorFile = file
              , errorSpan = getSpan next
              , errorCategory = [ECAssocOps]
              , errorMessage = ' ' : msg
                ++ ", so explicit grouping is required" }
            return Nothing
          missing (path :&: span) =
            addError compileError
              { errorFile = file
              , errorSpan = span
              , errorCategory = [ECAssocOps]
              , errorMessage =
                " operator `" ++ show path ++ "` has not been assigned an operator precedence," ++
                " so explicit grouping is required" }

      unwrap :: MaybeT CompileIO a -> CompileIO a
      unwrap m = runMaybeT m >>= \case
        Nothing -> do
          exitIfErrors
          compilerBug "unwrapping associated operator list failed despite no errors being reported"
        Just x -> return x

      getNext :: Monad m => StateT [a] m a
      getNext = do
        s <- get
        let h : t = s
        put t
        return h

      associateList :: FilePath -> Associator CompileIO
      associateList file list =
        unwrap $ evalStateT (goExpr Nothing) list
        where
          goExpr current = do
            next <- getNext
            a <- case next of
              UnOp unaryOp ->
                applyUnary unaryOp <$> goExpr (getPath unaryOp)
              UnExpr expr ->
                return expr
            goBin current a
          goBin current a =
            get >>= \case
              [] ->
                return a
              (UnOp binaryOp) : rest -> do
                allowed <- lift $ allow file current binaryOp
                if allowed then do
                  put rest
                  b <- goExpr $ getPath binaryOp
                  goBin current (applyBinary binaryOp a b)
                else
                  return a
              _ ->
                compilerBug "associateList: operator found at end of list"

      updateSome file = reassociate $ associateList file

      updateData :: Meta (InFile Span) DataDecl -> CompileIO (Meta (InFile Span) DataDecl)
      updateData (decl :&: file :/: span) = do
        variants <- mapM (mapM updateVariant) $ dataVariants decl
        return $ decl { dataVariants = variants } :&: file :/: span
        where
          updateVariant (name, types) =
            (,) name <$> mapM (updateSome file) types

      updateLet :: Meta (InFile Span) LetDecl -> CompileIO (Meta (InFile Span) LetDecl)
      updateLet (decl :&: file :/: span) = do
        letTypeAscription <- mapM (updateSome file) $ letTypeAscription decl
        letBody <- updateSome file $ letBody decl
        return $ decl { letTypeAscription, letBody } :&: file :/: span

-- | A type of function that can reassociate a list of unassociated expressions
type Associator m = forall t. ContainsOp t => [UnOpOrExpr t] -> m (Meta Span t)

-- | Represents a part in a list of unassociated expressions
data UnOpOrExpr a
  -- | An operator (either infix or unary)
  = UnOp (Meta Span a)
  -- | An expression that will be given to an operator
  | UnExpr (Meta Span a)

-- | A class representing anything that contains infix expressions
class (Show a, After a) => ContainsOp a where
  -- | Convert the expression to a list of unassociated expressions
  toUnOpList :: Meta Span a -> [UnOpOrExpr a]
  -- | Strip any leading parentheses
  stripParen :: Meta Span a -> Meta Span a
  -- | Get the 'Path' if this is a global identifier
  getPath :: Meta Span a -> Maybe (Meta Span Path)
  -- | Apply a unary operator to an expression
  applyUnary :: Meta Span a -> Meta Span a -> Meta Span a
  -- | Apply a binary operator to two expressions
  applyBinary :: Meta Span a -> Meta Span a -> Meta Span a -> Meta Span a

-- | Like 'toUnOpList', but takes an 'Unassociated' instead
uToUnOpList :: ContainsOp a => Unassociated Span a -> [UnOpOrExpr a]
uToUnOpList = \case
  UParen op ->
    [UnExpr op]
  UUnaryOp op rhs ->
    UnOp op : toUnOpList rhs
  UBinOp op lhs rhs ->
    UnExpr lhs : UnOp op : toUnOpList rhs

-- | Using an 'Associator', fully associate all infix expressions
reassociate :: (ContainsOp a, Monad m) => Associator m -> Meta Span a -> m (Meta Span a)
reassociate f = after $ aContainsOp (f . toUnOpList . stripParen)
  where
    aContainsOp :: Monad m
                => (forall a. ContainsOp a => Meta Span a -> m (Meta Span a))
                -> AfterMap m
    aContainsOp f = aDefault
      { aExpr = f
      , aPattern = f
      , aType = f }

instance ContainsOp (Type Span) where
  toUnOpList x =
    case unmeta x of
      TUnassociated u ->
        uToUnOpList u
      _ ->
        [UnExpr x]

  stripParen x =
    case unmeta x of
      TUnassociated (UParen op) ->
        stripParen op
      _ ->
        x

  getPath = \case
    TNamed path :&: span ->
      Just $ path :&: span
    _ ->
      Nothing

  applyUnary op rhs =
    withEnds op rhs $ TApp op rhs

  applyBinary op lhs rhs =
    withEnds lhs rhs $
      TApp (withEnds lhs op $ TApp op lhs) rhs

instance ContainsOp (Expr Span) where
  toUnOpList x =
    case unmeta x of
      EUnassociated u ->
        uToUnOpList u
      _ ->
        [UnExpr x]

  stripParen x =
    case unmeta x of
      EUnassociated (UParen op) ->
        stripParen op
      _ ->
        x

  getPath = \case
    EGlobal path :&: span ->
      Just $ path :&: span
    _ ->
      Nothing

  applyUnary op rhs =
    withEnds op rhs $ EApp op rhs

  applyBinary op lhs rhs =
    withEnds lhs rhs $
      EApp (withEnds lhs op $ EApp op lhs) rhs

instance ContainsOp (Pattern Span) where
  toUnOpList x =
    case unmeta x of
      PUnassociated u ->
        uToUnOpList u
      _ ->
        [UnExpr x]

  stripParen x =
    case unmeta x of
      PUnassociated (UParen op) ->
        stripParen op
      _ ->
        x

  getPath = \case
    PCons path [] :&: _ ->
      Just path
    _ ->
      Nothing

  applyUnary (PCons op [] :&: _) rhs =
    withEnds op rhs $ PCons op [rhs]
  applyUnary _ _ =
    error "applyUnary called with local variable"

  applyBinary (PCons op [] :&: _) lhs rhs =
    withEnds lhs rhs $ PCons op [lhs, rhs]
  applyBinary _ _ _ =
    error "applyBinary called with local variable"

