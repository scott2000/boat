-- | Associates all operators based on their declared precedence relations and associativities
module Analyze.AssocOps where

import Utility

import Data.List
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Trans.Maybe

import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
  , assocPaths :: Map (Meta Path) (InFile Vertex) }

-- | An 'AssocState' with no operator types
defaultAssocState :: AssocState
defaultAssocState = AssocState
  { assocGraph = Seq.empty
  , assocPaths = Map.empty }

-- | Associates all operators in every expression based on their operator types
assocOps :: AllDecls -> CompileIO AllDecls
assocOps decls = do
  opTypes <- getSortedAcyclic decls
  exitIfErrors
  assocState <- execStateT (mapM_ addToGraph opTypes) defaultAssocState
  exitIfErrors
  updateExprs assocState decls

-- | Adds a path to the graph and returns the index where the vertex will be added
addPath :: Meta Path -> FilePath -> Assoc Vertex
addPath path file = do
  s <- get
  let index = Seq.length $ assocGraph s
  put s { assocPaths = Map.insert path (file :/: index) $ assocPaths s }
  return index

-- | Looks up a path and returns the index of the vertex
lookupPath :: Meta Path -> Assoc Vertex
lookupPath path =
  unfile . mapGet path <$> gets assocPaths

-- | Adds a vertex to the graph with a set of lower precedence vertices
addVertex :: IntSet -> Assoc ()
addVertex v = modify $ \s -> s
  { assocGraph = assocGraph s |> v }

-- | Updates the set of lower precedence vertices for a given vertex
updateVertex :: Vertex -> (IntSet -> IntSet) -> Assoc ()
updateVertex index f = modify $ \s -> s
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
getSortedAcyclic :: AllDecls -> CompileIO [(Meta Path, InFile OpTypeEnds)]
getSortedAcyclic AllDecls { allOpTypes } =
  checkForCycles $ topSortMap concatEnds allOpTypes
  where
    concatEnds = \case
      _ :/: (Nothing,  Nothing)  -> []
      _ :/: (Nothing,  (Just b)) -> [b]
      _ :/: ((Just a), Nothing)  -> [a]
      _ :/: ((Just a), (Just b)) -> [a, b]

    checkForCycles = \case
      [] ->
        return []
      AcyclicSCC node : rest ->
        (node :) <$> checkForCycles rest
      CyclicSCC nodes : rest -> do
        let
          (Meta { metaSpan }, file :/: _) = head nodes
          nodeList =
            intercalate ", " $ map (show . fst) nodes
        addError CompileError
          { errorFile = Just file
          , errorSpan = metaSpan
          , errorKind = Error
          , errorMessage =
            "cyclic dependencies for operator type declarations\n" ++
            "(nodes in cycle: " ++ nodeList ++ ")" }
        checkForCycles rest

-- | Adds a new operator type declaration to the graph
addToGraph :: (Meta Path, InFile OpTypeEnds) -> Assoc ()
addToGraph (path, file :/: ends) =
  case ends of
    (Nothing, Nothing) -> do
      addPath path file
      addVertex IntSet.empty
    (Nothing, Just higher) -> do
      index <- addPath path file
      higherVertex <- lookupPath higher
      updateVertex higherVertex $ IntSet.insert index
      addVertex IntSet.empty
    (Just lower, Nothing) -> do
      addPath path file
      lowerVertex <- lookupPath lower
      addVertex $ IntSet.singleton lowerVertex
    (Just lower, Just higher) -> do
      lowerVertex <- lookupPath lower
      higherVertex <- lookupPath higher
      graph <- gets assocGraph
      let
        ordering = checkVertexOrdering graph lowerVertex higherVertex
        showLast = show . last . unpath . unmeta
        l = showLast lower
        h = showLast higher
        p = showLast path
        showErr msg =
          lift $ addFatal CompileError
            { errorFile = Just file
            , errorSpan = metaSpan path
            , errorKind = Error
            , errorMessage = msg
              ++ ",\nso `" ++ p ++ "` cannot be added in between" }
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
          index <- addPath path file
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
      comparePaths :: Meta Path -> Meta Path -> Maybe Ordering
      comparePaths a b =
        checkVertexOrdering assocGraph (v a) (v b)
        where
          v path = unfile $ mapGet path assocPaths

      allow :: FilePath -> Maybe (Meta Path) -> Meta Path -> MaybeT CompileIO Bool
      allow file current next =
        case current of
          Nothing ->
            return True
          Just current ->
            case (Map.lookup current allOpDecls, Map.lookup next allOpDecls) of
              (Nothing, Nothing) -> MaybeT $ do
                missing current
                missing next
                return Nothing
              (Nothing, _) -> MaybeT $ do
                missing current
                return Nothing
              (_, Nothing) -> MaybeT $ do
                missing next
                return Nothing
              (Just (_ :/: a), Just (_ :/: b)) ->
                let
                  aOp = opType a
                  bOp = opType b
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
          notAllowed msg = MaybeT $ do
            addError CompileError
              { errorFile = Just file
              , errorSpan = metaSpan next
              , errorKind = Error
              , errorMessage = msg
                ++ ",\n so explicit grouping is required" }
            return Nothing
          missing path =
            addError CompileError
              { errorFile = Just file
              , errorSpan = metaSpan path
              , errorKind = Error
              , errorMessage =
                "operator `" ++ show path ++ "` has not been assigned an "
                ++ "operator precedence,\nso explicit grouping is required" }

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
                applyUnary unaryOp <$> goExpr (Just unaryOp)
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
                  b <- goExpr (Just binaryOp)
                  goBin current (applyBinary binaryOp a b)
                else
                  return a

      updateSome file = reassociate $ associateList file

      updateData :: InFile DataDecl -> CompileIO (InFile DataDecl)
      updateData (file :/: decl) = do
        variants <- mapM (mapM updateVariant) $ dataVariants decl
        return (file :/: decl { dataVariants = variants })
        where
          updateVariant (name, types) =
            (,) name <$> mapM (updateSome file) types

      updateLet :: InFile LetDecl -> CompileIO (InFile LetDecl)
      updateLet (file :/: decl) =
        (file :/:) . (\x -> decl { letBody = x }) <$> updateSome file (letBody decl)

-- | A type of function that can reassociate a list of unassociated expressions
type Associator m = forall t. ContainsOp t => [UnOpOrExpr t] -> m (Meta t)

-- | Represents a part in a list of unassociated expressions
data UnOpOrExpr a
  -- | An operator (either infix or unary)
  = UnOp (Meta Path)
  -- | An expression that will be given to an operator
  | UnExpr (Meta a)

instance Show a => Show (UnOpOrExpr a) where
  show = \case
    UnOp path -> "`" ++ show path ++ "`"
    UnExpr expr -> show expr

-- | A class representing anything that contains infix expressions
class (Show a, After a) => ContainsOp a where
  -- | Convert the expression to a list of unassociated expressions
  toUnOpList :: Meta a -> [UnOpOrExpr a]
  -- | Apply a unary operator to an expression
  applyUnary :: Meta Path -> Meta a -> Meta a
  -- | Apply a binary operator to two expressions
  applyBinary :: Meta Path -> Meta a -> Meta a -> Meta a

-- | Using an 'Associator', fully associate all infix expressions
reassociate :: (Monad m, ContainsOp a) => Associator m -> Meta a -> m (Meta a)
reassociate f = after $ aContainsOp (f . toUnOpList)
  where
    aContainsOp :: Monad m
                => (forall a. ContainsOp a => Meta a -> m (Meta a))
                -> AfterMap m
    aContainsOp f = aDefault
      { aExpr = f
      , aPattern = f
      , aType = f }

instance ContainsOp Type where
  toUnOpList x =
    -- Strip leading parentheses
    case unmeta x of
      TParen a ->
        toUnOpList a
      _ ->
        go x
    where
      go x =
        case unmeta x of
          TParen a ->
            [UnExpr a]
          TUnaryOp path a ->
            UnOp path : toUnOpList a
          TBinOp path a b ->
            UnExpr a : UnOp path : toUnOpList b
          _ ->
            [UnExpr x]

  applyUnary path a =
    metaWithEnds path a $ TApp (copySpan path $ TNamed [] path) a

  applyBinary path a b =
    metaWithEnds a b $
      TApp (metaWithEnds a path $ TApp (copySpan path $ TNamed [] path) a) b

instance ContainsOp Expr where
  toUnOpList x =
    -- Strip leading parentheses
    case unmeta x of
      EParen a ->
        toUnOpList a
      _ ->
        go x
    where
      go x =
        case unmeta x of
          EParen a ->
            [UnExpr a]
          EUnaryOp path a ->
            UnOp path : toUnOpList a
          EBinOp path a b ->
            UnExpr a : UnOp path : toUnOpList b
          _ ->
            [UnExpr x]

  applyUnary path a =
    metaWithEnds path a $ EApp (EGlobal <$> path) a

  applyBinary path a b =
    metaWithEnds a b $
      EApp (metaWithEnds a path $ EApp (EGlobal <$> path) a) b

instance ContainsOp Pattern where
  toUnOpList x =
    -- Strip leading parentheses
    case unmeta x of
      PParen a ->
        toUnOpList a
      _ ->
        go x
    where
      go x =
        case unmeta x of
          PParen a ->
            [UnExpr a]
          PUnaryOp path a ->
            UnOp path : toUnOpList a
          PBinOp path a b ->
            UnExpr a : UnOp path : toUnOpList b
          _ ->
            [UnExpr x]

  applyUnary path a =
    metaWithEnds path a $ PCons path [a]

  applyBinary path a b =
    metaWithEnds a b $ PCons path [a, b]

