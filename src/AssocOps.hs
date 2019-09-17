module AssocOps where

import TopSort
import AST
import ErrorPrint

import Data.List
import Control.Monad.Reader
import Control.Monad.State.Strict

import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

type Assoc = StateT AssocState CompileIO

data AssocState = AssocState
  { assocGraph :: Seq IntSet -- set of lower precedence vertices
  , assocPaths :: Map (Meta Path) (InFile Int) }

defaultAssocState :: AssocState
defaultAssocState = AssocState
  { assocGraph = Seq.empty
  , assocPaths = Map.empty }

assocOps :: AllDecls -> CompileIO AllDecls
assocOps decls = do
  opTypes <- getSortedAcyclic decls
  exitIfErrors
  lift $ print opTypes
  assocState <- execStateT (createGraph opTypes) defaultAssocState
  exitIfErrors
  updateExprs assocState decls

getSortedAcyclic :: AllDecls -> CompileIO [(Meta Path, OpTypeEnds)]
getSortedAcyclic AllDecls { allOpTypes } =
  checkForCycles $ topSortMap allOpTypes concatEnds
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

addPath :: Meta Path -> FilePath -> Assoc Int
addPath path file = do
  s <- get
  let index = Seq.length $ assocGraph s
  put s { assocPaths = Map.insert path (file :/: index) $ assocPaths s }
  return index

lookupPath :: Meta Path -> Assoc Int
lookupPath path = do
  paths <- gets assocPaths
  case Map.lookup path paths of
    Just (_ :/: index) ->
      return index
    Nothing ->
      fail ("missing path in AssocOps: " ++ show path)

addVertex :: IntSet -> Assoc ()
addVertex v = modify $ \s -> s
  { assocGraph = assocGraph s |> v }

updateVertex :: Int -> (IntSet -> IntSet) -> Assoc ()
updateVertex index f = modify $ \s -> s
  { assocGraph = Seq.adjust' f index $ assocGraph s }

checkVertexOrdering :: Int -> Int -> Assoc (Maybe Ordering)
checkVertexOrdering a b =
  if a == b then
    return $ Just EQ
  else do
    graph <- gets assocGraph
    let
      check target = go
        where
          go index
            | index == target = True
            | otherwise =
              IntSet.foldl' goAll False $ Seq.index graph index
          goAll a b = a || go b
    if check a b then
      return $ Just LT
    else if check b a then
      return $ Just GT
    else
      return Nothing

createGraph :: [(Meta Path, OpTypeEnds)] -> Assoc ()
createGraph = \case
  [] ->
    return ()
  (path, file :/: ends) : rest -> do
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
        ordering <- checkVertexOrdering lowerVertex higherVertex
        let
          showLast = show . last . unpath . unmeta
          l = showLast lower
          h = showLast higher
          p = showLast path
          showErr msg = do
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
    createGraph rest

updateExprs :: AssocState -> AllDecls -> CompileIO AllDecls
updateExprs AssocState { assocGraph, assocPaths } decls = do
  lift $ do
    print assocGraph
    print assocPaths
  -- TODO: Add operator decls to AllDecls for use here
  -- TODO: Implement associativity fixing (through a typeclass?)
  return decls
