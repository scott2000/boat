-- | Utilities for topological sorting
module Utility.TopSort
  ( -- * Reverse Topological Sort
    TopSortable (..)
  , topSort
  , topSortExt

    -- * Strongly Connected Components
  , SCC (..)
  , flattenSCC
  , isSCCAcyclic
  ) where

import Utility.Basics
import Utility.Program

import Data.Graph (SCC (..), stronglyConnComp, flattenSCC)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | A collection of items that can be topologically sorted
class Ord key => TopSortable map entry int key value | map -> entry int key value where
  -- | Get a list of entries from the collection
  entries :: map -> [(entry, int, value)]
  -- | Find the index of a key in the collection
  findIndex :: map -> key -> Int
  -- | Find the index of an internally-used key in the collection
  findInternalIndex :: map -> int -> Int

instance Ord a => TopSortable (Set a) a a a a where
  entries = map (\x -> (x, x, x)) . Set.toAscList
  findIndex = flip Set.findIndex
  findInternalIndex = findIndex

instance Ord k => TopSortable (Map k v) (k, v) k k v where
  entries = map (\e@(k, v) -> (e, k, v)) . Map.toAscList
  findIndex = flip Map.findIndex
  findInternalIndex = findIndex

instance TopSortable (PathMap a) (ReversedPath, (Maybe Span, InFile a)) ReversedPath Path (InFile a) where
  entries (PathMap m) =
    map createEntry $ Map.toAscList m
    where
      createEntry e@(revPath, (_, decl)) = (e, revPath, decl)
  findIndex (PathMap m) k =
    Map.findIndex (reversePath k) m
  findInternalIndex (PathMap m) k =
    Map.findIndex k m

-- | Sorts a 'TopSortable' collection given a function to determine dependencies
topSort :: TopSortable t e i k v => (v -> [k]) -> t -> [SCC e]
topSort f m =
  stronglyConnComp $ map toGraph $ entries m
  where
    toGraph (e, i, v) =
      (e, findInternalIndex m i, map (findIndex m) $ f v)

-- | Like 'topSort' but inside a 'Monad' and collecting additional information
topSortExt :: (TopSortable t e i k v, Monad m) => (v -> m ([k], a)) -> t -> m ([SCC e], Map i a)
topSortExt f m = do
  (depList, ascInfo) <- unzip <$> (mapM toGraphAndInfo $ entries m)
  return (stronglyConnComp depList, Map.fromDistinctAscList ascInfo)
  where
    toGraphAndInfo (e, i, v) = do
      (deps, info) <- f v
      return ((e, findInternalIndex m i, map (findIndex m) deps), (i, info))

-- | Checks is a 'SCC' is an 'AcyclicSCC'
isSCCAcyclic :: SCC a -> Bool
isSCCAcyclic = \case
  AcyclicSCC _ -> True
  CyclicSCC _ -> False

