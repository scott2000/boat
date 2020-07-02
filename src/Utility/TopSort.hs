-- | Utilities for topological sorting
module Utility.TopSort
  ( -- * Reverse Topological Sort
    TopSortable (..)
  , topSortExt
  , topSortM
  , topSort

    -- * Strongly Connected Components
  , SCC (..)
  , flattenSCC
  , isSCCAcyclic
  ) where

import Utility.Basics

import Data.Hashable

import Data.Graph (Vertex, SCC (..), stronglyConnComp, flattenSCC)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad
import Data.Functor.Identity

-- | A collection of items that can be topologically sorted
class TopSortable key entry map | map -> entry key where
  -- | Like 'mapM', but with specific information for sorting
  mapEntries :: Monad m => ((key -> Vertex) -> entry -> Vertex -> m a) -> map -> m [a]

instance Ord a => TopSortable a a (Set a) where
  mapEntries f s =
    zipWithM (f (`Set.findIndex` s)) (Set.toAscList s) [0..]

instance Ord k => TopSortable k (k, v) (Map k v) where
  mapEntries f m =
    zipWithM (f (`Map.findIndex` m)) (Map.toAscList m) [0..]

instance (Eq k, Hashable k) => TopSortable k (k, v) (HashMap k v) where
  mapEntries f m =
    zipWithM (f (keyMap HashMap.!)) entryList [0..]
    where
      entryList = HashMap.toList m
      keyMap =
        HashMap.fromList $ zipWith (\(k, _) n -> (k, n)) entryList [0..]

-- | Sorts a 'TopSortable' collection given a function to determine dependencies
topSortExt :: (TopSortable k e map, Monad m) => (e -> m ([k], a)) -> map -> m [SCC a]
topSortExt f =
  fmap stronglyConnComp . mapEntries \getIndex entry index -> do
    f entry <&> \(deps, result) ->
      (result, index, map getIndex deps)

-- | Like 'topSortExt', but always returns the entry directly
topSortM :: (TopSortable k e map, Monad m) => (e -> m [k]) -> map -> m [SCC e]
topSortM f =
  topSortExt \entry ->
    f entry <&> \deps ->
      (deps, entry)

-- | Like 'topSortM', but always uses the 'Identity' monad
topSort :: TopSortable k e map => (e -> [k]) -> map -> [SCC e]
topSort f =
  runIdentity . topSortM (pure . f)

-- | Checks is a 'SCC' is an 'AcyclicSCC'
isSCCAcyclic :: SCC a -> Bool
isSCCAcyclic = \case
  AcyclicSCC _ -> True
  CyclicSCC _ -> False

