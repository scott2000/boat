-- | Utilities for topological sorting
module Utility.TopSort
  ( -- * Reverse Topological Sort
    topSortSet
  , topSortMap
  , topSortPathMap

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

-- | Sorts a 'Set' given a function to determine dependencies
topSortSet :: Ord a => (a -> [a]) -> Set a -> [SCC a]
topSortSet f set =
  stronglyConnComp $ map toGraph $ Set.toList set
  where
    toVertex x = Set.findIndex x set
    toGraph x = (x, toVertex x, map toVertex $ f x)

-- | Sorts a 'Map' given a function to determine dependencies
topSortMap :: Ord k => (v -> [k]) -> Map k v -> [SCC (k, v)]
topSortMap f m =
  stronglyConnComp $ map toGraph $ Map.toList m
  where
    toVertex k = Map.findIndex k m
    toGraph (k, v) = ((k, v), toVertex k, map toVertex $ f v)

-- | Sorts a 'PathMap' given a function to determine dependencies
topSortPathMap :: (a -> [Path]) -> PathMap a -> [SCC (ReversedPath, (Maybe Span, InFile a))]
topSortPathMap f (PathMap m) =
  stronglyConnComp $ map toGraph $ Map.toList m
  where
    toVertex revPath = Map.findIndex revPath m
    toGraph entry@(revPath, (_, _ :/: decl)) =
      (entry, toVertex revPath, map (toVertex . reversePath) $ f decl)

-- | Checks is a 'SCC' is an 'AcyclicSCC'
isSCCAcyclic :: SCC a -> Bool
isSCCAcyclic = \case
  AcyclicSCC _ -> True
  CyclicSCC _ -> False

