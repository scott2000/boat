module Utility.TopSort (SCC (..), topSortSet, topSortMap) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

topSortSet :: Ord a => (a -> [a]) -> Set a -> [SCC a]
topSortSet f set =
  stronglyConnComp $ map toGraph $ Set.toList set
  where
    -- use the indices in the Set as vertices for the graph
    toVertex x = Set.findIndex x set
    toGraph x = (x, toVertex x, map toVertex $ f x)

topSortMap :: Ord k => (v -> [k]) -> Map k v -> [SCC (k, v)]
topSortMap f m =
  stronglyConnComp $ map toGraph $ Map.toList m
  where
    -- use the indices in the Map as vertices for the graph
    toVertex k = Map.findIndex k m
    toGraph (k, v) = ((k, v), toVertex k, map toVertex $ f v)

