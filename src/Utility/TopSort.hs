module Utility.TopSort (SCC (..), topSortSet, topSortMap) where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

topSortSet :: Ord a => Set a -> (a -> [a]) -> [SCC a]
topSortSet set f =
  stronglyConnComp $ map toGraph $ Set.toList set
  where
    -- use the indices in the Set as vertices for the graph
    toVertex x = Set.findIndex x set
    toGraph x = (x, toVertex x, map toVertex $ f x)

topSortMap :: Ord k => Map k v -> (v -> [k]) -> [SCC (k, v)]
topSortMap m f =
  stronglyConnComp $ map toGraph $ Map.toList m
  where
    -- use the indices in the Map as vertices for the graph
    toVertex k = Map.findIndex k m
    toGraph (k, v) = ((k, v), toVertex k, map toVertex $ f v)
