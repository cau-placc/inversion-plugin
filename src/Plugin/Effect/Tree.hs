module Plugin.Effect.Tree
 ( module Control.Monad.SearchTree
 , dfs, bfs )
 where

import Control.Monad.SearchTree

import qualified Data.Sequence as Seq

dfs :: Search a -> [a]
dfs t' = dfs' [searchTree t']
  where dfs' [] = []
        dfs' (t:ts) = case t of
                        None -> dfs' ts
                        One x -> x : dfs' ts
                        Choice l r -> dfs' ([l, r] ++ ts)

bfs :: Search a -> [a]
bfs t' = bfs' (Seq.singleton (searchTree t'))
  where bfs' Seq.Empty = []
        bfs' (t Seq.:<| ts) = case t of
          None -> bfs' ts
          One x -> x : bfs' ts
          Choice l r -> bfs' (ts Seq.:|> l Seq.:|> r)