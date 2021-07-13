module Plugin.Effect.Tree
 ( module Control.Monad.SearchTree
 , dfs, bfs, prettySearchTree, list )
 where

import Control.Monad.SearchTree
import Data.List

list :: [a] -> [a]
list = id

dfs :: Search a -> [a]
dfs t' = dfs' [searchTree t']
  where dfs' [] = []
        dfs' (t:ts) = case t of
                        None -> dfs' ts
                        One x -> x : dfs' ts
                        Choice l r -> dfs' ([l, r] ++ ts)

bfs :: Search a -> [a]
bfs t' = bfs' [searchTree t']
  where bfs' [] = []
        bfs' (t:ts) = case t of
                        None -> bfs' ts
                        One x -> x : bfs' ts
                        Choice l r -> bfs' (ts ++ [l, r])

data Rose a = Rose a [Rose a]

toRose :: Show a => SearchTree a -> Rose String
toRose None = Rose "!" []
toRose (One a) = Rose (show a) []
toRose (Choice tl tr) = Rose "?" (map toRose [tl, tr])

pretty :: Rose String -> String
pretty = pretty' 0
  where
    pretty' n (Rose x ts) =
      intercalate "\n" $ prettyIndented n x : map (pretty' (n + 1)) ts

    prettyIndented 0 x = x
    prettyIndented n x = concat (replicate (n - 1) "| ") ++ "+– " ++ x

prettySearchTree :: Show a => SearchTree a -> String
prettySearchTree = pretty . toRose
