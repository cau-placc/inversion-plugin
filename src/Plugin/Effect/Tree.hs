module Plugin.Effect.Tree
 ( module Control.Monad.SearchTree
 , dfs, bfs, ps )
 where

import Control.Concurrent
import Control.Monad.SearchTree

import GHC.IO (unsafePerformIO)

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

ps :: Search a -> [a]
ps t' = unsafePerformIO $ do
  ch <- newChan
  let psIO t = case t of
        None -> return ()
        One x -> writeChan ch x
        Choice l r -> do
          _ <- forkIO $ psIO l
          _ <- forkIO $ psIO r
          return ()
  psIO (searchTree t')
  getChanContents ch
