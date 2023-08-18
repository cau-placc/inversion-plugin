{-# LANGUAGE LambdaCase #-}

module Plugin.Effect.Tree
 ( module Control.Monad.SearchTree
 , dfs, iddfs, bfs, ps )
 where

import Control.Concurrent
import Control.Monad.SearchTree

import           Data.Maybe
import           Data.Monoid
import qualified Data.Sequence as Seq

import System.IO.Unsafe
import System.Mem.Weak

dfs :: SearchTree a -> [a]
dfs = dfs' . (: [])
  where dfs' [] = []
        dfs' (t:ts) = case t of
          None -> dfs' ts
          One x -> x : dfs' ts
          Choice l r -> dfs' ([l, r] ++ ts)

{-
-- Implementation of depth-first search without accumulator.
dfs :: SearchTree a -> [a]
dfs None = []
dfs (One x) = [x]
dfs (Choice l r) = dfs l ++ dfs r
-}

iddfs :: SearchTree a -> [a]
iddfs t = foldr (\maxDepth ys -> let (xs, All exhausted) = iddfs' t 0 maxDepth
                                 in xs ++ if exhausted then [] else ys) [] [0 ..]
  where iddfs' :: SearchTree a -> Int -> Int -> ([a], All)
        iddfs' None _ _ = ([], All True)
        iddfs' (One x) depth maxDepth | depth < maxDepth = ([], All True)
                                      | depth == maxDepth = ([x], All True)
        iddfs' (Choice l r) depth maxDepth | depth < maxDepth =
          let (xs, all1) = iddfs' l (depth + 1) maxDepth
              (ys, all2) = iddfs' r (depth + 1) maxDepth
          in (xs ++ ys, all1 <> all2)
        iddfs' _ _ _ = ([], All False)

{-
-- Implementation of iterative deepening depth-first search without knowing when the search tree is exhausted.
iddfs :: SearchTree a -> [a]
iddfs t = concatMap (iddfs' t 0) [0 ..]
  where iddfs' :: SearchTree a -> Int -> Int -> [a]
        iddfs' None _ _ = []
        iddfs' (One x) d maxD | d == maxD = [x]
        iddfs' (Choice l r) d maxD | d < maxD = iddfs' l (d + 1) maxD ++ iddfs' r (d + 1) maxD
        iddfs' _ _ _ = []
-}

bfs :: SearchTree a -> [a]
bfs = bfs' . Seq.singleton
  where bfs' Seq.Empty = []
        bfs' (t Seq.:<| ts) = case t of
          None -> bfs' ts
          One x -> x : bfs' ts
          Choice l r -> bfs' (ts Seq.:|> l Seq.:|> r)

ps :: SearchTree a -> [a]
ps t = unsafePerformIO $ do
  ch <- newChan
  let psIO = \case
        None -> return ()
        One x -> writeChan ch (Just x)
        Choice l r -> do
          mvarL <- newEmptyMVar
          mvarR <- newEmptyMVar
          _ <- forkFinally (psIO l) $ \_ -> putMVar mvarL ()
          _ <- forkFinally (psIO r) $ \_ -> putMVar mvarR ()
          takeMVar mvarL
          takeMVar mvarR
  tid <- forkFinally (psIO t) $ \_ -> writeChan ch Nothing
  res <- catMaybes . takeWhile isJust <$> getChanContents ch
  addFinalizer res $ killThread tid
  return res

{-
-- Implementation of parallel search without knowing when the search tree is exhausted and without finalizer.
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

-- Implementation of parallel search without finalizer.
psWithoutFinalizer :: Search a -> [a]
psWithoutFinalizer t' = unsafePerformIO $ do
  ch <- newChan
  let psIO t = case t of
        None -> return ()
        One x -> writeChan ch (Just x)
        Choice l r -> do
          mvarl <- newEmptyMVar
          mvarr <- newEmptyMVar
          _ <- forkFinally (psIO l) $ \_ -> putMVar mvarl ()
          _ <- forkFinally (psIO r) $ \_ -> putMVar mvarr ()
          takeMVar mvarl
          takeMVar mvarr
  _ <- forkFinally (psIO $ searchTree t') $ \_ -> writeChan ch Nothing
  catMaybes . takeWhile isJust <$> getChanContents ch
-}
