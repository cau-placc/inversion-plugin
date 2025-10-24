module Plugin.Effect.Tree
 ( module Control.Monad.SearchTree
 , dfs, iddfs, bfs, concurrentSearch )
 where

import Control.Concurrent
import Control.Monad.SearchTree

import           Data.Maybe
import           Data.Monoid
import qualified Data.Sequence as Seq
import qualified Data.Set      as Set

import GHC.Exts (noinline)

import System.IO.Unsafe
import System.Mem.Weak

dfs :: SearchTree a -> [a]
dfs = go . (: [])
  where go [] = []
        go (t:ts) = case t of
          None       -> go ts
          One x      -> x : go ts
          Choice l r -> go ([l, r] ++ ts)

{-
-- Implementation of depth-first search without accumulator.
dfs :: SearchTree a -> [a]
dfs None         = []
dfs (One x)      = [x]
dfs (Choice l r) = dfs l ++ dfs r
-}

iddfs :: SearchTree a -> [a]
iddfs t = foldr (\maxDepth ys -> let (xs, All exhausted) = go t 0 maxDepth
                                 in xs ++ if exhausted then [] else ys) [] [0 ..]
  where go :: SearchTree a -> Int -> Int -> ([a], All)
        go None _ _ = ([], All True)
        go (One x) depth maxDepth | depth < maxDepth = ([], All True)
                                      | depth == maxDepth = ([x], All True)
        go (Choice l r) depth maxDepth | depth < maxDepth =
          let (xs, all1) = go l (depth + 1) maxDepth
              (ys, all2) = go r (depth + 1) maxDepth
          in (xs ++ ys, all1 <> all2)
        go _ _ _ = ([], All False)

{-
-- Implementation of iterative deepening depth-first search without knowing when the search tree is exhausted.
iddfs :: SearchTree a -> [a]
iddfs t = concatMap (go t 0) [0 ..]
  where go :: SearchTree a -> Int -> Int -> [a]
        go None _ _ = []
        go (One x) d maxD | d == maxD = [x]
        go (Choice l r) d maxD | d < maxD = go l (d + 1) maxD ++ go r (d + 1) maxD
        go _ _ _ = []
-}

bfs :: SearchTree a -> [a]
bfs = go . Seq.singleton
  where go Seq.Empty = []
        go (t Seq.:<| ts) = case t of
          None       -> go ts
          One x      -> x : go ts
          Choice l r -> go (ts Seq.:|> l Seq.:|> r)

{-# NOINLINE concurrentSearch #-}
concurrentSearch :: SearchTree a -> [a]
concurrentSearch t = unsafePerformIO $ do
  ch <- newChan
  mTids <- newEmptyMVar
  putMVar mTids Set.empty
  let go t' = case t' of
        None       -> return ()
        One x      -> writeChan ch (Just x)
        Choice l r -> do
          mL <- newEmptyMVar
          mR <- newEmptyMVar
          tids <- takeMVar mTids
          tidL <- forkFinally (go l) $ \_ -> finalizeT mL
          tidR <- forkFinally (go r) $ \_ -> finalizeT mR
          putMVar mTids $ Set.insert tidL (Set.insert tidR tids)
          takeMVar mL
          takeMVar mR
      finalizeT mT = do
        putMVar mT ()
        tid <- myThreadId
        modifyMVar_ mTids (return . Set.delete tid)
  tid <- forkFinally (go t) $ \_ -> writeChan ch Nothing
  results <- catMaybes . takeWhile isJust <$> getChanContents ch
  addFinalizer results $ do
    tids <- takeMVar mTids
    mapM_ killThread (tid : Set.toList tids)
  return (foldr (\x xs -> noinline (const id) results (x : xs)) [] results)

{- old:
{-# NOINLINE concurrentSearch #-}
concurrentSearch :: SearchTree a -> [a]
concurrentSearch t = unsafePerformIO $ do
  ch <- newChan
  mvarTids <- newEmptyMVar
  putMVar mvarTids []
  let go t' = case t' of
        None       -> return ()
        One x      -> writeChan ch (Just x)
        Choice l r -> do
          mvarL <- newEmptyMVar
          mvarR <- newEmptyMVar
          tids <- takeMVar mvarTids
          tidL <- forkFinally (go l) $ \_ -> putMVar mvarL ()
          tidR <- forkFinally (go r) $ \_ -> putMVar mvarR ()
          putMVar mvarTids $ [tidL, tidR] ++ tids
          takeMVar mvarL
          takeMVar mvarR
  tid <- forkFinally (go t) $ \_ -> writeChan ch Nothing
  result <- catMaybes . takeWhile isJust <$> getChanContents ch
  addFinalizer result $ do
    tids <- takeMVar mvarTids
    mapM_ killThread (tid : tids)
  return result
  -}

{-
-- Implementation of concurrent search without knowing when the search tree is exhausted and without finalizer.
{-# NOINLINE concurrentSearch #-}
concurrentSearch :: SearchTree a -> [a]
concurrentSearch t = unsafePerformIO $ do
  ch <- newChan
  let go t' = case t' of
        None       -> return ()
        One x      -> writeChan ch x
        Choice l r -> do
          _ <- forkIO $ go l
          _ <- forkIO $ go r
          return ()
  go t
  getChanContents ch

-- Implementation of concurrent search without finalizer.
{-# NOINLINE concurrentSearch #-}
concurrentSearch :: SearchTree a -> [a]
concurrentSearch t = unsafePerformIO $ do
  ch <- newChan
  let go t' = case t' of
        None       -> return ()
        One x      -> writeChan ch (Just x)
        Choice l r -> do
          mvarL <- newEmptyMVar
          mvarR <- newEmptyMVar
          _ <- forkFinally (go l) $ \_ -> putMVar mvarL ()
          _ <- forkFinally (go r) $ \_ -> putMVar mvarR ()
          takeMVar mvarL
          takeMVar mvarR
  _ <- forkFinally (go t) $ \_ -> writeChan ch Nothing
  catMaybes . takeWhile isJust <$> getChanContents ch

-- Implementation of concurrent search with finalizer.
{-# NOINLINE concurrentSearch #-}
concurrentSearch :: SearchTree a -> [a]
concurrentSearch t = unsafePerformIO $ do
  ch <- newChan
  let go t' = case t' of
        None       -> return ()
        One x      -> writeChan ch (Just x)
        Choice l r -> do
          mvarL <- newEmptyMVar
          mvarR <- newEmptyMVar
          _ <- forkFinally (go l) $ \_ -> putMVar mvarL ()
          _ <- forkFinally (go r) $ \_ -> putMVar mvarR ()
          takeMVar mvarL
          takeMVar mvarR
  tid <- forkFinally (go t) $ \_ -> writeChan ch Nothing
  res <- catMaybes . takeWhile isJust <$> getChanContents ch
  addFinalizer res (killThread tid)
  return res
-}
