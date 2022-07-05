module Plugin.Effect.Tree
 ( module Control.Monad.SearchTree
 , Search, searchTree
 , dfs, bfs, ps )
 where

import Control.Concurrent
import Control.Monad.Codensity
import Control.Monad.Fix
import Control.Monad.SearchTree hiding (Search, searchTree)

import           Data.Maybe

import qualified Data.Sequence as Seq

import System.IO.Unsafe
import System.Mem.Weak

type Search = Codensity SearchTree

-- TODO: Fix orphan instance
instance MonadFix m => MonadFix (Codensity m) where
    mfix f = Codensity $ \k -> mfix (lowerCodensity . f) >>= k

-- TODO: Fix orphan instance
instance MonadFix SearchTree where
  mfix f = case fix (f . unOne) of
    None -> None
    One x -> One x
    Choice _ _ -> Choice (mfix (lT . f)) (mfix (rT . f))
    where
      unOne (One x) = x
      unOne _ = error "Not a Leaf in mfix"
      lT (Choice x _) = x
      lT _ = error "Not a Node in mfix"
      rT (Choice _ x) = x
      rT _ = error "Not a Node in mfix"

searchTree :: Search a -> SearchTree a
searchTree = lowerCodensity

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
        One x -> writeChan ch (Just x)
        Choice l r -> do
          mvarL <- newEmptyMVar
          mvarR <- newEmptyMVar
          _ <- forkFinally (psIO l) $ \_ -> putMVar mvarL ()
          _ <- forkFinally (psIO r) $ \_ -> putMVar mvarR ()
          takeMVar mvarL
          takeMVar mvarR
  tid <- forkFinally (psIO $ searchTree t') $ \_ -> writeChan ch Nothing
  res <- catMaybes . takeWhile isJust <$> getChanContents ch
  addFinalizer res $ killThread tid
  return res

{-
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

{-
psNaive :: Search a -> [a]
psNaive t' = unsafePerformIO $ do
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
-}
