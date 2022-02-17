module Plugin.Effect.Tree
 ( module Control.Monad.SearchTree
 , dfs, bfs, ps )
 where

import Control.Concurrent
import Control.Monad.SearchTree

import           Data.Maybe

import qualified Data.Sequence as Seq

import System.IO.Unsafe
import System.Mem.Weak

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
ps :: Search a -> [a]
ps t' = unsafePerformIO $ do
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
ps1 :: Search a -> [a]
ps1 t' = unsafePerformIO $ do
  ch <- newChan
  let psIO mvar t = case t of
        None -> putMVar mvar ()
        One x -> do
          writeChan ch (Just x)
          putMVar mvar ()
        Choice l r -> do
          mvarl <- newEmptyMVar
          mvarr <- newEmptyMVar
          _ <- forkIO $ psIO mvarl l
          _ <- forkIO $ psIO mvarr r
          takeMVar mvarl
          takeMVar mvarr
          putMVar mvar ()
  mvar <- newEmptyMVar
  _ <- forkIO $ psIO mvar (searchTree t')
  _ <- forkIO $ do
    takeMVar mvar
    writeChan ch Nothing
  catMaybes . takeWhile isJust <$> getChanContents ch

ps2 :: Search a -> [a]
ps2 t' = unsafePerformIO $ do
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
