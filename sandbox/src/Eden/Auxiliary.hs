{-# LANGUAGE CPP, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Parallel.Eden.Auxiliary
-- Copyright   :  (c) Philipps Universitaet Marburg 2009-2014
-- License     :  BSD-style (see the file LICENSE)
-- 
-- Maintainer  :  eden@mathematik.uni-marburg.de
-- Stability   :  beta
-- Portability :  not portable
--
-- This Haskell module defines auxiliary functions for 
-- programming with the parallel functional language Eden.
--
-- Depends on GHC. Using standard GHC, you will get a threaded simulation of Eden. 
-- Use the forked GHC-Eden compiler from http:\/\/www.mathematik.uni-marburg.de/~eden 
-- for a parallel build.
--
-- Eden Group ( http:\/\/www.mathematik.uni-marburg.de/~eden )


#if defined(NOT_PARALLEL)    
#warning !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\
 Eden BUILD WITH CONCURRENT HASKELL SIMULATION OF PARALLEL PRIMITIVES, \
 DON'T EXPECT SPEEDUPS! USE THE EDEN VERSION OF GHC FROM \
 http://www.mathematik.uni-marburg.de/~eden \
 FOR A PARALLEL BUILD \
 !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!'
#endif
module Eden.Auxiliary (                 
                 -- * Distribution and combine functions
                 -- | ... of form:  @ Int -> [a] -> [[a]] @ / @ [[a]] -> [a] @
                 unshuffle,    shuffle,
                 splitIntoN,   unSplit,
                 chunk,        unchunk,
                 -- * Distribution function for workpools
                 distribute,
                 -- * Lazy functions
                 lazy,
                 lazy1ZipWith, lazy2ZipWith, 
                 lazy1Zip, lazy2Zip,
                 lazyTranspose,
                 -- * other useful functions
                 takeEach, transposeRt,
                 -- * unLiftRDs
                 unLiftRD, unLiftRD2, unLiftRD3, unLiftRD4,
                 -- * More predefined Parallel Actions
                 spawnPss, fetch2, fetchRDss, mergeS
                 ) where

import Data.List
import Data.Maybe(maybeToList,mapMaybe)
import Control.Concurrent
import System.IO.Unsafe(unsafePerformIO,unsafeInterleaveIO)
import Eden.EdenConcHs

-- | Round robin distribution - inverse to shuffle
-- 
unshuffle :: Int      -- ^number of sublists
             -> [a]   -- ^input list
             -> [[a]] -- ^distributed output
unshuffle n xs = [takeEach n (drop i xs) | i <- [0..n-1]]

takeEach :: Int -> [a] -> [a] 
takeEach n [] = []
takeEach n (x:xs) = x : takeEach n (drop (n-1) xs)


-- | Simple shuffling - inverse to round robin distribution
shuffle :: [[a]]  -- ^ sublists
           -> [a] -- ^ shuffled sublists
shuffle = concat . transpose

-- | transpose for matrices of rectangular shape (rows of equal length). Top level list of the resulting matrix is defined as soon as the first row of the original matrix is closed.
transposeRt               :: [[a]] -> [[a]]
transposeRt []             = []
transposeRt ([]   : xss)   = []  -- originally transpose xss -- keeps top level list open until all rows are done
transposeRt ((x:xs) : xss) = (x : [h | (h:_) <- xss]) : transposeRt (xs : [ t | (_:t) <- xss])

-- | Block distribution, @ splitIntoN @ distributes one list on n lists with
--  equal distribution ((+-1) without precondition on length).
splitIntoN :: Int      -- ^ number of blocks
              -> [a]   -- ^list to be split
              -> [[a]] -- ^list of blocks
splitIntoN n xs = chunkBalance (l `div` n) (l `mod` n) xs where
  l = length xs
-- | Inverse function to @ splitIntoN @ - alias for concat.
unSplit :: [[a]]  -- ^list of blocks
           -> [a] -- ^restored list
unSplit = concat

-- | Creates a list of chunks of length @ d @. The first @ m @ chunks will
-- contain an extra element. 
--
-- Result: list of chunks (blocks)
chunkBalance :: Int    -- ^@ d @: chunk-length
              -> Int   -- ^@ m @: number of bigger blocks 
              -> [a]   -- ^list to be split 
              -> [[a]] -- ^list of chunks (blocks)
chunkBalance d = chunk' where
  chunk' _ [] = []
  chunk' 0 xs = ys : chunk' 0 zs where
    (ys,zs) = splitAt d xs
  chunk' m xs = ys : chunk' (m-1) zs where
    (ys,zs) = splitAt (d+1) xs

-- | Creates a list of chunks of length @ d@ .
--
-- Result: list of chunks (blocks)
chunk      :: Int      -- ^@ d @: chunk-length
              -> [a]   -- ^list to be split 
              -> [[a]] -- ^list of chunks (blocks)
chunk l = chunkBalance l 0

-- | Inverse function to @ chunk @ - alias for concat.
unchunk :: [[a]]  -- ^list of chunks
           -> [a] -- ^restored list
unchunk = concat

-- | Task distribution according to worker requests.
--
distribute :: Int  -- ^number of workers
              -> [Int] -- ^ request stream (worker IDs ranging from 0 to n-1)
              -> [t]   -- ^ task list
              -> [[t]] -- ^ task distribution, each inner list for one worker
distribute np reqs tasks = [taskList reqs tasks n | n<-[0..np-1]]
    where taskList (r:rs) (t:ts) pe
                        | pe == r    = t:(taskList rs ts pe)
                        | otherwise  =    taskList rs ts pe
          taskList _      _      _  = []




----------------------------Lazy Functions----------------------------
-- | A lazy list is an infinite stream
lazy :: [a] -> [a]
lazy ~(x:xs) = x : lazy xs

-- |lazy in first argument
lazy1ZipWith :: (a->b->c) -> [a] -> [b] -> [c]
lazy1ZipWith f xs = zipWith f (lazy xs)

-- |lazy in second argument
lazy2ZipWith :: (a->b->c) -> [a] -> [b] -> [c]
lazy2ZipWith f xs ys = zipWith f xs (lazy ys)

-- |lazy in first argument
lazy1Zip :: [a] -> [b] -> [(a,b)]
lazy1Zip xs ys = zip (lazy xs) ys

-- |lazy in second argument
lazy2Zip :: [a] -> [b] -> [(a,b)]
lazy2Zip xs ys = zip xs (lazy ys)

-- |lazy in tail lists
lazyTranspose :: [[a]] -> [[a]]
lazyTranspose = foldr (lazy2ZipWith (:)) (repeat [])

---------------------------unLiftRDs------------------------------
unLiftRD :: (Trans a, Trans b) =>
            (RD a -> RD b)  -- ^ Function to be unlifted
            -> a            -- ^ input
            -> b            -- ^ output
unLiftRD f = fetch . f . release

-- | see @liftRD@
unLiftRD2 :: (Trans a, Trans b, Trans c) 
           => (RD a -> RD b -> RD c)  -- ^ Function to be unlifted
           -> a   -- ^ First input
           -> b   -- ^ Second input
           -> c   -- ^ output
unLiftRD2 f x = unLiftRD (f  (release x)) 

-- | see @liftRD@
unLiftRD3 :: (Trans a, Trans b, Trans c, Trans d) => (RD a -> RD b -> RD c -> RD d) -> a -> b -> c -> d
unLiftRD3 f x = unLiftRD2 (f  (release x)) 

-- | see @liftRD@
unLiftRD4 :: (Trans a, Trans b, Trans c, Trans d, Trans e) => (RD a -> RD b -> RD c -> RD d -> RD e) -> a -> b -> c -> d -> e
unLiftRD4 f x = unLiftRD3 (f  (release x)) 

---------------------------Parallel Actions---------------------------------
-- | Spawn a matrix of processes
spawnPss :: (Trans a, Trans b) => [[Process a b]] -> [[a]] -> [[b]]
spawnPss pss xss = runPA $ sequence $ zipWith3 (\is ps xs -> sequence (zipWith3 instantiateAt is ps xs)) iss pss xss where
  iss = (unshuffle (length (zip pss xss)) [selfPe+1..])

-- | Fetch two Remote Data values
fetch2 :: (Trans a, Trans b) => RD a -> RD b -> (a,b)
fetch2 a b = runPA $
             do a' <- fetchPA a
                b' <- fetchPA b
                return (a',b')
-- | Fetch a matrix of Remote Data
fetchRDss :: Trans a => [[RD a]] -> [[a]]
fetchRDss rda =  runPA $ mapM (mapM fetchPA) rda

--------------------merge variant mergeS-----------------
-- | A variant of non-deterministic list merging, which applies a strategy to list elements prior to merging them and stops the additional merge thread (the suckIO_S thread) when only one input stream is left.
mergeS:: [[a]] -> Strategy a -> [a]
mergeS l st = unsafePerformIO (nmergeIO_S l st)


nmergeIO_S :: [[a]] -> Strategy a -> IO [a]
nmergeIO_S lss st
 = let
    len = length lss
   in
    newEmptyMVar      >>= \ tail_node ->
    newMVar tail_node     >>= \ tail_list ->
    newQSem max_buff_size >>= \ e ->
    newMVar len       >>= \ branches_running ->
    let
     buff = (tail_list,e)
    in
    mapIO (\ x -> forkIO (suckIO_S branches_running buff x st)) lss >>
    takeMVar tail_node  >>= \ val ->
    signalQSem e    >>
    return val
  where
    mapIO f xs = sequence (map f xs)
        
        
suckIO_S :: MVar Int -> Buffer a -> [a] -> Strategy a -> IO ()

suckIO_S branches_running buff@(tail_list,e) vs st
    = do count <- takeMVar branches_running
         if count == 1 then
           takeMVar tail_list     >>= \ node ->
           putMVar node vs        >>
           putMVar tail_list node
          else putMVar branches_running count >>
           case vs of
            [] -> takeMVar branches_running >>= \ val ->
             if val == 1 then
               takeMVar tail_list     >>= \ node ->
               putMVar node []        >>
               putMVar tail_list node
             else  
               putMVar branches_running (val-1)
            (x:xs) ->
               (st x `seq` waitQSem e)       >>
               takeMVar tail_list        >>= \ node ->
                 newEmptyMVar              >>= \ next_node ->
               unsafeInterleaveIO (
                 takeMVar next_node  >>= \ y ->
                 signalQSem e        >>
                 return y)            >>= \ next_node_val ->
               putMVar node (x:next_node_val)   >>
               putMVar tail_list next_node   >>
               suckIO_S branches_running buff xs st

type Buffer a 
 = (MVar (MVar [a]), QSem)

max_buff_size :: Int
max_buff_size = 1