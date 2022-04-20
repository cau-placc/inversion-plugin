{-# LANGUAGE CPP, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Parallel.Eden.MapReduce
-- Copyright   :  (c) Philipps Universitaet Marburg 2011-2014
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  eden@mathematik.uni-marburg.de
-- Stability   :  beta
-- Portability :  not portable
--
-- This Haskell module defines map-reduce skeletons for
-- the parallel functional language Eden.
--
-- Depends on GHC. Using standard GHC, you will get a threaded simulation of Eden.
-- Use the forked GHC-Eden compiler from http:\/\/www.mathematik.uni-marburg.de/~eden
-- for a parallel build.
--
-- Eden Group ( http:\/\/www.mathematik.uni-marburg.de/~eden )
-- Depends on the Eden Compiler.


module Eden.MapReduce (
                 -- * Sequential map-reduce definitions
                 mapRedr, mapRedl, mapRedl',
                 -- * Simple map-reduce skeletons
                 parMapRedr, parMapRedl, parMapRedl',
                 -- * offline map-reduce skeletons
                 offlineParMapRedr, offlineParMapRedl, offlineParMapRedl',
                 --  Google map-reduce
                 ) where
import Eden.EdenConcHs
import Eden.Auxiliary
import Eden.Map
import Data.List

mapRedr :: (b -> c -> c)  -- ^ reduce function
           -> c           -- ^ neutral for reduce function
           -> (a -> b)    -- ^ map function
           -> [a]         -- ^ input
           -> c           -- ^ result
mapRedr g e f = (foldr g e) . (map f)

mapRedl :: (c -> b -> c)  -- ^ reduce function
           -> c           -- ^ neutral for reduce function
           -> (a -> b)    -- ^ map function
           -> [a]         -- ^ input
           -> c           -- ^ result
mapRedl g e f = (foldl g e) . (map f)

mapRedl' :: (c -> b -> c) -- ^ reduce function
            -> c          -- ^ neutral for reduce function
            -> (a -> b)   -- ^ map function
            -> [a]        -- ^ input
            -> c          -- ^ result
mapRedl' g e f = (foldl' g e) . (map f)



-- | Basic parMapRedr skeleton - as many processes as noPe.
-- local pre-folding per PE and final folding of PE-results
-- via different fold variants
parMapRedr :: (Trans a, Trans b) =>
              (b -> b -> b) -> b -> (a -> b) -> [a] -> b
parMapRedr g e f
  = --if noPe == 1 then  mapRedr g e f  else
    (foldr g e) . (parMap (mapRedr g e f)) . (splitIntoN noPe)

-- | Basic parMapRedl skeleton - as many processes as noPe.
-- local pre-folding per PE and final folding of PE-results
-- via different fold variants
parMapRedl :: (Trans a, Trans b) =>
              (b -> b -> b) -> b -> (a -> b) -> [a] -> b
parMapRedl g e f
  = --if noPe == 1 then  mapRedl g e f  else
    (foldl g e) . (parMap (mapRedl g e f)) . (splitIntoN noPe)

-- | Basic parMapRedl' skeleton - as many processes as noPe.
-- local pre-folding per PE and final folding of PE-results
-- via different fold variants
parMapRedl' :: (Trans a, Trans b) =>
              (b -> b -> b) -> b -> (a -> b) -> [a] -> b
parMapRedl' g e f
  = --if noPe == 1 then  mapRedl' g e f else
    (foldl' g e) . (parMap (mapRedl' g e f)) . (splitIntoN noPe)



-- | Offline parMapRedr skeleton - as many processes as noPe.
-- local pre-folding per PE and final folding of PE-results
-- via different fold variants,
-- BUT local selection of input sub-list by worker processes
offlineParMapRedr :: (Trans a, Trans b) =>
              (b -> b -> b) -> b -> (a -> b) -> [a] -> b
offlineParMapRedr g e f xs
  = if noPe == 1 then  mapRedr g e f xs  else
    foldr g e (parMap worker [0..noPe-1])
  where worker i = mapRedr g e f ((splitIntoN noPe xs)!!i)

-- | Offline parMapRedl skeleton - as many processes as noPe.
-- local pre-folding per PE and final folding of PE-results
-- via different fold variants,
-- BUT local selection of input sub-list by worker processes
offlineParMapRedl :: (Trans a, Trans b) =>
              (b -> b -> b) -> b -> (a -> b) -> [a] -> b
offlineParMapRedl g e f xs
  = if noPe == 1 then  mapRedl g e f xs  else
    foldr g e (parMap worker [0..noPe-1])
  where worker i = mapRedl g e f ((splitIntoN noPe xs)!!i)

-- | Offline parMapRedl' skeleton - as many processes as noPe.
-- local pre-folding per PE and final folding of PE-results
-- via different fold variants,
-- BUT local selection of input sub-list by worker processes
offlineParMapRedl' :: (Trans a, Trans b) =>
              (b -> b -> b) -> b -> (a -> b) -> [a] -> b
offlineParMapRedl' g e f xs
  = if noPe == 1 then  mapRedl' g e f xs  else
    foldr g e (parMap worker [0..noPe-1])
  where worker i = mapRedl' g e f ((splitIntoN noPe xs)!!i)
