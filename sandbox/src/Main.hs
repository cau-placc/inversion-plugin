{-# LANGUAGE FlexibleContexts #-}
module Main where

import Plugin.InversionPlugin

import P

--import Janus
import Robert

main = return ()
  --print $ lastTH (replicate 1600 True ++ [False])

{-import Control.DeepSeq

import GHC.Conc (setNumCapabilities)

import System.Environment (getArgs)

import Conquer

-- Build with: stack build sandbox:main --flag inversion-plugin:use-what4
-- Run with: time stack exec main -- mps 16 +RTS

main = do
  [benchmark, cores] <- getArgs
  let func = case benchmark of
        "mps" -> mpsBenchmark
        "mss" -> mssBenchmark
  setNumCapabilities (read cores)
  () <- return $ rnf func
  return ()
-}
{-
--permutations :: Ord a => [a] -> [[a]]
permutations :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutations xs = $(inv 'insertionSort) (insertionSort xs)

permutationsP :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsP xs = let n = lengthP xs in $(partialInv 'insertionSortP [0]) n (insertionSortP n xs)

permutationsI :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsI xs = let n = length xs in $(partialInv 'insertionSortI [0]) n (insertionSortI n xs)

permutationsM :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsM xs = $(inv 'mergeSort) (mergeSort xs)

permutationsMP :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsMP xs = let n = lengthP xs in $(partialInv 'mergeSortP [0]) n (mergeSortP n xs)
-}

permutationsQ :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsQ xs = $(inv 'quickSort) (quickSort xs)

permutationsQP :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsQP xs = let n = lengthP xs in $(partialInv 'quickSortP [0]) n (quickSortP n xs)

permutationsQI :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsQI xs = let n = length xs in $(partialInv 'quickSortI [0]) n (quickSortI n xs)

permutationsQ2 :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsQ2 xs = $(inv 'quickSort2) (quickSort2 xs)

permutationsQ2P :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsQ2P xs = let n = lengthP xs in $(partialInv 'quickSort2P [0]) n (quickSort2P n xs)

{-fibiterInv :: Int -> [Int]
fibiterInv x = $(inv 'fibiter) x

fibrecInv :: Int -> [Int]
fibrecInv x = $(inv 'fibrec) x-}
