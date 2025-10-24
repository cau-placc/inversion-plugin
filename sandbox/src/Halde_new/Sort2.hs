{-# LANGUAGE TemplateHaskell #-}

module Sort2 where

import Plugin.InversionPlugin

import Sort

permutations :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutations xs = $(inv 'insertionSort) (insertionSort xs)

permutationsP :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsP xs = $(partialInv 'insertionSortP [0]) n (insertionSortP n xs)
  where
    n = lengthP xs

permutationsI :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsI xs = $(partialInv 'insertionSortI [0]) n (insertionSortI n xs)
  where
    n = length xs

permutationsQ :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsQ xs = $(inv 'quickSort) (quickSort xs)

permutationsQP :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsQP xs = $(partialInv 'quickSortP [0]) n (quickSortP n xs)
  where
    n = lengthP xs

permutationsQI :: (Ord a, Transform (Ord a), Argument a, Result a) => [a] -> [[a]]
permutationsQI xs = $(partialInv 'quickSortI [0]) n (quickSortI n xs)
  where
    n = length xs
