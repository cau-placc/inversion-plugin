{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

-- Example from "A Program Inverter for a Functional Language"

module Pack where

pack :: Eq a => [a] -> [(a, Int)]
pack [] = []
pack (c1:r) = case pack r of
  [] -> [(c1, 1)]
  (c2, n):t | c1 == c2 -> (c1, n + 1) : t
            | otherwise -> (c1, 1) : (c2, n) : t

pack' :: Eq a => Int -> [a] -> [(a, Int)]
pack' n []     | n >= 0 = []
pack' n (c1:r) | n > 0  = case pack' (n - 1) r of
  [] -> [(c1, 1)]
  (c2, n):t | c1 == c2 -> (c1, n + 1) : t
            | otherwise -> (c1, 1) : (c2, n) : t

unpack :: Eq a => [(a, Int)] -> [a]
unpack [] = []
unpack [(x1, 1)] = [x1]
unpack ((x1, 1):(c2, n):t) | x1 /= c2 = x1 : unpack ((c2,n) : t)
unpack ((x1, n):y) | n > 1 = x1 : unpack ((x1, n - 1) : y)

-- Tests:

-- $(inv 'pack) [('a',3),('b',1),('c',1)]
-- The inverse of this function does not terminate due to the recursive call to pack.
-- This is the same problems as with reverse.

-- $(partialInv 'pack' [0]) 5 [('a',3),('b',1),('c',1)]
-- Terminates due to using a measure.
