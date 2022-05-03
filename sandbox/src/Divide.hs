{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Divide where

-- Maximum prefix/segment sum problem

mps :: (Num a, Ord a) => [a] -> a
mps []    = 0
mps (a:x) = max 0 (a + mps x)

mss :: (Num a, Ord a) => [a] -> a
mss []    = 0
mss (a:x) = max (a + mps x) (mss x)

mts :: (Num a, Ord a) => [a] -> a
mts []    = 0
mts (a:x) = max (mts x) (a + sum x)

mssTupled :: (Num a, Ord a) => [a] -> (a, a, a, a)
mssTupled xs = (mss xs, mps xs, mts xs, sum xs)

mpsTupled :: (Num a, Ord a) => [a] -> (a, a)
mpsTupled xs = (mps xs, sum xs)

-- Line-of-sight problem

visible :: Ord a => [a] -> Bool
visible [a] = True
visible (a:x) = a <= maximum x && visible x

visibleTupled :: Ord a => [a] -> (Bool, a)
visibleTupled x = (visible x, maximum x)
