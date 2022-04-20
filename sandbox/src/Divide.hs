{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Divide where

import Z

{-mss :: [Z] -> Z
mss []    = 0
mss (a:x) = max (a + mps x) (mss x)

mps :: [Z] -> Z
mps []    = 0
mps (a:x) = max 0 (a + mps x)

mts :: [Z] -> Z
mts []    = 0
mts (a:x) = max (mts x) (a + sum x)

mssTupled :: [Z] -> (Z, Z, Z, Z)
mssTupled xs = (mss xs, mps xs, mts xs, sum xs)

mpsTupled :: [Z] -> (Z, Z)
mpsTupled xs = (mps xs, sum xs)-}

mss :: (Num a, Ord a) => [a] -> a
mss []    = 0
mss (a:x) = max (a + mps x) (mss x)

mps :: (Num a, Ord a) => [a] -> a
mps []    = 0
mps (a:x) = max 0 (a + mps x)

mts :: (Num a, Ord a) => [a] -> a
mts []    = 0
mts (a:x) = max (mts x) (a + sum x)

mssTupled :: (Num a, Ord a) => [a] -> (a, a, a, a)
mssTupled xs = (mss xs, mps xs, mts xs, sum xs)

mpsTupled :: (Num a, Ord a) => [a] -> (a, a)
mpsTupled xs = (mps xs, sum xs)
