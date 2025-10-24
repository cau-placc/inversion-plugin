{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
--{-# OPTIONS_GHC -ddump-splices #-}

module Janus2 where

import Plugin.InversionPlugin

import Janus

fibInv :: Int -> [Int]
fibInv n = $(Plugin.InversionPlugin.inv 'fibiter) n

fibrecPairInv :: Int -> Int -> [(Int)]
fibrecPairInv x1 x2 = $(Plugin.InversionPlugin.inv 'fibrecPair) (x1, x2)


fibiterTripleInv :: Int -> Int -> Int -> [(Int, Int, Int)]
fibiterTripleInv n x1 x2 = $(Plugin.InversionPlugin.inv 'fibiterTriple) (n, x1, x2)

fib2Inv :: Int -> [Int]
fib2Inv n = $(Plugin.InversionPlugin.inv 'fib) n

fibPairInv :: Int -> Int -> [(Int)]
fibPairInv x1 x2 = $(Plugin.InversionPlugin.inv 'fibPair) (x1, x2)

fibAccInv :: Int -> [(Int)]
fibAccInv x = $(Plugin.InversionPlugin.inv 'fibAcc) x
