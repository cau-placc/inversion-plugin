{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
--{-# OPTIONS_GHC -ddump-splices #-}

module JanusInteger2 where

import Plugin.InversionPlugin

import JanusInteger

fibInv :: Integer -> [Integer]
fibInv n = $(Plugin.InversionPlugin.inv 'fibiter) n

fibrecPairInv :: Integer -> Integer -> [(Integer)]
fibrecPairInv x1 x2 = $(Plugin.InversionPlugin.inv 'fibrecPair) (x1, x2)

fibiterTripleInv :: Integer -> Integer -> Integer -> [(Integer, Integer, Integer)]
fibiterTripleInv n x1 x2 = $(Plugin.InversionPlugin.inv 'fibiterTriple) (n, x1, x2)

fib2Inv :: Integer -> [Integer]
fib2Inv n = $(Plugin.InversionPlugin.inv 'fib) n

fibPairInv :: Integer -> Integer -> [(Integer)]
fibPairInv x1 x2 = $(Plugin.InversionPlugin.inv 'fibPair) (x1, x2)

fibAccInv :: Integer -> [(Integer)]
fibAccInv x = $(Plugin.InversionPlugin.inv 'fibAcc) x
