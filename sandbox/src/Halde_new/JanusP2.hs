{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
--{-# OPTIONS_GHC -ddump-splices #-}

module JanusP2 where

import Plugin.InversionPlugin

import JanusP

fibInv :: Int -> [Int]
fibInv n = $(Plugin.InversionPlugin.inv 'fibiter) n

fibrecPairInv :: Int -> Int -> [(Int)]
fibrecPairInv x1 x2 = $(Plugin.InversionPlugin.inv 'fibrecPair) (x1, x2)
