{-# LANGUAGE TemplateHaskell, FlexibleContexts, ViewPatterns, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import GHC.Conc (getNumProcessors, numCapabilities)

import Plugin.InversionPlugin

import Z

import Conquer

-- Build with: stack build sandbox:main --flag inversion-plugin:use-what4
-- Run with: time stack exec main -- +RTS -N16

main :: IO ()
main = do
  numCores <- getNumProcessors
  putStrLn $ "Number of cores available: " ++ show numCores
  putStrLn $ "Number of threads used: " ++ show numCapabilities
  print (test1Eden list e)

e :: (Z, Z)
e = (0, 0)

list :: [Z]
list = concat $ take 100 $ repeat [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3]
--list = [1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1]

{---f = map showFree $ ($(inOutClassInv 'id False [[| Test True True |]] [| var 2 |]) :: [Solo Test])

split :: _ => _
split = $(inv '(++) True)

split123 :: [([Int], [Int])]
split123 = split [1,2,3]

--anythingBut42 :: [Int]
--anythingBut42 = $(inv 'is42) False

--last :: Invertible a => [a] -> a
--last $(funPat '(++) [p| _ |] [p| [x] |]) = x
--last _ = error "empty list"

--TODO: impossible to give type signature as FL is not exported (and should not be)
--TODO: Maybe use "Inverted" = "Lifted FL"
--reverseLookup :: (Invertible a, Invertible b, Eq a, Lifted FL (Eq a))
--              => [(a, b)] -> Maybe b -> [a]
reverseLookup :: _ => _
reverseLookup = $(partialInv 'lookup True [1])

testMap :: [(Int, Maybe Bool)]
testMap = [(0, Nothing), (2, Just False)]

--hasDuplicates :: Invertible a => [a] -> Bool
--hasDuplicates $(funPat 'hasDuplicatesPat [p| _ |] [p| _ |] [p| _ |] [p| _ |]) = True
--hasDuplicates _ = False

--isSame :: Invertible a => (a, a) -> Bool
--isSame $(funPat 'dup [p| _ |]) = True
--isSame _                       = False
-}
