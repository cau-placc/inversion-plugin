{-# LANGUAGE TemplateHaskell, FlexibleContexts, ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import Plugin.InversionPlugin

import TreeTraversal

f = map showFree $ ($(inOutClassInv 'id False [[| Test True True |]] [| var 2 |]) :: [Solo Test])

{-
import Prelude hiding (map, lookup, (++), last, Maybe(..))

split123 :: [([Int], [Int])]
split123 = $(inv '(++)) [1,2,3]

anythingBut42 :: [Int]
anythingBut42 = $(inv 'is42) False

last :: Invertible a => [a] -> a
last $(funPat '(++) [p| _ |] [p| [x] |]) = x
last _ = error "empty list"

reverseLookup :: (Invertible a, Invertible b, Eq a, Lifted (Eq a))
              => [(a, b)] -> Maybe b -> [a]
reverseLookup = $(partialInv 'lookup [2])

testMap :: [(Int, Maybe Bool)]
testMap = [(0, Nothing), (2, Just False)]

hasDuplicates :: Invertible a => [a] -> Bool
hasDuplicates $(funPat 'hasDuplicatesPat [p| _ |] [p| _ |] [p| _ |] [p| _ |]) = True
hasDuplicates _ = False

isSame :: Invertible a => (a, a) -> Bool
isSame $(funPat 'dup [p| _ |]) = True
isSame _                       = False
-}
