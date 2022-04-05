{-# LANGUAGE TemplateHaskell, FlexibleContexts, ViewPatterns, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import Plugin.InversionPlugin

import TreeTraversal

main :: IO ()
main = return ()

--f = map showFree $ ($(inOutClassInv 'id False [[| Test True True |]] [| var 2 |]) :: [Solo Test])

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
