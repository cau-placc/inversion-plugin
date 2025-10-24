{-# LANGUAGE TemplateHaskell, ViewPatterns, GADTs, AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -ddump-splices #-}

module List2 where

import Plugin.InversionPlugin

import List

--reverseInv :: (Argument a, Result a) => [a] -> [[a]]
--reverseInv :: (Argument [a], Result [a]) => [a] -> [[a]]
reverseInv x = $(inv 'reverse') x

--reversePInv :: (Argument a, Result a) => [a] -> [[a]]
reversePInv :: (Argument [a], Result [a]) => [a] -> [[a]]
reversePInv xs = $(partialInv 'reverseP [1]) n xs
  where
    n = lengthP xs

--reverseAccInv :: (Argument a, Result a) => [a] -> [[a]]
reverseAccInv :: (Argument [a], Result [a]) => [a] -> [[a]]
reverseAccInv xs = $(inv 'reverseAcc) xs

--reverseAccPInv :: (Argument a, Result a) => [a] -> [[a]]
reverseAccPInv :: (Argument [a], Result [a]) => [a] -> [[a]]
reverseAccPInv xs = $(partialInv 'reverseAccP [1]) n xs
  where
    n = lengthP xs

solveList [True] = True

solve2 True2 = True2

solveList2 (Cons2 True2 Nil2) = True2

not2 False2 = True2
not2 True2 = False2

f $(funPat 'constTrue2 [[p| x |]]) = x


--removeIndex :: [a] -> Int -> (a, [a])
--randomInsert :: (Argument a, Result a) => a -> [a] -> [([a], Int)]
randomInsert :: (Argument [a], Argument Int, Result (a, [a])) => a -> [a] -> [([a], Int)]
randomInsert x xs = $(inv 'removeIndex) (x, xs)

--insert :: (Argument a, Result a) => Int -> a -> [a] -> [a]
insert :: (Argument [a], To Int, Result (a, [a])) => Int -> a -> [a] -> [a]
insert n x xs = head $ $(partialInv 'removeIndex [2]) n (x, xs)

--removeElem :: (Argument a, Result a) => [a] -> a -> [(Int, [a])]
removeElem xs x = $(inOutClassInv 'removeIndex [[| xs |], [| var 0 |]] [| (x, var 1) |])

--removeElem2 :: (Argument a, Result a) => [a] -> a -> [(Int, [a])]
removeElem2 :: (Argument Int, Argument [a], Unifiable (Transform (a, [a])), To [a], To a) => [a] -> a -> [(Int, [a])]
removeElem2 x = $(semiInv 'removeIndex [1] [1]) x


testMH :: [Bool] -> [Bool] -> [()]
testMH xs ys = $(inOutClassInv 'id [[|xs|]] [|ys|])


lookupInv :: (Argument a, Result a, Argument b, Result b, Transform (Eq a)) => Maybe b -> [(a, [(a, b)])]
lookupInv x = $(inv 'myLookup) x
--lookupInv x = $(semiInv 'myLookup [] [1]) x --TODO: Kai, eta reduction

reverseLookup :: (To [(a, b)], Argument a, Result (Maybe b), Transform (Eq a)) => [(a, b)] -> Maybe b -> [a]
reverseLookup map res = $(partialInv 'lookup [2]) map res

{-
[Just failed,2] =:= [x,2]
$(inOutClassInv 'id [[|var 0|]] [|var 1|])
-}

--From inversion and term rewriting systems by kirkeby
divide :: (Argument a, Result a) => [a] -> [([a], [a])]
divide xs = $(inv '(++)) xs

--append :: (Argument a, Result a) => [a] -> [a] -> [a]
append xs ys = head $ $(semiInv '(++) [1, 2] []) xs ys

dropPrefix :: (Argument a, Result a) => [a] -> [a] -> [a]
dropPrefix prefix ys = head $ $(partialInv '(++) [1]) prefix ys

mathTestInv :: Integer -> [(Integer, Integer)]
mathTestInv x = $(semiInv 'mathTest [] [1]) x

lastTH $(funPat '(++) [[p| _ |], [p| [x] |]]) = x

--nullaryInv :: Bool -> [()]
nullaryInv = $(inv 'nullary)

--unaryInv :: Bool -> [Bool]
unaryInv = $(inv 'unary)


g = $(semiInv 'mhTest [1] [2])

{-
beispiel beweisen, dass das partiell/semi inverse ist, beispiele in extensions für arithmetische operationen aufgreifen, ivmod ergänzen

aussagen zu partiellen und semi inversen mit bijektivität

sorten in der einleitung zum kapitel mit verweis auf typen direkt erwähnen, aber aussclhießen
-}
