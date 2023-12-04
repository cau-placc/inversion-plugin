{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns          #-}

module FunPat where

import FunPatSrc

import Plugin.InversionPlugin

--appendInv :: (From [a], Unifiable [a], NormalForm [a]) => [a] -> [([a], [a])]
--appendInv :: (Input [a], Output [a]) => [a] -> [([a], [a])]
--appendInv = $(inv 'append)

--fInv :: (From a, NormalForm a, To b, Unifiable b) => b -> [a]
fInv x = $(inv 'FunPatSrc.f) x

lastTH $(funPat 'append [[p| _ |], [p| [x] |]]) = x

lastTHLegacy $(funPatLegacy '(++) [[p| _ |], [p| [x] |]]) = x

isEmpty :: [Bool] -> Bool
isEmpty $(funPat '(++) [[p| [] |], [p| [] |]]) = True

data Bla = Blub

instance Eq Bla where
  (==) :: Bla -> Bla -> Bool
  Blub == Blub = True

--f $(funPat 'h [[p| x |]]) = True

--lastTH2 $(funPatLegacy '(++) [[p| _ |], [p| [x] |]]) = x

{-
--nonStrictUnifyFL (x, empty) (y,y)
-- (y,y) =:<= (x, failed)
-- f (y, y)
-- f (x, y) | x =:= y
-- (x, z) =:<= (y, y)
testFunPat :: _ => Bool -> _
testFunPat = \x -> $(inOutClassInv 'g True [[| var 0 |], [| var 0 |]] [| (var 1, x) |])

testFunPat2 :: _ => Bool -> _
testFunPat2 = \x -> $(inOutClassInv 'g True [[| var 0 |], [| x |]] [| (var 1, var 1) |])

testFunPat3 :: _ => Bool -> _
testFunPat3 = \x -> $(inOutClassInv 'g True [[| var 0 |], [| var 0 |]] [| (var 0, x) |])

--f2Inv :: (Output a1, Input a2, To (a3 -> b)) => (a3 -> b) -> a2 -> [Solo a1]
--f2Inv = $(partialInv 'f2 True [0])

-}
