{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns          #-}

module FunPat where

import FunPatSrc

import Plugin.InversionPlugin

lastTH $(funPat '(++) [[p| _ |], [p| [x] |]]) = x

lastTHLegacy $(funPatLegacy '(++) [[p| _ |], [p| [x] |]]) = x

isEmpty :: [Bool] -> Bool
isEmpty $(funPat '(++) [[p| [] |], [p| [] |]]) = True

f $(funPat 'h [[p| x |]]) = True

--lastTH2 $(funPatLegacy '(++) [[p| _ |], [p| [x] |]]) = x

{-
--lazyUnifyFL (x, empty) (y,y)
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
