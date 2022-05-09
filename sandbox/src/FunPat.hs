{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ViewPatterns          #-}

module FunPat where

import FunPatSrc

import Plugin.InversionPlugin

lastTH $(funPat '(++) [p| _ |] [p| [x] |]) = x

lastVP (\arg -> [p | p@(_, [_]) <- $(inv '(++) False) arg] -> ((_, [x]) : _)) = x

lastVP2 (\arg -> [p | p@(_, [_]) <- $(inv '(++) True) arg] -> ((_, [x]) : _)) = x

lastIC ($(inClassInv '(++) False [[| var 0 |], [| [var 1] |]]) -> ((_, x) : _)) = x

h $(funPat 'pat [p| y |]) = True

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
