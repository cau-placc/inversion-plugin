{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns     #-}

module FunPat where

import Plugin.InversionPlugin

lastTH $(funPat '(++) [p| _ |] [p| [x] |]) = x

lastVP (\arg -> [p | p@(_, [_]) <- $(inv '(++) False) arg] -> ((_, [x]) : _)) = x

lastVP2 (\arg -> [p | p@(_, [_]) <- $(inv '(++) True) arg] -> ((_, [x]) : _)) = x

lastIC ($(inClassInv '(++) False [[| var 0 |], [| [var 1] |]]) -> ((_, x) : _)) = x
