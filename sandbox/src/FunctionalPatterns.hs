{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module FunctionalPatterns where

import Plugin.InversionPlugin

import ToBeInverted

-- Get the last element of a list.
-- The first argument of `funPat` is the quoted name of the function to be
-- used in the functional pattern.
-- The second argument is a list of quasi-quoted patterns,
-- whose length has to match the arity of the function in the functional pattern.
myLast :: (Argument a, Result a) => [a] -> a
myLast $(funPat 'myAppend [[p| _ |], [p| [x] |]]) = x
myLast _                                          = error "myLast: empty list"
-- ghci> myLast [1,2,3]
-- 3
