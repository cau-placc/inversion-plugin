{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module InvertedFunctions where

import Plugin.InversionPlugin

import ToBeInverted

-- Applying the inverted function of myAppend to [1,2,3].
-- ghci> $(inv 'myAppend) [1,2,3]
-- [([],[1,2,3]),([1],[2,3]),([1,2],[3]),([1,2,3],[])]
-- One can also use inverted functions to define new functions.
splits :: (Argument [a], Result [a]) => [a] -> [([a], [a])]
splits = $(inv 'myAppend)
-- ghci> splits [True,False]
-- [([],[True,False]),([True],[False]),([True,False],[])]
