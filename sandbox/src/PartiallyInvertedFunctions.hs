{-# LANGUAGE TemplateHaskell, FlexibleContexts, MonoLocalBinds #-}
module PartiallyInvertedFunctions where

import Plugin.InversionPlugin

import ToBeInverted

-- Implementing a reverse lookup via a partially inverted function of myLookup.
-- The list argument `[2]` to `partialInv` denotes
-- that the second argument (the key-value list) is fixed.
reverseLookup :: (To [(k, v)], Argument k, Result (Maybe v), Eq k, Transform (Eq k))
              => v -> [(k, v)] -> [k]
reverseLookup v xs = $(partialInv 'myLookup [2]) xs (Just v)
-- ghci> reverseLookup True [(1,True),(2,False),(3,True)]
-- [1,3]
