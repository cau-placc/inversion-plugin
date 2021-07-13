{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE TypeApplications          #-}
module SemanticTests where

import Test.QuickCheck

import Plugin.InversionPlugin
import Tests.QuickCheckInverse
import Tests.Definitions as Plugin

is42Test :: Bool -> Bool
is42Test = $(genInverseQuickCheck 'Plugin.is42Integer 10 [])

lastTest :: [Bool] -> Property
lastTest xs = not (null xs) ==> (last xs == otherLast xs)
  where
    otherLast $(funPat '(Plugin.++) [p| _ |] [p| [x] |]) = x
    otherLast _                                          = error "empty list"

lookupTestReverse :: [(Integer, Integer)] -> Integer -> Property
lookupTestReverse xs a = length xs <= 15 ==>
  $(genInverseQuickCheck 'Plugin.lookup 10 [2]) xs (Plugin.Just a)

lookupTestUnused :: [(Integer, Integer)] -> Property
lookupTestUnused xs = length xs <= 15 ==>
  $(genInverseQuickCheck 'Plugin.lookup 10 [2]) xs (Plugin.Nothing @Integer)
