{-# LANGUAGE PartialTypeSignatures, TemplateHaskell, FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Test2 where

import Test

import Plugin.InversionPlugin

g :: _ => _
g = $(mkF)

h :: _ => _
h = $(inv 'id True)

i :: (Argument a, Result a) => a -> a
i = id
