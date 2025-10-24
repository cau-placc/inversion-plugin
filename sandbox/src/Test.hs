{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin -fforce-recomp #-}

module Test where

id2 :: a -> a
id2 x = x
