{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module FunPatSrc where

g x y = (x, y)

pat y = g (id y) y

test f g x = f g x
