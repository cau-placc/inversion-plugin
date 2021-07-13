{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module Data where

-- Datatypes can be translated ...
data MyMaybe a = MyJust a
               | MyNothing

-- ... and newtypes as well.
newtype Wrap a = Proxy a

data Test a
