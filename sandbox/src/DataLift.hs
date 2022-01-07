{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module DataLift where

data B = F | T
  deriving (Eq, Show)

eq :: (Eq a) => a -> a -> Bool
eq = (==)

shw :: (Show a) => a -> String
shw = show

class C a where
  cc :: a -> a
  dd :: a -> a

instance C B where
  cc x = x
  dd = cc