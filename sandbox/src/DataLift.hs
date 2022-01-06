{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module DataLift where

data B = F | T


class C a where
  cc :: a -> a
  dd :: a -> a

instance C B where
  cc x = x
  dd = cc

notB :: B -> B
notB F = T
notB T = F

constI :: B -> a -> B
constI x _ = x

test :: Bool
test = True