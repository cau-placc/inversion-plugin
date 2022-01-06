{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module DataLift where

data B = F | T

notB :: B -> B
notB F = T
notB T = F

constI :: B -> a -> B
constI x _ = x

test :: Bool
test = True