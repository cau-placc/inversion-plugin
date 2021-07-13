{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns        #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns       #-}
module Tests.Definitions where

import Prelude (Eq(..), Num, Bool(..), Integer)

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

absurd :: a
absurd | False = absurd

is42 :: (Eq a, Num a) => a -> Bool
is42 42 = True
is42 _ = False

is42Integer :: Integer -> Bool
is42Integer = is42

infixr 5 ++
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : xs ++ ys

data Maybe a = Just a | Nothing
  deriving Eq

lookup :: Eq a => a -> [(a, b)] -> Maybe b
lookup _ [] = Nothing
lookup k ((k2,v):kvs) = if k == k2 then Just v else lookup k kvs

hasDuplicatesPat :: a -> [a] -> [a] -> [a] -> [a]
hasDuplicatesPat x a b c = a ++ x : b ++ x : c

mkPalindrome :: Maybe a -> [a] -> [a]
mkPalindrome Nothing  xs = xs ++ reverse xs
mkPalindrome (Just x) xs = xs ++ (x : reverse xs)

reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

isPalindrome :: Eq a => [a] -> Bool
isPalindrome xs = xs == reverse xs
