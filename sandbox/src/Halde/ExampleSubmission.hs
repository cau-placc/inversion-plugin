{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module ExampleSubmission where

import Prelude hiding (map, lookup, reverse, (++), Maybe(..))

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

absurd :: a
absurd | False = absurd

is42 :: (Eq a, Num a) => a -> Bool
is42 42 = True
is42 _ = False

infixr 5 ++
(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : xs ++ ys

data Maybe a = Just a | Nothing
  deriving Show

data Bool2 = T | F
  deriving Show

lookup :: Eq a => a -> [(a, b)] -> Maybe b
lookup _ [] = Nothing
lookup k ((k2,v):kvs) = if k == k2 then Just v else lookup k kvs

dup :: a -> (a, a)
dup x = (x, x)

hasDuplicatesPat :: a -> [a] -> [a] -> [a] -> [a]
hasDuplicatesPat x a b c = a ++ x : b ++ x : c

mkPalindrome :: Maybe a -> [a] -> [a]
mkPalindrome Nothing xs = xs ++ (reverse xs)
mkPalindrome (Just x) xs = xs ++ (x : reverse xs)

reverse :: [a] -> [a]
reverse [] = []
reverse (x:xs) = reverse xs ++ [x]

isPalindrome :: Eq a => [a] -> Bool
isPalindrome xs = xs == reverse xs
-- Notice the difference between the two versions regarding the Eq2 context.
-- The problem is known from functional logic programming. The strict equality
-- is part of the Unifiable class. An operator with the same semantics at source
-- level could be provided (like '===' in Curry).
