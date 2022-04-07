{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Palindrome where

mkPalindrome :: [a] -> Maybe a -> [a]
mkPalindrome xs Nothing  = xs ++ reverse xs
mkPalindrome xs (Just x) = xs ++ [x] ++ reverse xs

isPalindrome :: Eq a => [a] -> Bool
isPalindrome xs = xs == reverse xs

fromPalindromes :: Eq a => [[a]] -> [a]
fromPalindromes xs | and (map (\x -> not (null x) && isPalindrome x) xs) = concat xs
