{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Palindrome where

mkPalindrome :: [a] -> Maybe a -> [a]
mkPalindrome xs Nothing  = xs ++ reverse xs
mkPalindrome xs (Just x) = xs ++ [x] ++ reverse xs

isPalindrome :: Eq a => [a] -> Bool
isPalindrome xs = xs == reverse xs

fromPalindromes :: Eq a => [[a]] -> [a]
fromPalindromes xs | and (map (\x -> not (null x) && isPalindrome x) xs) = concat xs

-- TODO: Testen, ob das nachfolgende Palindrom nicht dasselbe ist, um nur die längsten zu bekommen
fromPalindromes2 :: Eq a => [[a]] -> [a]
fromPalindromes2 xs | and (map (\x -> not (null x) && isPalindrome x) xs) && check xs = concat xs
  where check [] = True
        check [_] = True
        check (x:y:xs) = x /= y && check (y:xs)
