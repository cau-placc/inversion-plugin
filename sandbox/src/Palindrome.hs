{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Palindrome where

mkPalindrome :: [a] -> Maybe a -> [a]
mkPalindrome xs Nothing  = xs ++ reverse xs
mkPalindrome xs (Just x) = xs ++ [x] ++ reverse xs

--isPalindrome :: String -> Bool
isPalindrome xs = xs == reverse xs

fromPalindromes :: Eq a => [[a]] -> [a]
fromPalindromes xs | all (\x -> not (null x) && isPalindrome x) xs = concat xs

fromPalindromes2 :: Eq a => [[a]] -> [a]
fromPalindromes2 xs | all (\x -> not (null x) && isPalindrome x) xs && ensureNoDoubles xs = concat xs
  where ensureNoDoubles []       = True
        ensureNoDoubles [_]      = True
        ensureNoDoubles (x:y:xs) = x /= y && ensureNoDoubles (y : xs)

data C = A | B | C
  deriving (Eq, Show)

word = [A,B,C,B,A,A,B,A,A,B,C,B,A,A,B,A,A,B,C,B,A,A,B,A]

-- Test with: head $ $(inv 'fromPalindromes2 True) "abba"
