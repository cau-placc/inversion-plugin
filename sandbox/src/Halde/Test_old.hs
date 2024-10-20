{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Test where

--TODO: ShowFree test

data Maybe2 a = Nothing2 | Just2 a
  deriving Show

isJust2 :: Maybe2 Bool -> Bool
isJust2 Nothing2  = False
isJust2 (Just2 _) = True



head2 :: [a] -> a
head2 (x:_) = x

-- $(inv 'isJust2) True
-- map showFree $ (\x -> $(genInOutClassInverse 'isJust2 True [[| var 1 |]] [| x |])) True

filter2 :: (a -> Bool) -> [a] -> [a]
filter2 _ []     = []
filter2 p (x:xs) | p x       = x : filter2 p xs
                 | otherwise = filter2 p xs

qsort :: Ord a => [a] -> [a]
qsort []     = []
qsort (x:xs) = qsort (filter2 (< x) xs) ++ x : qsort (filter2 (>= x) xs)

reverse2 :: [a] -> [a]
reverse2 [] = []
reverse2 (x:xs) = reverse2 xs ++ [x]



data A = A | B | C | D
  deriving (Eq, Show)

zip2 [] _ = []
zip2 _ [] = []
zip2 (x:xs) (y:ys) = (x,y) : zip2 xs ys

and2 [] = True
and2 (x:xs) = x && and2 xs

take2 0 _ = []
take2 _ [] = []
take2 n (x:xs) = x : take2 (n - 1) xs

length2 [] = 0
length2 (_:xs) = 1 + length2 xs
