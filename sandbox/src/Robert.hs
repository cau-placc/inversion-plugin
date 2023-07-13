{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Robert where

append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys

appendInv :: [a] -> [([a], [a])]
appendInv x = appendInv1 x ++ appendInv2 x

appendInv1 ys = return ([], ys)
appendInv2 (x:xs) = concatMap (\(ys, zs) -> [(x:ys, zs)]) (appendInv xs)
appendInv2 [] = []
--TODO: MonadPlus und do-notation klappte nicht: PANIC -> Kai

splits :: [a] -> [([a], [a])]
splits [] = [([], [])]
splits (x:xs) = ([], x:xs) : map (\(ys, zs) -> (x:ys, zs)) (splits xs)

primes :: [Integer]
primes = sieve [2..]
  where
    sieve (p:xs) = p : sieve (concatMap (\x -> if x `mod` p > 0 then [x] else []) xs) --[x|x <- xs, x `mod` p > 0]

getIndex :: [a] -> Int -> a
getIndex (x:xs) 0 = x
getIndex (x:xs) n = getIndex xs (n-1)

nthPrime :: Int -> Integer
nthPrime n = primes `getIndex` n

isPrime :: Integer -> Bool
isPrime k = if k > 1 then null (concatMap (\x -> if k `mod` x == 0 then [x] else []) [2..k - 1]) else False -- [ x | x <- [2..k - 1], k `mod` x == 0]


noDivs n ds = foldr (\d r -> d*d > n || (rem n d > 0 && r)) True ds

filterTD _ [] = []
filterTD p (x:xs) | p x       = x : filterTD p xs
                  | otherwise = filterTD p xs

primesTD  = 2 : 3 : filterTD (`noDivs` tail primesTD) [5,7..]

isPrimeTD n = n > 1 && noDivs n primesTD

qs :: Ord a => [a] -> [a]
qs [] = []
qs (x:xs) = qs (filterTD (< x) xs) ++ [x] ++ qs (filterTD (>= x) xs)

--https://smthngsmwhr.wordpress.com/2012/11/09/sorting-algorithms-in-haskell/#bubble_sort

bubblesort'iter :: (Ord a) => [a] -> [a]
bubblesort'iter (x:y:xs)
    | x > y = y : bubblesort'iter (x:xs)
    | otherwise = x : bubblesort'iter (y:xs)
bubblesort'iter (x) = (x)

bubblesort' :: (Ord a) => [a] -> Int -> [a]
bubblesort' xs i
    | i == (length xs) = xs
    | otherwise = bubblesort' (bubblesort'iter xs) (i + 1)

bubblesort :: (Ord a) => [a] -> [a]
bubblesort xs = bubblesort' xs 0

mergesort'merge :: (Ord a) => [a] -> [a] -> [a]
mergesort'merge [] xs = xs
mergesort'merge xs [] = xs
mergesort'merge (x:xs) (y:ys)
    | (x < y) = x:mergesort'merge xs (y:ys)
    | otherwise = y:mergesort'merge (x:xs) ys

mergesort'splitinhalf :: [a] -> ([a], [a])
mergesort'splitinhalf xs = (take n xs, drop n xs)
    where n = (length xs) `div` 2

mergesort :: (Ord a) => [a] -> [a]
mergesort xs
    | (length xs) > 1 = mergesort'merge (mergesort ls) (mergesort rs)
    | otherwise = xs
    where (ls, rs) = mergesort'splitinhalf xs

sort :: (Ord a) => [a] -> [a]
sort = mergeAll . map (:[])
  where
    mergeAll [] = []
    mergeAll [t] = t
    mergeAll xs  = mergeAll (mergePairs xs)

    mergePairs (x:y:xs) = merge x y:mergePairs xs
    mergePairs xs = xs

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys         = ys
merge xs []         = xs
merge (x:xs) (y:ys) | x < y     = x:merge xs (y:ys)
                    | otherwise = y:merge (x:xs) ys

isAva :: Integer -> Bool
isAva 1 = True
isAva n | n `mod` 7 == 0 = isAva (n `div` 7)
isAva n | n `mod` 5 == 0 = isAva (n `div` 5)
isAva n | n `mod` 3 == 0 = isAva (n `div` 3)
isAva _ = False

msort [] = []
msort xs = go (map return xs) --[[x] | x <- xs]
    where
    go [a] = a
    go xs = go (pairs xs)
    pairs (a:b:t) = merge a b : pairs t
    pairs t = t

insert :: Ord a => a -> [a] -> [a]
{-insert x [] = [x]
insert x (y:ys) | x < y     = x:y:ys
                | otherwise = y:(insert x ys)-}
insert x xs = let (z,zs) = case xs of
                             [] -> (x, [])
                             (y:ys) -> if x < y then (x, y:ys) else (y, insert x ys)
              in z : zs

{- [False]
isort 0
0 -> (1:2)

insert 1 (isort 2)
let (z,zs) = case (isort 2) of
                             [] -> (1, [])
                             (y:ys) -> if 1 < y then (1, y:ys) else (y, insert 1 ys)
              in z : zs

2 -> [] check
2 -> (3:4)


-}

isort :: Ord a => [a] -> [a]
isort [] = []
isort (x:xs) = insert x (isort xs)

nthPrimeTD :: Int -> Integer
nthPrimeTD n = primesTD `getIndex` n

 -- ordered lists, difference and union
minus (x:xs) (y:ys) = case (compare x y) of
           LT -> x : minus  xs  (y:ys)
           EQ ->     minus  xs     ys
           GT ->     minus (x:xs)  ys
minus  xs     _     = xs
union (x:xs) (y:ys) = case (compare x y) of
           LT -> x : union  xs  (y:ys)
           EQ -> x : union  xs     ys
           GT -> y : union (x:xs)  ys
union  xs     []    = xs
union  []     ys    = ys

primesToQ = eratos [2..]
    where
    eratos []     = []
    eratos (p:xs) = p : eratos (xs `minus` [p*p, p*p+p..])

nthPrimeQ :: Int -> Integer
nthPrimeQ n = primesToQ `getIndex` n

isPrimeQ :: Integer -> Bool
isPrimeQ n = n `elem` primesToQ


--- eigentlich nicht robert, aber zum testen:

a :: Int
a = 42
b :: () -> Int
b () = 42
--TODO:
