{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Robert where

import P

import Data.List (partition)

append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys

appendInv :: [a] -> [([a], [a])]
appendInv x = appendInv1 x ++ appendInv2 x

appendInv1 ys = return ([], ys)
appendInv2 (x:xs) = concatMap (\(ys, zs) -> [(x:ys, zs)]) (appendInv xs)
appendInv2 [] = []

appendInv' :: [a] -> [([a], [a])]
appendInv' x = appendInv'1 x ++ appendInv'2 x
appendInv'1 ys = return ([], ys)
appendInv'2 (x:xs) = appendInv' xs >>= \(ys, zs) -> return (x:ys, zs)
--appendInv'2 (x:xs) = do
--  (ys, zs) <- appendInv' xs
--  return (x:ys, zs)

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

data T = A | B | C deriving (Eq, Ord, Show)

noDivs n ds = foldr (\d r -> d*d > n || (rem n d > 0 && r)) True ds

filterTD _ [] = []
filterTD p (x:xs) | p x       = x : filterTD p xs
                  | otherwise = filterTD p xs

primesTD  = 2 : 3 : filterTD (`noDivs` tail primesTD) [5,7..]

isPrimeTD n = n > 1 && noDivs n primesTD

quickSort :: Ord a => [a] -> [a]
quickSort []     = []
quickSort (x:xs) = quickSort (filter (< x) xs) ++ [x] ++ quickSort (filter (>= x) xs)

partition2 :: (a -> Bool) -> [a] -> ([a], [a])
partition2 p xs = foldr (select p) ([], []) xs
  where
    select p x ~(ts,fs) | p x       = (x:ts,fs)
                        | otherwise = (ts, x:fs)

quickSort2 :: Ord a => [a] -> [a]
quickSort2 []     = []
quickSort2 (x:xs) = quickSort2 ys ++ [x] ++ quickSort zs
  where
    (ys,zs) = partition2 (< x) xs

filterP :: P -> (a -> Bool) -> [a] -> (P, [a])
filterP Z     _ []     = (Z, [])
filterP (S n) p (x:xs) =
    let (n', xs') = filterP n p xs
    in if p x then (S n', x : xs') else (n', xs')

quickSortP :: Ord a => P -> [a] -> [a]
quickSortP Z     []     = []
quickSortP (S n) (x:xs) =
    let (n', xs') = filterP n (< x) xs
        (n'', xs'') = filterP n (>= x) xs
    in quickSortP n' xs' ++ [x] ++ quickSortP n'' xs''

filterI :: Int -> (a -> Bool) -> [a] -> (Int, [a])
filterI 0     _ []         = (0, [])
filterI n p (x:xs) | n > 0 =
    let (n', xs') = filterI (n - 1) p xs
    in if p x then (n' + 1, x : xs') else (n', xs')

quickSortI :: Ord a => Int -> [a] -> [a]
quickSortI 0 []             = []
quickSortI n (x:xs) | n > 0 =
    let (n',  xs')  = filterI (n - 1) (< x) xs
        (n'', xs'') = filterI (n - 1) (>= x) xs
    in quickSortI n' xs' ++ [x] ++ quickSortI n'' xs''

partition2P :: P -> (a -> Bool) -> [a] -> (P, [a], P, [a])
partition2P Z     p []     = (Z, [], Z, [])
partition2P (S n) p (x:xs) = let (n', ts, n'', fs) = partition2P n p xs in if p x then (S n', x : ts, n'', fs) else (n', ts, S n'', x : fs)

quickSort2P :: Ord a => P -> [a] -> [a]
quickSort2P Z     []     = []
quickSort2P (S n) (x:xs) = quickSort2P n' ys ++ [x] ++ quickSort2P n'' zs
  where
    (n',ys,n'',zs) = partition2P n (< x) xs

mergeSort :: Ord a => [a] -> [a]
mergeSort [] = []
mergeSort xs = go (map (\x -> [x]) xs)
  where
    go [a] = a
    go xs  = go (mergePairs xs)
    mergePairs (a:b:t) = merge a b : mergePairs t
    mergePairs t       = t

mergeP :: Ord a => P -> [a] -> P -> [a] -> [a]
mergeP Z     []     _     ys                 = ys
mergeP _     xs     Z     []                 = xs
mergeP (S n) (x:xs) (S m) (y:ys) | x < y     = x : mergeP n xs (S m) (y : ys)
                                 | otherwise = y : mergeP (S n) (x : xs) m ys

mergeSortP :: Ord a => P -> [a] -> [a]
mergeSortP Z     [] = []
mergeSortP (S n) xs = go (mapP (S n) (\x -> (S Z, [x])) xs)
  where
    go [(S n, a)] = a
    go xs         = go (mergePairs xs)
    mergePairs ((n,a):(m,b):t) = (n `addP` m, mergeP n a m b) : mergePairs t
    mergePairs t               = t

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


merge4 :: Ord a => Int -> [a] -> Int -> [a] -> [a]
merge4 0 [] _ ys         = ys
merge4 _ xs 0 []         = xs
merge4 n (x:xs) m (y:ys) | n >0 && m > 0 && x < y     = x:merge4 (n-1) xs m (y:ys)
                         | n >0 && m > 0 = y:merge4 n (x:xs) (m-1) ys

msort4 :: Ord a => Int -> [a] -> [a]
msort4 0 [] = []
msort4 n xs | n > 0 && foldr (\_ s -> s + 1) 0 xs == n = go (map (\x -> (1, [x])) xs) --TODO :kai
    where
    go [(_, a)] = a
    go xs = go (pairs xs)
    pairs ((n,a):(m,b):t) = (n + m, merge4 n a m b) : pairs t
    pairs t = t


merge5 :: Ord a => P -> [a] -> P -> [a] -> [a]
merge5 Z [] _ ys         = ys
merge5 _ xs Z []         = xs
merge5 (S n) (x:xs) (S m) (y:ys) | x < y     = x:merge5 n xs (S m) (y:ys)
                                 | otherwise = y:merge5 (S n) (x:xs) m ys

msort5 :: Ord a => P -> [a] -> [a]
msort5 Z [] = []
msort5 (S n) xs = go (map (\x -> (S Z, [x])) xs) --[(S Z, [x]) | x <- xs]
    where
    go [(S n, a)] = a
    go xs = go (pairs xs)
    pairs ((n,a):(m,b):t) = (n `addP` m, merge5 n a m b) : pairs t
    pairs t = t

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

---------------------

insert :: Ord a => a -> [a] -> [a]
insert x []     = [x]
insert x (y:ys) = if x < y then x : y : ys else y : insert x ys

insertionSort :: Ord a => [a] -> [a]
insertionSort []     = []
insertionSort (x:xs) = insert x (insertionSort xs)

insertP :: Ord a => P -> a -> [a] -> [a]
insertP Z     x []     = [x]
insertP (S n) x (y:ys) = if x < y then x : y : ys else y : insertP n x ys

insertionSortP :: Ord a => P -> [a] -> [a]
insertionSortP Z     []     = []
insertionSortP (S n) (x:xs) = insertP n x (insertionSortP n xs)

insertI :: Ord a => Int -> a -> [a] -> [a]
insertI 0 x []             = [x]
insertI n x (y:ys) | n > 0 = if x < y then x : y : ys else y : insertI (n - 1) x ys

insertionSortI :: Ord a => Int -> [a] -> [a]
insertionSortI 0 []             = []
insertionSortI n (x:xs) | n > 0 = insertI (n - 1) x (insertionSortI (n - 1) xs)


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

--TODO:

--permutations :: Ord a => [a] -> [[a]]
--permutations xs = $(partialInv 'isort5 [0]) (lengthP xs) xs



--- eigentlich nicht robert, aber zum testen:

a :: Int
a = 42
b :: () -> Int
b () = 42
--TODO:

factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)
