{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin -fforce-recomp #-}

module Sort where

insert :: Ord a => a -> [a] -> [a]
insert x []     = [x]
insert x (y:ys) = if x < y then x : y : ys else y : insert x ys

insertionSort :: Ord a => [a] -> [a]
insertionSort []     = []
insertionSort (x:xs) = insert x (insertionSort xs)

data P = Z | S P deriving (Eq, Ord, Show)

lengthP :: [a] -> P
lengthP []     = Z
lengthP (x:xs) = S (lengthP xs)

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

quickSort :: Ord a => [a] -> [a]
quickSort []     = []
quickSort (x:xs) = quickSort (filter (< x) xs) ++ [x] ++ quickSort (filter (>= x) xs)

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

bubble :: Ord a => [a] -> ([a], Bool)
bubble (x:y:xs) | x > y     = (y : fst (bubble (x:xs)), True)
                | otherwise = let (yxs, swapped) = bubble (y : xs) in (x : yxs, swapped)
bubble xs = (xs, False)

bubbleSort :: Ord a => [a] -> [a]
bubbleSort xs = case bubble xs of
    (xs', True)  -> bubbleSort xs'
    (_  , False) -> xs
