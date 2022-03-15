{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module Tree where

data Tree a = Empty
            | Node (Tree a) a (Tree a)
  deriving Show

preorder :: Tree a -> [a]
preorder Empty        = []
preorder (Node l x r) = [x] ++ preorder l ++ preorder r

inorder :: Tree a -> [a]
inorder Empty        = []
inorder (Node l x r) = inorder l ++ [x] ++ inorder r

pinorder :: Tree a -> ([a], [a])
pinorder t = (preorder t, inorder t)

inporder :: Tree a -> ([a], [a])
inporder t = (inorder t, preorder t)
-- TODO: terminiert nicht, da inorder nicht terminiert.

exampleTree :: Tree Char
exampleTree = Node (Node (Node Empty 'a' Empty) 'b' (Node Empty 'c' Empty)) 'd' (Node (Node Empty 'e' Empty) 'f' Empty)

--testList = [x + y | x <- [0, 1], y <- [1, 2]]

--

-- Hufmann

data HTree a = HLeaf a Int
             | HNode (HTree a) (HTree a) Int
  deriving Show

weight :: HTree a -> Int
weight (HLeaf _ w)    = w
weight (HNode _ _ w)  = w

filter2 :: (a -> Bool) -> [a] -> [a]
filter2 _ [] = []
filter2 p (x:xs) | p x = x : filter2 p xs
                 | otherwise = filter2 p xs

partition2 :: (a -> Bool) -> [a] -> ([a], [a])
partition2 p = foldr2 select ([], [])
  where select x (xs, ys) | p x = (x : xs, ys)
                          | otherwise = (xs, x : ys)

frequencies :: Eq a => [a] -> [(a, Int)]
frequencies []       = []
frequencies (x : xs) = let (ys, zs) = partition2 (== x) xs
                       in (x, length2 ys + 1) : frequencies zs

data Alphabet = A | B | C | D | E | F
  deriving (Show, Eq)

type Codemap a = [(a, [Bool])]

orderedInsert :: HTree a -> [HTree a] -> [HTree a]
orderedInsert n [] = [n]
orderedInsert n all@(first:rest)
    | weight n <= weight first = n : all
    | otherwise = first : (orderedInsert n rest)

makeTree :: [HTree a] -> HTree a
makeTree [n] = n
makeTree (first:second:rest) =
  makeTree (orderedInsert (HNode first second (weight first + weight second)) rest)

makeCodemap :: HTree a -> Codemap a
makeCodemap (HLeaf c _)    = [(c, [])]
makeCodemap (HNode l r _)  = map (addBit False) (makeCodemap l) ++ map (addBit True) (makeCodemap r)
  where addBit b (x, y) = (x, b : y)

genCodemap input = makeCodemap (makeTree (map (uncurry HLeaf) (frequencies input)))

genCodeword codemap input = concatMap2 (flip lookupJust2 codemap) input

-- $(partialInv 'genCodeword [0]) :: Codemap a -> Output -> [(restlichenInput)]
-- \x -> $(partialInv 'genCodeword [| free 1 |] [| free 1 |])

--genCodewordFL [| free 1 |] [| free 1 |])


--TODO: müssen pattern sein, da ich diese traversieren muss, um
encode :: Eq a => [a] -> (Codemap a, [Bool])
encode input = (codemap, codeword)
  where codemap = genCodemap input
        codeword = genCodeword codemap input

encode2 :: Eq a => [a] -> ([Bool], Codemap a)
encode2 input = (codeword, codemap)
  where codemap = genCodemap input
        codeword = genCodeword codemap input

lookupJust2 :: Eq a => a -> [(a, b)] -> b
lookupJust2 k ((k2,x):xs) | k == k2 = x
                          | otherwise = lookupJust2 k xs

{-append [] ys = ys
append (x:xs) ys = x : append xs ys

appendInv ys = ([], ys)
appendInv (x:zs) = case appendInv zs of
  (xs,ys) -> (x:xs, ys)
-}

appendInv :: [a] -> [([a], [a])]
appendInv ys = [([], ys)] ++ (case ys of {[] -> []; x:zs -> appendInv zs >>= \ (xs,ys) -> [(x:xs,ys)]})

-- Run-length encoding

foldr2 :: (a -> b -> b) -> b -> [a] -> b
foldr2 _ e [] = e
foldr2 f e (x:xs) = f x (foldr2 f e xs)

--rle2 :: Eq a => [a] -> [(a, Int)]

{-rleIneff :: Eq a => [a] -> [(a, Int)]
rleIneff = foldr2 code []
      where code c []            = [(c, 1)]
            code c ((x, n) : ts) | c == x    = (x, n + 1) : ts
                                 | otherwise = (c, 1) : (x, n) : ts --TODO: info dass n > 0 fehlt-}

length2 :: [a] -> Int
length2 [] = 0
length2 (_:xs) = 1 + length2 xs

lengthI :: [a] -> Integer
lengthI [] = 0
lengthI (_:xs) = 1 + lengthI xs

lengthP :: [a] -> P
lengthP [] = Z
lengthP (_:xs) = S (lengthP xs)

dropP :: P -> [a] -> [a]
dropP Z xs = xs
dropP (S l) (_:xs) = dropP l xs

data P = Z | S P
  deriving (Show, Eq)

rleP :: Eq a => [a] -> [(a, P)]
rleP [] = []
rleP (c:cs) = let l = lengthP (takeWhile (== c) cs)
             in (c, S l) : rleP (dropP l cs)

dropI :: Integer -> [a] -> [a]
dropI n xs | n <= 0 = xs
dropI _ [] = []
dropI n (_:xs) = dropI (n - 1) xs

rleI :: Eq a => [a] -> [(a, Integer)]
rleI [] = []
rleI (c:cs) = let l = lengthI (takeWhile (== c) cs)
              in (c, l + 1) : rleI (dropI l cs)

rle :: Eq a => [a] -> [(a, Int)]
rle [] = []
rle (c:cs) = let l = length2 (takeWhile (== c) cs)
             in (c, l + 1) : rle (drop l cs)

unrle :: [(a, Int)] -> [a]
unrle [] = []
unrle ((x, n) : ts) | n > 0 = replicate2 n x ++ unrle ts

unrle3 :: Eq a => [(a, Int)] -> [a]
unrle3 [] = []
unrle3 ((x, n) : []) | n > 0 = replicate2 n x
unrle3 ((x, n) : (y, m) : ts) | y /= x && n > 0 = replicate2 n x ++ unrle3 ((y, m) : ts)

replicateP Z _ = []
replicateP (S n) x = x : replicateP n x

unrle3P :: Eq a => [(a, P)] -> [a]
unrle3P [] = []
unrle3P ((x, n@(S _)) : []) = replicateP n x
unrle3P ((x, n@(S _)) : (y, m) : ts) | y /= x = replicateP n x ++ unrle3P ((y, m) : ts)

--TODO: ..., because 'Int ist einfach ein kack Datentyp' [TeegenPrott2022KackDatentypInt].
--TODO: könnte peano intern für int(eger) nehmen
--TODO: cantor als gegenbeispiel für peano (-> case study)
--TODO: note context on inverse (missing)
--TODO: O(n*m)
--TODO: peano for connection with list length (known from curry, and proving (kai))


--TODO: l-inverse: fInv . f   -> x `elem` fInv (f x) für alle values x
--TODO: r-inverse: map f . fInv   -> map ((== x) . f) (fInv x) für alle values x
-- TODO: often functions are pseudo-inverses. for example, the functions rle and unrle are not inverses of each other. unrleInv yields "unexpected" results, like tuples with zero and ('a', 1), ('a', 1) instead of ('a', 2)

--other examples are words/unwords, lines/unlines. zip/unzip. all those functions are not injective.
--(uncurry zip . unzip) gilt, lines "a", "a\n", words mehrere leerzeichen

replicate2 0 _ = []
replicate2 n x | n > 0 = x : replicate2 (n - 1) x

unrle2 :: [(a, Int)] -> [a]
unrle2 = concatMap2 (uncurry (flip replicate2))

concatMap2 :: (a -> [b]) -> [a] -> [b]
concatMap2 _ [] = []
concatMap2 f (x:xs) = f x ++ concatMap2 f xs

{-rle :: Eq a => [a] -> [(a, Int)]
rle = foldr2 code []

code :: Eq a => a -> [(a, Int)] -> [(a, Int)]
code c []            = [(c, 1)]
code c ((x, n) : ts) | c == x    = (x, n + 1) : ts
                     | otherwise = (c, 1) : (x, n) : ts-}

--- substring/match from the URA: inverse computation in a functional language

match :: Eq a => [a] -> [a] -> Bool
match []     _      = True
match _      []     = False
match (x:xs) (y:ys) = (x == y && match xs ys) || match (x:xs) ys

-- $(partialInv 'match [1]) "abcd" True
-- \x -> $(clsInv 'match [ free 1, "abcd" ] (x))




-- concrete example from "principles of inverse computation and the URA"

--TODO: Num instanz für peano angeben

{-findrep :: [Int] -> [Int] -> [Int]
findrep [] _  = []
findrep xs [] = xs
findrep (x:xs) -}

--TODO: same paper, acyclic walk example

type Graph a = [(a, [a])]
type Path a = [a]

elem2 :: Eq a => a -> [a] -> Bool
elem2 _ []     = False
elem2 x (y:ys) = x == y || elem2 x ys

notElem2 x xs = not (elem2 x xs)

data Maybe2 a = Nothing2 | Just2 a

lookup2 :: Eq a => a -> [(a, b)] -> Maybe2 b
lookup2 _ [] = Nothing2
lookup2 k ((k2,v):kvs) | k == k2 = Just2 v
                       | otherwise = lookup2 k kvs

f False = False

error2 _ = f True

and2 :: Bool -> Bool -> Bool
and2 True True = True
and2 _ _ = False

--TODO: 2-parts: is walk and cycle free
isWalk :: Eq a => Graph a -> Path a -> Bool
isWalk g p = isWalk' p []
  where isWalk' []     _      = True
        isWalk' (x:xs) []     =
          if notElem2 x (map fst g) then error2 "bla"
                                    else isWalk' xs [x]
        isWalk' (x:xs) (y:ys) =
          if notElem2 x (map fst g) then error2 "bla"
                                    else
            isReachable x y && notElem2 x (y:ys) && isWalk' xs (x:y:ys)
        isReachable x y = case lookup2 y g of
          Nothing2 -> error2 "bla"
          Just2 ys -> elem2 x ys

--ex_g = [('A', "BC"), ('B', "D"), ('C', ""), ('D', "AC")]
ex_g = [(A, [B,C]), (B, [D]), (C, []), (D, [A,C])]

-- $(partialInv 'isWalk [0]) ex_g True
--allWalks x = $(partialInv 'isWalk [|| x ||] [|| free 1 ||])

----

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

-- :t $(inv 'snoc)


-- $(ioInv 'f [[|| x ||], [|| [free 1] ||]] [|| free 1 ||])

--TODO: (vgl. minikanren post von dmitri) conjunction order problem in prolog/minikanren

reverse2 :: [a] -> [a]
reverse2 [] = []
reverse2 (x:xs) = reverse2 xs ++ [x]

reverseAcc2 :: [a] -> [a]
reverseAcc2 xs = reverseAcc xs []
  where reverseAcc [] ys = ys
        reverseAcc (x:xs) ys = reverseAcc xs (x:ys)


and'2 :: [Bool] -> Bool
and'2 [] = True
and'2 (False:_) = False
and'2 (_:bs) = and'2 bs

all2 f = and'2 . map f

concat2 [] = []
concat2 (x:xs) = x ++ concat2 xs

--[a] -> [[a]]
fromPalindromes :: Eq a => [[a]] -> [a]
fromPalindromes xs | all2 (\x -> notNull2 x && isPalindrome x) xs = concat2 xs

isPalindrome :: Eq a => [a] -> Bool
isPalindrome xs = xs == reverse2 xs

--[a] -> [[a]]
fromPalindromesL :: Eq a => [(P, [a])] -> (P, [a])
fromPalindromesL xs | all2 (\(n, x) -> notNull2 x && isPalindromeL n x) xs = concat2L xs

isPalindromeL :: Eq a => P -> [a] -> Bool
isPalindromeL n xs = xs == reverseL n xs

addP Z n = n
addP (S n) m = S (addP n m)

concat2L [] = (Z, [])
concat2L ((n,x):xs) = let (m, ys) = concat2L xs in (addP n m, x ++ ys)

reverseL Z _ = []
reverseL (S n) (x:xs) = reverseL n xs ++ [x]

notNull2 [] = False
notNull2 _ = True
