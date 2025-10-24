{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin -fforce-recomp #-}

module List where

data Bool2 = False2 | True2
  deriving (Eq, Show)

data List2 a = Nil2 | Cons2 a (List2 a)
  deriving (Eq, Show)

reverse' :: [a] -> [a]
reverse' []     = []
reverse' (x:xs) = reverse' xs ++ [x]

reverseAcc :: [a] -> [a]
reverseAcc xs = go xs []
  where
    go []     acc = acc
    go (x:xs) acc = go xs (x : acc)

data P = Z | S P deriving (Eq, Ord, Show)

lengthP :: [a] -> P
lengthP []     = Z
lengthP (x:xs) = S (lengthP xs)

reverseP :: P -> [a] -> [a]
reverseP Z     []     = []
reverseP (S n) (x:xs) = reverseP n xs ++ [x]

reverseAccP :: P -> [a] -> [a]
reverseAccP n xs = go n xs []
  where
    go Z     []     acc = acc
    go (S n) (x:xs) acc = go n xs (x : acc)

solve True = True

constTrue2 :: () -> Bool
constTrue2 _ = True

data A = A | B
  deriving Show

removeIndex :: [a] -> Int -> (a, [a])
removeIndex (x:xs) 0 = (x, xs)
removeIndex (x:xs) n | n > 0 = (y, x:ys)
  where
    (y, ys) = removeIndex xs (n - 1) --TODO: Peano?

nullary :: Bool
nullary = True

unary :: Bool -> Bool
unary True = True

myLookup :: (Eq a) => a -> [(a, b)] -> Maybe b
myLookup = lookup

mathTest :: Integer -> (Integer, Integer)
mathTest x = (x * x, x * x * x)

data Solo2 a = Solo2 a
  deriving (Eq, Show)

fromSolo2 :: Solo2 a -> a
fromSolo2 (Solo2 x) = x

insertAt :: a -> Int -> [a] -> [a]
insertAt y 0 xs = y:xs
insertAt y n (x:xs) | n > 0 = x: insertAt y (n - 1) xs



mhTest :: Int -> Int -> (Int, Int)
mhTest x y = (x + 3*y+2,2*x+y+1)
