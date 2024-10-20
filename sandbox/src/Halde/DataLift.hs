-- {-# LANGUAGE MultiParamTypeClasses, BangPatterns #-}
{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module DataLift where

--import Data.Char
import Data.Functor.Identity

newtype A a = A { getA :: a }
  deriving Show


getId (Identity x) = x

--f = chr
--g = ord

{-mySignum :: Num a => a -> a
mySignum = signum

data Pair a b = Pair a b
  deriving Show
signumTest :: Num a => a -> Pair a a
signumTest x = Pair x x

--signumTest2 :: Num a => a -> (a, a)
--signumTest2 x = (x, x)

myAbs :: Num a => a -> a
myAbs = abs

myMax :: Ord a => a -> a -> a
myMax = max

mySeq :: a -> b -> b
mySeq = seq

ackG :: Integer -> Integer -> Integer
ackG 0 n | n >= 0 = n + 1
ackG m 0 | m >= 0 = ackG (m - 1) 1
ackG m n | m >= 0 && n >= 0 = ackG (m - 1) (ackG m (n - 1)) -- $(inv 'ackG) 43

ackSame :: Integer -> Integer
ackSame n = ackG n n

test = mySeq (cantor 56456456 56456456) True

cantor :: (Ord a, Num a, Integral a) => a -> a -> a
cantor x y | x >= 0 && y >= 0 = ((x + y) * (x + y + 1) `div` 2) + y -- $-}

--const x y = x

{-f :: Bool
f = error ""

g :: Bool
g = undefined
-}

--data StrictBool = StrictBool !Bool

--test :: Int -> Int
--test !x = x

{-data List2 a = List2 [a]
--  deriving Show
newtype List3 a = List3 [a]
type List4 = List2

f :: List4 a -> List2 a
f = id-}

{-
 Argument value doesn't match argument type:
    Fun type:
        FL (IntFL FL :--> (List2FL a_a153v :--> ShowSFL FL))
        -> FL (List2FL a_a153v :--> StringFL FL)
        -> FL (ListFL FL (List2FL a_a153v) :--> ShowSFL FL)
        -> ShowFL (List2FL a_a153v)
    Arg type:
        FL
          ((-->) FL (IntFL FL) ((-->) FL (List2FL FL a_a153v) (ShowSFL FL)))
    Arg: $cshowsPrecFL_a15fv @ a_a153v $dShow_a153w
    In the RHS of $fShowList2FL :: forall a.
                                   ShowFL a =>
                                   ShowFL (List2FL FL a)
-}

{-loop = loop

g False = g False
g True  = True

g3 False = False
g3 True  = True-}


--eq :: Eq a => a -> a -> Bool
--eq = (==)
