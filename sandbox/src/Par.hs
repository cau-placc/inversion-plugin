{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Par where

mps :: [Integer] -> Integer
mps [] = 0
--mps [a] = mymax 0 a
mps (a:x) = mymax 0 (a + mps x)

mymax :: Ord a => a -> a -> a
mymax x y = if x > y then x else y

mysum :: [Integer] -> Integer
mysum [] = 0
mysum (a:x) = a + mysum x

---


mpsSum :: [Integer] -> (Integer, Integer)
mpsSum [] = (0,0) --TODO:notwendig?
mpsSum [a] = (mymax 0 a, a)
mpsSum (a:x) = a `pl` mpsSum x
  where a `pl` (p,s) = (mymax 0 (a + p), a + s)

mpsSum2 :: [Integer] -> (Integer, Integer)
mpsSum2 xs = (mps xs, mysum xs)

---

mss :: [Integer] -> Integer
mss [] = 0
mss (a:x) = mymax (a + mps x) (mss x)

mts :: [Integer] -> Integer
mts [] = 0
mts (a:x) = mymax (mts x) (a + mysum x)

mssTupled' :: [Integer] -> (Integer, Integer, Integer, Integer)
mssTupled' xs = (mss xs, mps xs, mts xs, mysum xs)

mssTupled :: [Integer] -> (Integer, Integer, Integer, Integer)
mssTupled [a] = (mymax 0 a, mymax 0 a, mymax 0 a, a)
mssTupled (a:x) = let (m,p,t,s) = mssTupled x in (mymax (a + p) m, mymax 0 (a+p), mymax t (a+s), a + s)

mssTupledWI :: (Integer, Integer, Integer, Integer) -> [Integer]
mssTupledWI (m, p, t, s) = [p, -p - t + s, m, -m + t]
--mssTupledWI (m, p, t, s) = if (0 <= p && p >= m && 0 <= t && t >= m && s+m <= t+p) then [p, -p - t + s, m, -m + t] else error "Blub"

func a = mssTupled [a]

odot :: (Integer, Integer, Integer, Integer) -> (Integer, Integer, Integer, Integer) -> (Integer, Integer, Integer, Integer)
odot x y = mssTupled (mssTupledWI x ++ mssTupledWI y)

---

data Z = Neg N | Zero | Pos N
  deriving (Eq, Ord, Show)
data N = I | S N
  deriving (Eq, Ord, Show)

plusN :: N -> N -> N
plusN I n = S n
plusN (S m) n = S (plusN m n)

minusN :: N -> N -> Z
minusN I n = incZ (Neg n)
minusN (S m) I = Pos m
minusN (S m) (S n) = minusN m n

incZ :: Z -> Z
incZ (Neg I) = Zero
incZ (Neg (S m)) = Neg m
incZ Zero = Pos I
incZ (Pos m) = Pos (S m)

plusZ :: Z -> Z -> Z
plusZ Zero y = y
plusZ x Zero = x
plusZ (Pos m) (Pos n) = Pos (plusN m n)
plusZ (Neg m) (Neg n) = Neg (plusN m n)
plusZ (Pos m) (Neg n) = minusN m n
plusZ (Neg m) (Pos n) = minusN n m

mssZ :: [Z] -> Z
mssZ [] = Zero
mssZ (a:x) = mymax (a `plusZ` mpsZ x) (mssZ x)


mpsZ :: [Z] -> Z
mpsZ [] = Zero
mpsZ (a:x) = mymax Zero (a `plusZ` mpsZ x)

mtsZ :: [Z] -> Z
mtsZ [] = Zero
mtsZ (a:x) = mymax (mtsZ x) (a `plusZ` sumZ x)

sumZ :: [Z] -> Z
sumZ [] = Zero
sumZ (a:x) = a `plusZ` sumZ x

mssZTupled :: [Z] -> (Z, Z, Z, Z)
mssZTupled xs = (mssZ xs, mpsZ xs, mtsZ xs, sumZ xs)

negateZ :: Z -> Z
negateZ (Pos n) = Neg n
negateZ Zero = Zero
negateZ (Neg n) = Pos n

minusZ :: Z -> Z -> Z
minusZ x y = x `plusZ` negateZ y

mssZTupledWI :: (Z, Z, Z, Z) -> [Z]
mssZTupledWI (m, p, t, s) = [p, negateZ p `minusZ` t `plusZ` s, m, negateZ m `plusZ` t]