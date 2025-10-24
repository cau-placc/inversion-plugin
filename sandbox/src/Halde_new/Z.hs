{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Z where

data N = I | S N
  deriving (Show)

instance Eq N where
  I     == I     = True
  (S m) == (S n) = m == n
  _     == _     = False

instance Ord N where
  I     <= _     = True
  (S _) <= I     = False
  (S m) <= (S n) = m <= n

data Z = Neg N | Zero | Pos N
  deriving (Show)

instance Eq Z where
  Neg m == Neg n = m == n
  Zero  == Zero  = True
  Pos m == Pos n = m == n
  _     == _     = False

instance Ord Z where
  Zero  <= Pos _ = True
  Zero  <= Neg _ = False
  Zero  <= Zero  = True
  Neg m <= Neg n = n <= m
  Neg _ <= _     = True
  Pos m <= Pos n = m <= n
  Pos _ <= _     = False

instance Num Z where
  (+) = plusZ
  (-) = minusZ
  (*) = timesZ
  negate = negateZ
  abs = absZ
  signum = signumZ
  fromInteger = fromIntegerZ

plusN :: N -> N -> N
plusN I     n = S n
plusN (S m) n = S (plusN m n)

minusN :: N -> N -> Z
minusN I     n     = incZ (Neg n)
minusN (S m) I     = Pos m
minusN (S m) (S n) = minusN m n

timesN :: N -> N -> N
timesN I     n = n
timesN (S m) n = plusN n (timesN m n)

fromIntegerN :: Integer -> N
fromIntegerN 1         = I
fromIntegerN i | i > 1 = S (fromIntegerN (i - 1))

incZ :: Z -> Z
incZ (Neg I)     = Zero
incZ (Neg (S m)) = Neg m
incZ Zero        = Pos I
incZ (Pos m)     = Pos (S m)

decZ :: Z -> Z
decZ = plusZ (Neg I)

plusZ :: Z -> Z -> Z
plusZ Zero    y       = y
plusZ x       Zero    = x
plusZ (Pos m) (Pos n) = Pos (plusN m n)
plusZ (Neg m) (Neg n) = Neg (plusN m n)
plusZ (Pos m) (Neg n) = minusN m n
plusZ (Neg m) (Pos n) = minusN n m

minusZ :: Z -> Z -> Z
minusZ x y = x `plusZ` negateZ y

timesZ :: Z -> Z -> Z
timesZ Zero    _       = Zero
timesZ _       Zero    = Zero
timesZ (Pos m) (Pos n) = Pos (timesN m n)
timesZ (Pos m) (Neg n) = Neg (timesN m n)
timesZ (Neg m) (Pos n) = Neg (timesN m n)
timesZ (Neg m) (Neg n) = Pos (timesN m n)

absZ :: Z -> Z
absZ (Neg m) = Pos m
absZ x       = x

signumZ :: Z -> Z
signumZ Zero    = Zero
signumZ (Pos _) = Pos I
signumZ (Neg _) = Neg I

negateZ :: Z -> Z
negateZ (Pos n) = Neg n
negateZ Zero    = Zero
negateZ (Neg n) = Pos n

fromIntegerZ :: Integer -> Z
fromIntegerZ 0             = Zero
fromIntegerZ i | i < 0     = Neg (fromIntegerN (negate i))
               | otherwise = Pos (fromIntegerN i)

lengthZ :: [a] -> Z
lengthZ []     = Zero
lengthZ (_:xs) = incZ (lengthZ xs)
