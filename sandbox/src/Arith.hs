{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Arith where

con :: Int
con = 42

con2 :: () -> Int
con2 () = 42

plus :: Num a => a -> a -> a
plus = (+)

someArith :: Num a => a -> a -> a
someArith x y = x * 42 + y -- take 30 $ $(inv 'someArith) 42 -- 16s

ack, ackG :: (Ord a, Num a) => a -> a -> a
ack 0 n = n + 1
ack m 0 = ack (m - 1) 1
ack m n = ack (m - 1) (ack m (n - 1))
--  ^ Bad, because it allows negative numbers for m n that could be generated and result in an endless loop
-- (not endless, because int is bounded, but you get it)

ackG 0 n | n >= 0 = n + 1
ackG m 0 | m >= 0 = ackG (m - 1) 1
ackG m n | m >= 0 && n >= 0 = ackG (m - 1) (ackG m (n - 1)) -- $(inv 'ackG) 43

ackSame :: (Ord a, Num a) => a -> a
ackSame n = ackG n n

isAckRes :: (Ord a, Num a) => a -> a -> a -> Bool
isAckRes n m r = ackG n m == r -- take 10 $ $(inv 'isAckRes) True -- 16s

cantor :: (Ord a, Num a, Integral a) => a -> a -> a
cantor x y | x >= 0 && y >= 0 = ((x + y) * (x + y + 1) `div` 2) + y -- $(inv 'cantor) 14
-- ^ 1 res immediately, but takes a loooooooooong time to terminate










-- 0 == (V -1)
-- (V 0) == (V -2) + 1

-- ack (v -1) (v -2) = 1