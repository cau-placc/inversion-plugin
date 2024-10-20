--{-# LANGUAGE TemplateHaskell, StandaloneDeriving, FlexibleContexts, ExtendedDefaultRules, ViewPatterns, ScopedTypeVariables #-}
-- TODO: Palindrome example needs flexible contexts.
{-# LANGUAGE TemplateHaskell, FlexibleContexts, PartialTypeSignatures #-}
module Main where

import Plugin.InversionPlugin

import Arith

--test :: _ => _
--test = $(inClassInv '(++) [| var 1 |] [| (:) (var 2) ((:) (var 2) []) |])

--test' :: _ => _
--test' = $(inClassInv '(++) [| (:) True [] |] [| (:) (var 2) ((:) (var 2) []) |])


--TODO: welche eingaben liefern einen bestimmten wert (testfälle interessant)
test2 :: _ => _
test2 = let x = someShit 1 in (x,x)

someShit :: Ord n => Integer -> [n]
someShit _ = []

appendInv42 :: _ => _
appendInv42 = $(inClassInv '(++) [[| var 1 |], [| [var 2] |]])
--TODO: anonVar introducen


--myNotInv = $(inv 'myNot)

--testf = $(inv 'unlines)

appendInv42' :: _ => _
appendInv42' x = $(inOutClassInv '(++) [[| var 1 |], [| [var 2] |]] [| x |])


appendInv422 :: _ => _
appendInv422 = $(inOutClassInv '(++) [[| var 1 |], [| [False] |]] [| var 2 |])
{-
\x -> $(inOutClassInv 'sort [[| x |]] [| 2:var 1 |])
-}

--test3 :: [Int]
--test3 = map snd ($(inClassInv '(++) [| var 1 |] [| (:) (var 2) ((:) (var 2) []) |]) [True])


-- (...) :: _ =>
-- let b :: _ => _
--     b = (...)
-- in b

--TEst: map showFree $ ($(genInOutClassInverse 'id True [[| (var 1, var 2, var 3) |]] [| (var 1, var 2, var 3)  |]) :: [(Bool, Bool, Bool)])

main = return ()

{-import Control.Applicative
import Control.Monad
import Data.Maybe

import Plugin.InversionPlugin

import Example
import qualified Example0 as E (append)
import Peano
import Compression
import NonLinear
import Arith

import System.Environment

main :: IO ()
main = do
  args <- getArgs
  case args of
    []       -> return ()
    arg : _ ->
      let n = read arg :: Int
       in print $
            -- last (take n (repeat ()))
            last2 (take n (repeat ()))

deriving instance Show a => Show (List2 a)
deriving instance Show a => Show (Maybe2 a)

last2 :: Invertible a => [a] -> a
last2 $(funPat 'E.append [p| _ |] [p| [x] |]) = x

last3 :: Invertible a => [a] -> a
last3 ((\arg -> [ res | res@(_ , [_]) <- $(inv 'E.append) arg]) -> (_, [x]) : _) = x

absurdPat :: Int -> Int
absurdPat $(funPat 'absurdIntId [p| (x, _) |]) = x

id3 :: Invertible a => a -> a
id3 $(funPat 'id2 [p| x |]) = x

id4 :: Invertible a => a -> a
id4 $(funPat 'const2 [p| x |] [p| (y :: Bool) |]) = x

fromSame :: Invertible a => (a, a) -> a
fromSame $(funPat 'dup2 [p| x |]) = x

hasDuplicates :: Invertible a => [a] -> Bool
hasDuplicates $(funPat 'hasDuplicatesPat [p| _ |] [p| _ |] [p| _ |] [p| _ |]) = True
hasDuplicates _ = False

isUnit :: () -> Bool
isUnit $(funPat 'unit) = True

reverseLookup2 :: (Invertible a, Invertible b, Eq a, Lifted (Eq a)) => [(a, b)] -> Maybe2 b -> [a]
reverseLookup2 = $(partialInv 'lookup2 [2])

testMap :: [(Peano, Maybe2 Bool)]
testMap = [(Z, Nothing2), (S (S Z), Just2 False)]

-- map id $ reverseLookup2 testMap Nothing2
-- map id $ reverseLookup2 testMap (Just2 Nothing2)
-- map id $ reverseLookup2 testMap (Just2 (Just2 False))
-- map id $ reverseLookup2 testMap (Just2 (Just2 True))

testPeano :: [Peano]
testPeano = $(inv 'isZero) False

toInt :: Peano -> Int
toInt Z     = 0
toInt (S n) = succ (toInt n)

fromInt :: Int -> Peano
fromInt 0 = Z
fromInt n = S (fromInt (pred n))

fFunPat :: Maybe2 [()] -> Bool
fFunPat $(funPat 'f [p| [()] |]) = True

fPartialFunPat :: Maybe2 [()] -> Bool
fPartialFunPat (\arg -> [res | res@(()) <- $(partialInv 'f [1]) [()] arg] -> ():_) = True

dropSuffix :: Invertible a => [a] -> [a] -> Maybe [a]
dropSuffix suff xs = listToMaybe ($(partialInv '(+++) [2]) suff xs)

decomposePalindrom $(funPat 'k1 [p| xs |])          = (Nothing, xs)
decomposePalindrom $(funPat 'k2 [p| xs |] [p| x |]) = (Just x, xs)

decomposePalindrome $(funPat 'mkPalindrome [p| mx |]  [p| xs |]) = (mx, xs)

-- f2 :: [Int] -> String
-- f2 $(funPat 'f2Helper [p| x |] [p| _ |] [p| _ |] [p| _ |]) = "matched"
-- f2 _ = "not matched"

-- f2' :: [Int] -> String
-- f2' $(funPat 'f2Helperr [p| x |] [p| y |] [p| _ |] [p| _ |] [p| _ |]) | y == x + 1 = "matched"
-- f2' _ = "not matched"

-- f3 :: [Int] -> String
-- f3 $(funPat 'f3Helper [p| x |] [p| _ |] [p| _ |] [p| _ |] [p| _ |]) = "matched"
-- f3 _ = "not matched"

-- f3' :: [Int] -> String
-- f3' $(funPat 'f3Helperr [p| x |] [p| y |] [p| z |] [p| _ |] [p| _ |] [p| _ |] [p| _ |]) | y == x + 1 && z == x + 2 = "matched"
-- f3' _ = "not matched"

-- f4 :: [Int] -> String
-- f4 $(funPat 'f4Helper [p| x |] [p| _ |] [p| _ |] [p| _ |] [p| _ |] [p| _ |]) = "matched"
-- f4 _ = "not matched"
-}
