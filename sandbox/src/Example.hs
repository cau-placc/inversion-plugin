{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Example where

data X = A | B | C | D
  deriving (Eq, Ord, Enum)

class C a where
  some :: a

instance C X where

enumAlias :: X -> [X]
enumAlias = enumFrom

class Functor2 f where
  fmap2 :: (a -> b) -> f a -> f b

lengthNum :: Num n => [a] -> n
lengthNum []     = 0
lengthNum (_:xs) = 1 + lengthNum xs

map2 :: (a -> b) -> [a] -> [b]
map2 _ []     = []
map2 f (x:xs) = f x : map2 f xs

map3 :: (Bool -> Bool) -> [Bool] -> [Bool]
map3 _ []     = []
map3 f (x:xs) = f True : map3 f xs

isNullChar :: Char -> Bool
isNullChar '\0' = True
isNullChar _    = False

absurdIntId :: (a, Int) -> a
absurdIntId (a, b) =
  if b == 5
    then if b == 6
      then a
    else absurd
  else absurd

id2 :: a -> a
id2 x = x

id6 :: Int -> Int
id6 x = if x == 6 then x else x

id7 :: Char -> Char
id7 x = if x == 'a' then x else x

absurd :: a
absurd = error "absurd"

is42 :: (Eq a, Num a) => a -> Bool
is42 42 = True
is42 _ = False

is0 :: (Eq a, Num a) => a -> Bool
is0 0 = True
is0 _ = False

ctest :: Integer -> Integer -> Bool
ctest x y = if x == y then True else False

const2 :: a -> b -> a
const2 x _ = x
-- map id $ const2InvNF True :: [(Bool, Maybe2 (Maybe2 Bool))]

and2 :: Bool -> Bool -> Bool
and2 True True = True
and2 _    _    = False
-- map id $ and2Inv False
-- map id $ and2InvNF False

null2 :: [a] -> Bool
null2 [] = True
null2 _  = False
-- take 10 $ null2Inv False :: [[Maybe2 Bool]]
-- take 10 $ null2InvNF False :: [[Maybe2 Bool]]

infixr 5 +++
(+++) :: [a] -> [a] -> [a]
(+++) [] ys = ys
(+++) (x:xs) ys = x : xs +++ ys

append2 :: [a] -> [a] -> [a]
append2  = (+++)

reverse2 :: [a] -> [a]
reverse2 [] = []
reverse2 (x:xs) = append2 (reverse2 xs) [x]

foldr2 :: (a -> b -> b) -> b -> [a] -> b
foldr2 _ e []     = e
foldr2 f e (x:xs) = f x (foldr2 f e xs)

concat2 :: [[a]] -> [a]
concat2 = foldr2 append2 []

compose2 :: (a -> b) -> (c -> a) -> c -> b
compose2 = (.)

data Maybe2 a = Nothing2 | Just2 a

undefined2 :: a
undefined2 = undefined

isJust2 :: Maybe2 a -> Bool
isJust2 Nothing2 = False
isJust2 (Just2 _) = True

lookup2 :: Eq a => a -> [(a, b)] -> Maybe2 b
lookup2 _ [] = Nothing2
lookup2 k ((k2,v):kvs) = if k == k2 then Just2 v else lookup2 k kvs

newtype List2 a = List2 [a]

fromList2 :: List2 a -> [a]
fromList2 (List2 xs) = xs

test :: List2 a -> Bool
test x = case x of
  List2 _ -> True

dup2 :: a -> (a, a)
dup2 x = (x, x)

hasDuplicatesPat :: a -> [a] -> [a] -> [a] -> [a]
hasDuplicatesPat x a b c = a +++ x : b +++ x : c

showInteger :: Integer -> String
showInteger = show

constrainedShowInt :: Int -> String
constrainedShowInt n = if n == 5 then show n else absurd

unit :: ()
unit = ()

mkPalindrome :: Maybe2 a -> [a] -> [a]
mkPalindrome Nothing2 xs = xs `append2` (reverse2 xs)
mkPalindrome (Just2 x) xs = xs `append2` (x : reverse2 xs)

isPalindrome :: Eq a => [a] -> Bool
isPalindrome xs = xs == reverse2 xs
-- TODO: Notice the difference between the two versions regarding the Eq2 context.
-- The problem is known from functional logic programming. The strict equality
-- is part of the Unifiable class. An operator with the same semantics at source
-- level could be provided (like '===' in Curry).

f :: [()] -> Maybe2 [()]
f x = if lengthNum x == (1 :: Integer) then Just2 x else Nothing2

data Rec = RecX { selector :: Bool } | RecY
  deriving Show

data Rec2 = RecX2 Bool | RecY2
  deriving Show

selector2 :: Rec2 -> Bool
selector2 (RecX2 x) = x
selector2 (RecY2 ) = absurd

not2 :: Bool -> Bool
not2 True = False
not2 False = True

idList :: [a] -> [a]
idList x = reverse2 . reverse2
