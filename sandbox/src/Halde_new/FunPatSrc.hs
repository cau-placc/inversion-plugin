{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
{-# OPTIONS_GHC -ddump-tc -ddump-splices #-}

-- {-# OPTIONS_GHC -fplugin-opt Plugin.InversionPlugin:dump-pattern-matched #-}
-- {-# OPTIONS_GHC -fplugin-opt Plugin.InversionPlugin:dump-gen-instances #-}
--{-# OPTIONS_GHC -ddump-tc #-}

module FunPatSrc where

type A a b = (a, b)
data B a b = B a b

g x y = (x, y)

pat y = g (id y) y

test f g x = f g x

id2 :: a -> b
id2 _ = undefined
{-
$(inv 'id2 True)
  :: (Plugin.Effect.Monad.NormalForm a1,
      Plugin.Effect.Monad.HasPrimitiveInfo
        (Lifted Plugin.Effect.Monad.FL a1),
      Plugin.Effect.Monad.Unifiable a2,
      Plugin.Effect.Monad.Convertible a1,
      Plugin.Effect.Monad.Convertible a2) =>
     a2 -> [Solo a1]
     ausgaben von inversen müssen from sein, normalform haben und primitiveinfo haben,
     eingaben selbiger müssen to sein und unifizerbar
-}

f2 :: (a -> b) -> c -> d
f2 _ _ = error "bla"

h :: Bool -> Bool
h x = True

append :: [a] -> [a] -> [a]
append [] ys = ys
append (x:xs) ys = x : append xs ys

append2 = \xs -> \ys -> case xs of
  [] -> ys
  (x:xs) -> x : append2 xs ys

f :: a -> b
f x = error "bla"

g2 :: a -> b -> c
g2 x y = error "bla"

loopTest False = loopTest False
loopTest True = True


ctest :: [a] -> b -> c
ctest x y = error "bla"

mapBool :: (Bool -> Bool) -> [Bool] -> [Bool]
mapBool f [] = []
mapBool f (x:xs) = f x : mapBool f xs


myzip :: [a] -> [b] -> [(a, b)]
myzip [] _ = []
myzip _ [] = []
myzip (x:xs) (y:ys) = (x, y) : myzip xs ys

mylookup :: Eq a => a -> [(a, b)] -> Maybe b
mylookup _ [] = Nothing
mylookup x ((y, z):ys) = if x == y then Just z else mylookup x ys

mynull :: [a] -> Bool
mynull [] = True
mynull _ = False

nand :: Bool -> Bool -> Bool
nand True True = False
nand _ _ = True
