{-# LANGUAGE FlexibleContexts, UndecidableInstances, TemplateHaskell, TypeFamilyDependencies, PolyKinds #-}

module Test where

import Language.Haskell.TH

class D a

instance D Bool

instance (D a, D [a]) => D [a]

class C a where
  c :: a -> a

instance (C a, C [a]) => C [a] where
  c [] = []
  c (x:xs) = c x : c xs

instance C Bool where
  c False = True
  c True  = False

type family F (a :: k) = (b :: k) | b -> a

type instance F [a] = [F a]
type instance F Bool = Bool

f :: (C a, D (F a)) => a -> a
f = c

mkF :: ExpQ
mkF = [| \x -> f x |]
