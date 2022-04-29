{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Plugin.BuiltIn.Identity where

import Data.Functor.Identity

import Plugin.Effect.Monad
import Plugin.Lifted

newtype IdentityFL m a = IdentityFL (m a)

type instance Lifted m Identity = IdentityFL m
type instance Lifted m (Identity a) = IdentityFL m (Lifted m a)

instance HasPrimitiveInfo a => HasPrimitiveInfo (IdentityFL FL a) where
  primitiveInfo = NoPrimitive

instance HasPrimitiveInfo a => Narrowable (IdentityFL FL a) where
  narrow j = [(IdentityFL (free j), 1)]

instance Convertible a => Convertible (Identity a) where
  to (Identity x) = IdentityFL (toFL x)
  fromWith ff (IdentityFL x) = Identity (ff x)

instance (Convertible a, Matchable a) => Matchable (Identity a) where
  match (Identity x) (IdentityFL y) = matchFL x y

instance Unifiable a => Unifiable (Identity a) where
  lazyUnify (IdentityFL x) (IdentityFL y) = lazyUnifyFL x y

instance NormalForm a => NormalForm (Identity a) where
  normalFormWith nf = \case
    IdentityFL x ->
      nf x >>= \y ->
        return (FTODO (pure (IdentityFL y)))

instance ShowFree a => ShowFree (Identity a) where
  showsFreePrec' d (Identity x) = showParen (d > 10) $
    showString "Identity " . showsFreePrec 11 x

instance Invertible a => Invertible (Identity a)
