{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wno-orphans #-}
module Plugin.BuiltIn.Identity where

import Data.Functor.Identity

import Plugin.Effect.Monad
import Plugin.Lifted

newtype IdentityFL m a = IdentityFL (m a)

type instance Lifted m Identity = IdentityFL m
type instance Lifted m (Identity a) = IdentityFL m (Lifted m a)

instance (HasPrimitiveInfo a, Shareable FL (IdentityFL FL a)) => HasPrimitiveInfo (IdentityFL FL a) where
  primitiveInfo = NoPrimitive

instance (HasPrimitiveInfo a, Shareable FL (IdentityFL FL a)) => Narrowable (IdentityFL FL a) where
  narrow = [IdentityFL free]

instance To a => To (Identity a) where
  toWith tf (Identity x) = IdentityFL (tf x)

instance From a => From (Identity a) where
  from (IdentityFL x) = Identity (fromFL x)

instance (To a, Matchable a) => Matchable (Identity a) where
  match (IdentityFL x) (Identity y) = matchFL x y

instance Unifiable a => Unifiable (Identity a) where
  lazyUnify (IdentityFL x) (IdentityFL y) = lazyUnifyFL x y

instance NormalForm a => NormalForm (Identity a) where
  normalFormWith nf = \case
    IdentityFL x -> FL $
      unFL (nf x) >>= \y ->
        unFL (return (IdentityFL (FL (return y))))

instance ShowFree a => ShowFree (Identity a) where
  showsFreePrec' d (Identity x) = showParen (d > 10) $
    showString "Identity " . showsFreePrec 11 x

instance (Shareable m a, MonadShare m) => Shareable m (IdentityFL m a) where
  shareArgs (IdentityFL x) = IdentityFL <$> share x

instance Invertible a => Invertible (Identity a)
