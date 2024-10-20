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

instance HasPrimitiveInfo a => HasPrimitiveInfo (IdentityFL FL a) where
  primitiveInfo = NoPrimitive

instance HasPrimitiveInfo a => Instantiatable (IdentityFL FL a) where
  enumerate = [IdentityFL <$> share free]
  enumerateSame (IdentityFL _) = head enumerate

instance To a => To (Identity a) where
  toWith tf (Identity x) = IdentityFL (tf x)

instance From a => From (Identity a) where
  from (IdentityFL x) = Identity (fromFL x)

instance Unifiable a => Unifiable (IdentityFL FL a) where
  unify (IdentityFL x) (IdentityFL y) = unifyFL x y
  nonStrictUnify (IdentityFL x) (IdentityFL y) = nonStrictUnifyFL x y

instance NormalForm a => NormalForm (IdentityFL FL a) where
  normalFormWith nf = \case
    IdentityFL x -> FL $
      unFL (nf x) >>= \y ->
        unFL (return (IdentityFL (FL (return y))))

instance ShowFree a => ShowFree (Identity a) where
  showsFreePrec' d (Identity x) = showParen (d > 10) $
    showString "Identity " . showsFreePrec 11 x
