{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Plugin.Lifted where

type family Lifted (m :: * -> *) (a :: k) = (b :: k) | b -> m a