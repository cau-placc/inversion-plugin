{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Plugin.Lifted where

import Data.Kind

type family Lifted (m :: Type -> Type) (a :: k) = (b :: k) | b -> m a
