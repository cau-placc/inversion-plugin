{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module InstanceExport where

newtype Id a = Id a
  deriving Show

instance Functor Id where
  fmap f (Id a) = Id (f a)

instance Applicative Id where
  pure = Id
  Id f <*> Id a = Id (f a)

instance Monad Id where
  Id x >>= f = f x
