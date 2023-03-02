{-# LANGUAGE TypeFamilies #-}

module Plugin.BuiltIn.Primitive where

import Data.Kind

import Plugin.Lifted

newtype IntFL (m :: Type -> Type) = IntFL Int

type instance Lifted m Int = IntFL m

newtype IntegerFL (m :: Type -> Type) = IntegerFL Integer

type instance Lifted m Integer = IntegerFL m

newtype FloatFL (m :: Type -> Type) = FloatFL Float

type instance Lifted m Float = FloatFL m

newtype DoubleFL (m :: Type -> Type) = DoubleFL Double

type instance Lifted m Double = DoubleFL m

newtype CharFL (m :: Type -> Type) = CharFL Char

type instance Lifted m Char = CharFL m
