{-# LANGUAGE TypeFamilies #-}

module Plugin.BuiltIn.Primitive where

import Plugin.Lifted

newtype IntFL (m :: * -> *) = IntFL Int

type instance Lifted m Int = IntFL m

newtype IntegerFL (m :: * -> *) = IntegerFL Integer

type instance Lifted m Integer = IntegerFL m

newtype FloatFL (m :: * -> *) = FloatFL Float

type instance Lifted m Float = FloatFL m

newtype DoubleFL (m :: * -> *) = DoubleFL Double

type instance Lifted m Double = DoubleFL m

newtype CharFL (m :: * -> *) = CharFL Char

type instance Lifted m Char = CharFL m
