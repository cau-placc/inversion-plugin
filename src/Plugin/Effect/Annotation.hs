{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings  #-}
{-|
Module      : Plugin.Effect.Annotation
Description : Effect annotation used by the plugin
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains the data type that is used by the plugin to mark
plugin-compiled modules.
-}
module Plugin.Effect.Annotation (InvertTag(..)) where

import Data.Data

import Outputable

-- | This data type is used to tag plugin-compiled modules.
data InvertTag = Invertible
  deriving (Eq, Data)

instance Outputable InvertTag where
  ppr _ = "Invertible"
