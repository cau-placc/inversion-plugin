{-# OPTIONS_GHC -fplugin Plugin.NLPlugin -ddump-rn #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
module NLPluginTest where

import Plugin.Effect.Monad
import Plugin.BuiltIn ()
import Plugin.InversionPlugin
import Example ((+++))

f :: (Invertible a) => a -> [a] -> [a] -> a
f x y@[x] y = x
f x _     ($(funPat '(++) [p| _ |] [p| [x] |])) = x
