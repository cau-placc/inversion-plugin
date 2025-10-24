{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
--{-# OPTIONS_GHC -ddump-splices #-}

module Parser2 where

import Plugin.InversionPlugin

import Parser

prettyInv :: String -> [Expr]
prettyInv str = $(inv 'pretty) str
