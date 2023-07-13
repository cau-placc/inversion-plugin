{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Compiler where

data Cmd = Skip
         | Assign Id Expr
         | Seq Cmd Cmd
         | Ite Expr Cmd Cmd
         | While Expr Cmd
         | Error
  deriving Show
