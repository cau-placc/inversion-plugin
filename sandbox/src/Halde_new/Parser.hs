{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Parser where

data Expr = Add Expr Expr | Num Int deriving (Eq, Show)

pretty :: Expr -> String
pretty (Num _)   = "2"
pretty (Add a b) = pretty a ++ " + " ++ pretty b
