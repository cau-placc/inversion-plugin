{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Lambda where

data P = Z | S P
  deriving (Ord, Show)

instance Eq P where
  Z     == Z     = True
  (S m) == (S n) = m == n
  _     == _     = False

data E
  = EApp E E
  | EAbs E
  | EVar P  -- EVar n refers to the variable bound by the nth-innermost abstraction
  deriving (Show)

eval :: E -> E
eval (EApp fun arg) = case eval fun of
  EAbs body -> eval (sub Z body) where
                sub n e = case e of
                  EApp e1 e2 -> EApp (sub n e1) (sub n e2)
                  EAbs e' -> EAbs (sub (S n) e')
                  EVar n' | n == n'    -> arg  -- substitute. arg has no free vars.
                          | otherwise  -> EVar n'
  other -> EApp other arg
eval x = x

quine :: E
quine = EApp (EAbs (EApp (EVar Z) (EVar Z))) (EAbs (EApp (EVar Z) (EVar Z)))
