{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Interpreter where

import Z

type VarName = String

data Cmd a = Skip
           | Assign VarName (AExpr a)
           | Seq (Cmd a) (Cmd a)
           | Ite (BExpr a) (Cmd a) (Cmd a)
           | While (BExpr a) (Cmd a)
           | Error
  deriving Show

data AExpr a = Lit a
             | Var VarName
             | Add (AExpr a) (AExpr a)
             | Sub (AExpr a) (AExpr a)
             | Mul (AExpr a) (AExpr a)
  deriving Show

data BExpr a = Tru
             | Lt (AExpr a) (AExpr a)
             | Eq (AExpr a) (AExpr a)
             | Not (BExpr a)
             | And (BExpr a) (BExpr a)
             | Or (BExpr a) (BExpr a)
  deriving Show

type Env a = [(VarName, a)]

evalA :: (Num a, Ord a) => Env a -> AExpr a -> Maybe a
evalA _   (Lit i)     = Just i
evalA env (Var v)     = lookup v env
evalA env (Add e1 e2) = (+) <$> evalA env e1 <*> evalA env e2
evalA env (Sub e1 e2) = (-) <$> evalA env e1 <*> evalA env e2
evalA env (Mul e1 e2) = (*) <$> evalA env e1 <*> evalA env e2

evalB :: (Num a, Ord a) => Env a -> BExpr a -> Maybe Bool
evalB _   Tru         = Just True
evalB env (Lt e1 e2)  = (<)  <$> evalA env e1 <*> evalA env e2
evalB env (Eq e1 e2)  = (==) <$> evalA env e1 <*> evalA env e2
evalB env (Not e)     = not  <$> evalB env e
evalB env (And e1 e2) = (&&) <$> evalB env e1 <*> evalB env e2
evalB env (Or e1 e2)  = (||) <$> evalB env e1 <*> evalB env e2

run :: (Num a, Ord a) => Env a -> Cmd a -> Maybe (Env a)
run env Skip          = Just env
run env (Assign v a)  = evalA env a >>= \i -> Just ((v, i) : env)
run env (Seq c1 c2)   = run env c1 >>= \env' -> run env' c2
run env (Ite e c1 c2) = evalB env e >>= \b -> run env (if b then c1 else c2)
run env (While e c)   = evalB env e >>= \b -> run env (if b then Seq c (While e c) else Skip)
run _   Error         = Nothing

--

-- Faculty test program
-- Expects input in variable X, puts output in variable Y

-- IF X < 0 THEN
--   ERROR
-- ELSE
--   Y = 1;
--   WHILE NOT(X == 0) DO
--     Y = Y * X;
--     X = X - 1
--   OD
-- FI

example :: (Num a, Ord a) => Cmd a
example = Ite (Lt (Var "X") (Lit 0)) Error
            (foldl1 Seq [ Assign "Y" (Lit 1)
                        , While (Not (Eq (Var "X") (Lit 0))) (foldl1 Seq [ Assign "Y" (Mul (Var "Y") (Var "X"))
                                                                         , Assign "X" (Sub (Var "X") (Lit 1))
                                                                         ])
                        ])

test :: (Num a, Ord a) => a -> Maybe a
test x = run [("X", x)] example >>= lookup "Y"

-- Test with: head $ $(inv 'test) (Just 3628800)

--

-- Equivalent test program in Haskell

ref :: (Num a, Ord a) => a -> Maybe a
ref x = if x < 0 then Nothing else Just (ref' x)
  where ref' 0  = 1
        ref' x' = x' * ref' (x' - 1)

-- Test with: head $ $(inv 'ref True) (Just 3628800)
