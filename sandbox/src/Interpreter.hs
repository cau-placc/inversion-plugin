{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Interpreter where

--

data Maybe2 a = Nothing2 | Just2 a

instance Functor Maybe2 where
  fmap _ Nothing2  = Nothing2
  fmap f (Just2 x) = Just2 (f x)

instance Applicative Maybe2 where
  pure = Just2
  Nothing2 <*> _        = Nothing2
  _        <*> Nothing2 = Nothing2
  Just2 f  <*> Just2 x  = Just2 (f x)

lookup2 :: Eq a => a -> [(a, b)] -> Maybe2 b
lookup2 _ [] = Nothing2
lookup2 k ((k2,v):kvs) | k == k2 = Just2 v
                       | otherwise = lookup2 k kvs

--

type VarName = Int

type Prog = [Cmd]

data Cmd = Skip
         | Assign VarName AExpr
         | Seq Cmd Cmd
         | Ite BExpr Cmd Cmd
         | While BExpr Cmd
  deriving Show

data AExpr = Lit Integer
           | Var VarName
           | Add AExpr AExpr
           | Sub AExpr AExpr
           | Mul AExpr AExpr
           | Div AExpr AExpr
  deriving Show

data BExpr = Tru
           | Lt AExpr AExpr
           | Eq AExpr AExpr
           | Not BExpr
           | And BExpr BExpr
           | Or BExpr BExpr
  deriving Show

type Env = [(VarName, Integer)]

evalA :: Env -> AExpr -> Maybe2 Integer
evalA _   (Lit i)     = Just2 i
evalA env (Var v)     = lookup2 v env
evalA env (Add e1 e2) = (+) <$> evalA env e1 <*> evalA env e2
evalA env (Sub e1 e2) = (-) <$> evalA env e1 <*> evalA env e2
evalA env (Mul e1 e2) = (*) <$> evalA env e1 <*> evalA env e2
evalA env (Div e1 e2) = div <$> evalA env e1 <*> evalA env e2

evalB :: Env -> BExpr -> Maybe2 Bool
evalB _   Tru         = Just2 True
evalB env (Lt e1 e2)  = (<) <$> evalA env e1 <*> evalA env e2
evalB env (Eq e1 e2)  = (==) <$> evalA env e1 <*> evalA env e2
evalB env (Not e)     = not <$> evalB env e
evalB env (And e1 e2) = (&&) <$> evalB env e1 <*> evalB env e2
evalB env (Or e1 e2)  = (||) <$> evalB env e1 <*> evalB env e2
