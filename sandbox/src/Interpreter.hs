{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Interpreter where

type VarName = String

data Cmd = Skip
         | Assign VarName AExpr
         | Seq Cmd Cmd
         | Ite BExpr Cmd Cmd
         | While BExpr Cmd
         | Error
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

evalA :: Env -> AExpr -> Maybe Integer
evalA _   (Lit i)     = Just i
evalA env (Var v)     = lookup v env
evalA env (Add e1 e2) = (+) <$> evalA env e1 <*> evalA env e2
evalA env (Sub e1 e2) = (-) <$> evalA env e1 <*> evalA env e2
evalA env (Mul e1 e2) = (*) <$> evalA env e1 <*> evalA env e2
evalA env (Div e1 e2) = div <$> evalA env e1 <*> evalA env e2

evalB :: Env -> BExpr -> Maybe Bool
evalB _   Tru         = Just True
evalB env (Lt e1 e2)  = (<)  <$> evalA env e1 <*> evalA env e2
evalB env (Eq e1 e2)  = (==) <$> evalA env e1 <*> evalA env e2
evalB env (Not e)     = not  <$> evalB env e
evalB env (And e1 e2) = (&&) <$> evalB env e1 <*> evalB env e2
evalB env (Or e1 e2)  = (||) <$> evalB env e1 <*> evalB env e2

run :: Env -> Cmd -> Maybe Env
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

example :: Cmd
example = Ite (Lt (Var "X") (Lit 0)) Error
            (foldl1 Seq [ Assign "Y" (Lit 1)
                        , While (Not (Eq (Var "X") (Lit 0))) (foldl1 Seq [ Assign "Y" (Mul (Var "Y") (Var "X"))
                                                                         , Assign "X" (Sub (Var "X") (Lit 1))
                                                                         ])
                        ])

test x = run [("X", x)] example >>= lookup "Y"

-- Test with: head $ $(inv 'test) (Just 3628800)

--

-- Equivalent test program in Haskell

ref :: Integer -> Maybe Integer
ref x = if x < 0 then Nothing else Just (ref' x)
  where ref' :: Integer -> Integer
        ref' 0  = 1
        ref' x' = (*) x' (ref' ((-) x' 1))

-- Test with: head $ $(inv 'ref) (Just 3628800)
