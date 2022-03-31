{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Interpreter where

--

data Maybe2 a = Nothing2 | Just2 a
  deriving Show

instance Functor Maybe2 where
  fmap _ Nothing2  = Nothing2
  fmap f (Just2 x) = Just2 (f x)

instance Applicative Maybe2 where
  pure = Just2
  Nothing2 <*> _        = Nothing2
  _        <*> Nothing2 = Nothing2
  Just2 f  <*> Just2 x  = Just2 (f x)

instance Monad Maybe2 where
  Nothing2 >>= _ = Nothing2
  Just2 x  >>= f = f x

lookup2 :: Eq a => a -> [(a, b)] -> Maybe2 b
lookup2 _ []                        = Nothing2
lookup2 k ((k2, v):kvs) | k == k2   = Just2 v
                        | otherwise = lookup2 k kvs

foldl2 :: (a -> a -> a) -> a -> [a] -> a
foldl2 _ e []     = e
foldl2 f e (x:xs) = foldl2 f (f e x) xs

foldl12 :: (a -> a -> a) -> [a] -> a
foldl12 f (x:xs) = foldl2 f x xs

--

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

evalA :: Env -> AExpr -> Maybe2 Integer
evalA _   (Lit i)     = Just2 i
evalA env (Var v)     = lookup2 v env
evalA env (Add e1 e2) = (+) <$> evalA env e1 <*> evalA env e2
evalA env (Sub e1 e2) = (-) <$> evalA env e1 <*> evalA env e2
evalA env (Mul e1 e2) = (*) <$> evalA env e1 <*> evalA env e2
evalA env (Div e1 e2) = div <$> evalA env e1 <*> evalA env e2

evalB :: Env -> BExpr -> Maybe2 Bool
evalB _   Tru         = Just2 True
evalB env (Lt e1 e2)  = (<)  <$> evalA env e1 <*> evalA env e2
evalB env (Eq e1 e2)  = (==) <$> evalA env e1 <*> evalA env e2
evalB env (Not e)     = not  <$> evalB env e
evalB env (And e1 e2) = (&&) <$> evalB env e1 <*> evalB env e2
evalB env (Or e1 e2)  = (||) <$> evalB env e1 <*> evalB env e2

run :: Env -> Cmd -> Maybe2 Env
run env Skip          = Just2 env
run env (Assign v a)  = evalA env a >>= \i -> Just2 ((v, i) : env)
run env (Seq c1 c2)   = run env c1 >>= \env' -> run env' c2
run env (Ite e c1 c2) = evalB env e >>= \b -> run env (if b then c1 else c2)
run env (While e c)   = evalB env e >>= \b -> run env (if b then Seq c (While e c) else Skip)
run _   Error         = Nothing2

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
            (foldl12 Seq [ Assign "Y" (Lit 1)
                         , While (Not (Eq (Var "X") (Lit 0))) (foldl12 Seq [ Assign "Y" (Mul (Var "Y") (Var "X"))
                                                                           , Assign "X" (Sub (Var "X") (Lit 1))
                                                                           ])
                         ])

test x = run [("X", x)] example >>= lookup2 "Y"

-- Test with: $(inv 'test) (Just2 3628800)

--

-- Equivalent test program in Haskell

reference :: Integer -> Maybe2 Integer
reference x = if x < 0 then Nothing2 else Just2 (reference' x)
  where reference' :: Integer -> Integer
        reference' 0  = 1
        reference' x' = (*) x' (reference' ((-) x' 1))

-- Test with: $(inv 'reference) (Just2 3628800)
