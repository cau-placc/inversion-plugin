{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
{-# OPTIONS_GHC -dcore-lint #-}
{-# LANGUAGE LambdaCase #-}

module Janus where

import Data.Maybe (fromJust)

{-
procedure fib(int x1, int x2, int n)
    if n = 0 then
        x1 += 1 + 1
        x2 += 1
    else
        n -= 1
        call fib(x1, x2, n)
        x1 += x2
        x1 <=> x2
    fi x1 = x2

procedure main()
    int x1
    int x2
    int n
    n += 4
    call fib(x1, x2, n)


-}

type Id = String

type Val = Int

data Exp
    = Var Id
    | Val Val
    | Eq Exp Exp
    | Add Exp Exp
    | Sub Exp Exp
    | Lt Exp Exp
  deriving Show

--data Op = Eq | Plus | Minus --TODO: BinOp einführen

data Stm = Skip
         | Seq Stm Stm
         | Mod Id Mod Exp
         | Swap Id Id
         | If Exp Stm Stm Exp
         | Do Exp Stm Stm Exp
         -- | Call Id
         -- | Uncall Id
  deriving Show

data Mod = Plus | Minus
  deriving Show

type Env = [(Id, Val)]

--TODO: Enum for Bool
boolToInt :: Bool -> Int
boolToInt False = 0
boolToInt _ = 1

find :: Id -> Env -> Val
find v env = case lookup v env of
    Nothing -> 0
    Just x  -> x

eval :: Exp -> Env -> Val
eval (Var v) env = find v env
eval (Val x) _ = x
eval (Eq e1 e2) env = boolToInt ((==) (eval e1 env) (eval e2 env))
eval (Add e1 e2) env = (+) (eval e1 env) (eval e2 env)
eval (Sub e1 e2) env = (-) (eval e1 env) (eval e2 env)
eval (Lt e1 e2) env = boolToInt ((<) (eval e1 env) (eval e2 env))

run :: Env -> Stm -> Maybe Env
run env Skip = Just env
run env (Seq s1 s2) = run env s1 >>= \env' -> run env' s2
run env (Mod v m e) =
    let op = case m of
                  Plus -> (+)
                  Minus -> (-)
    in return ((v, op (find v env) (eval e env)) : env)
run env (Swap v1 v2) = return ((v1, find v2 env) : (v2, find v1 env) : env)
run env (If e1 s1 s2 e2) = case eval e1 env of
    0 -> run env s2 >>= \env2 -> case eval e2 env2 of
        0 -> Just env2
        _ -> Nothing
    _ -> run env s1 >>= \env2 -> case eval e2 env2 of
        0 -> Nothing
        _ -> Just env2
run env (Do e1 s1 s2 e2) = case eval e1 env of
    0 -> Nothing
    _ -> go env
  where go env' = run env' s1 >>= \env2 -> case eval e2 env2 of
                    0 -> run env2 s2 >>= \env3 -> case eval e1 env3 of
                      0 -> go env3
                      _ -> Nothing
                    _ -> return env2

{-
// Computes the n-th Fibonacci number in x1 and the (n+1)-th Fibonacci number in x2
procedure fibrec
    if n = 0 then
        x1 += 1
        x2 += 1
    else
        n -= 1
        call fibrec
        x1 += x2
        x1 <=> x2
    fi x1 = x2
-}
fibrecStm :: Stm
fibrecStm = If
    (Eq (Var "n") (Val 0))
    (foldl1 Seq
        [ Mod "x1" Plus (Val 1)
        , Mod "x2" Plus (Val 1)
        ])
    (foldl1 Seq
        [ Mod "n" Minus (Val 1)
        , Call "fibrec"
        , Mod "x2" Plus (Var "x2")
        , Swap "x1" "x2"
        ])
    (Eq (Var "x1") (Var "x2"))

fibrec :: Int -> Int
fibrec n | n >= 0, Just i <- run [("n", n)] fibrecStm >>= lookup "x1" = i

{-
// Computes the n-th Fibonacci number in x1 and the (n+1)-th Fibonacci number in x2
procedure fibiter
    x1 += 1
    x2 += 1
    if n = 0 then
        skip
    else
        from x1 = x2
        do
            x1 += x2
            x1 <=> x2
            n -= 1
        until n = 0
    fi x1 = x2
-}
fibiterStm :: Stm
fibiterStm = foldl1 Seq
    [ Mod "x1" Plus (Val 1)
    , Mod "x2" Plus (Val 1)
    , If (Eq (Var "n") (Val 0))
        Skip
        (Do (Eq (Var "x1") (Var "x2"))
            (foldl1 Seq
                [ Mod "x1" Plus (Var "x2")
                , Swap "x1" "x2"
                , Mod "n" Minus (Val 1)
                ])
            Skip
            (Eq (Var "n") (Val 0)))
        (Eq (Var "x1") (Var "x2"))
    ]

fibiter :: Int -> Int
fibiter n | n >= 0, Just i <- run [("n", n)] fibiterStm >>= lookup "x1" = i

{-
There are no parameters to procedures, so all variable passing is done by side-effects on the global store.
-}
