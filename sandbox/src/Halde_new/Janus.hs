{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
{-# OPTIONS_GHC -dcore-lint #-}

module Janus where

type Id = String

type Val = Int

data Exp
    = Var Id
    | Val Val
    | Bin Exp Op Exp

data Op
    = Eq
    | Add
    | Sub

data Stm
    = Skip
    | Seq Stm Stm
    | Mod Id Mod Exp
    | Swap Id Id
    | If Exp Stm Stm Exp
    | Do Exp Stm Stm Exp
    | Call Id
    | Uncall Id

data Mod = Plus | Minus

type Prog = [(Id, Stm)]

type Env = [(Id, Val)]

find :: Id -> Env -> Val
find v env = case lookup v env of
    Nothing -> 0
    Just x  -> x

eval :: Env -> Exp -> Val
eval env (Var v)        = find v env
eval _   (Val x)        = x
eval env (Bin e1 op e2) = f (eval env e1) (eval env e2)
  where
    f = case op of
        Eq  -> \x1 x2 -> case x1 == x2 of
            False -> 0
            True  -> 1
        Add -> (+)
        Sub -> (-)

run :: Prog -> Env -> Stm -> Maybe Env
run _ env Skip             = return env
run p env (Seq s1 s2)      = run p env s1 >>= \env2 -> run p env2 s2
run _ env (Mod v m e)      = return ((v, f (find v env) (eval env e)) : env)
  where
    f = case m of
        Plus  -> (+)
        Minus -> (-)
run _ env (Swap v1 v2)     = return ((v1, find v2 env) : (v2, find v1 env) : env)
run p env (If e1 s1 s2 e2) = case eval env e1 of
    0 -> run p env s2 >>= \env2 -> case eval env2 e2 of
        0 -> Just env2
        _ -> Nothing
    _ -> run p env s1 >>= \env2 -> case eval env2 e2 of
        0 -> Nothing
        _ -> Just env2
run p env (Do e1 s1 s2 e2) = case eval env e1 of
    0 -> Nothing
    _ -> go env
  where
    go env' = run p env' s1 >>= \env2 -> case eval env2 e2 of
        0 -> run p env2 s2 >>= \env3 -> case eval env3 e1 of
            0 -> go env3
            _ -> Nothing
        _ -> return env2
run p env (Call f)         = lookup f p >>= \s -> run p env s
run p env (Uncall f)       = lookup f p >>= \s -> run p env (inv2 s)

inv2 :: Stm -> Stm
inv2 Skip             = Skip
inv2 (Seq s1 s2)      = Seq (inv2 s2) (inv2 s1)
inv2 (Mod v m e)      = Mod v m' e
  where
    m' = case m of
        Plus  -> Minus
        Minus -> Plus
inv2 (Swap v1 v2)     = Swap v1 v2
inv2 (If e1 s1 s2 e2) = If e2 (inv2 s1) (inv2 s2) e1
inv2 (Do e1 s1 s2 e2) = Do e2 (inv2 s1) (inv2 s2) e1
inv2 (Call f)         = Uncall f
inv2 (Uncall f)       = Call f

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
    (Bin (Var "n") Eq (Val 0))
    (foldl1 Seq
        [ Mod "x1" Plus (Val 1)
        , Mod "x2" Plus (Val 1)
        ])
    (foldl1 Seq
        [ Mod "n" Minus (Val 1)
        , Call "fibrec"
        , Mod "x1" Plus (Var "x2")
        , Swap "x1" "x2"
        ])
    (Bin (Var "x1") Eq (Var "x2"))

fibrec :: Int -> Int
fibrec n | n >= 0, Just res <- run [("fibrec", fibrecStm)] [("n", n)] (Call "fibrec") >>= return . find "x1" = res

fibrecPair :: Int -> (Int, Int)
fibrecPair n | n >= 0, Just res <- run [("fibrec", fibrecStm)] [("n", n)] (Call "fibrec") >>= \env -> return (find "x1" env, find "x2" env) = res

-- Old-school Haskell fib
fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

-- Old-school Haskell fib
fibPair :: Int -> (Int, Int)
fibPair 0 = (0, 1)
fibPair n | n > 0 = let (a, b) = fibPair (n - 1) in (b, a + b)

fibAcc :: Int -> Int
fibAcc n = fibAcc' n 1 1
  where
    fibAcc' 0 a _ = a
    fibAcc' m a b | m > 0 = fibAcc' (m - 1) b (a + b)

fibrecUncall :: Int -> Int -> Int
fibrecUncall x1 x2 | Just res <- run [("fibrec", fibrecStm)] [("x1", x1), ("x2", x2)] (Uncall "fibrec") >>= return . find "n" = res

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
    , If (Bin (Var "n") Eq (Val 0))
        Skip
        (Do (Bin (Var "x1") Eq (Var "x2"))
            (foldl1 Seq
                [ Mod "x1" Plus (Var "x2")
                , Swap "x1" "x2"
                , Mod "n" Minus (Val 1)
                ])
            Skip
            (Bin (Var "n") Eq (Val 0)))
        (Bin (Var "x1") Eq (Var "x2"))
    ]

fibiter :: Int -> Int
fibiter n | n >= 0, Just res <- run [("fibiter", fibiterStm)] [("n", n)] (Call "fibiter") >>= return . find "x1" = res

fibiterPair :: Int -> (Int, Int)
fibiterPair n | n >= 0, Just res <- run [("fibiter", fibiterStm)] [("n", n)] (Call "fibiter") >>= \env -> return (find "x1" env, find "x2" env) = res

fibiterTriple :: Int -> Int -> Int -> (Int, Int, Int)
fibiterTriple n x1 x2 | Just res <- run [("fibiter", fibiterStm)] [("n", n), ("x1", x1), ("x2", x2)] (Call "fibiter") >>= \env -> return (find "n" env, find "x1" env, find "x2" env) = res

fibiterUncall :: Int -> Int -> Int
fibiterUncall x1 x2 | Just res <- run [("fibiter", fibiterStm)] [("x1", x1), ("x2", x2)] (Uncall "fibiter") >>= return . find "n" = res

fibiterUncall2 :: Int -> Int -> Int -> (Int, Int, Int)
fibiterUncall2 n x1 x2 | Just res <- run [("fibiter", fibiterStm)] [("n", n), ("x1", x1), ("x2", x2)] (Uncall "fibiter") >>= \env -> return (find "n" env, find "x1" env, find "x2" env) = res

{-
Tests:
$(Plugin.InversionPlugin.inv 'fibiterTriple) (0,8,12)
-}

{-
There are no parameters to procedures, so all variable passing is done by side-effects on the global store.
-}
