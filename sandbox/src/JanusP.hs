{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
{-# OPTIONS_GHC -dcore-lint #-}

module JanusP where

-- import P

data P = Z | S P
  deriving (Eq, Ord, Show)

toP :: Int -> P
toP 0 = Z
toP i | i > 0 = S (toP (i - 1))

fromP :: P -> Int
fromP Z     = 0
fromP (S n) = 1 + fromP n

addP :: P -> P -> P
addP Z     n = n
addP (S m) n = S (addP m n)

subP :: P -> P -> P
subP n     Z     = n
subP (S n) (S m) = subP n m

type Id = String

type Val = P

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
    Nothing -> Z
    Just x  -> x

eval :: Env -> Exp -> Val
eval env (Var v)        = find v env
eval _   (Val x)        = x
eval env (Bin e1 op e2) = f (eval env e1) (eval env e2)
  where
    f = case op of
        Eq  -> \x1 x2 -> case x1 == x2 of
            False -> Z
            True  -> S Z
        Add -> addP
        Sub -> subP

run :: Prog -> Env -> Stm -> Maybe Env
run _ env Skip             = return env
run p env (Seq s1 s2)      = run p env s1 >>= \env2 -> run p env2 s2
run _ env (Mod v m e)      = return ((v, f (find v env) (eval env e)) : env)
  where
    f = case m of
        Plus  -> addP
        Minus -> subP
run _ env (Swap v1 v2)     = return ((v1, find v2 env) : (v2, find v1 env) : env)
run p env (If e1 s1 s2 e2) = case eval env e1 of
    Z -> run p env s2 >>= \env2 -> case eval env2 e2 of
        Z -> Just env2
        _ -> Nothing
    _ -> run p env s1 >>= \env2 -> case eval env2 e2 of
        Z -> Nothing
        _ -> Just env2
run p env (Do e1 s1 s2 e2) = case eval env e1 of
    Z -> Nothing
    _ -> go env
  where
    go env' = run p env' s1 >>= \env2 -> case eval env2 e2 of
        Z -> run p env2 s2 >>= \env3 -> case eval env3 e1 of
            Z -> go env3
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
    (Bin (Var "n") Eq (Val Z))
    (foldl1 Seq
        [ Mod "x1" Plus (Val (S Z))
        , Mod "x2" Plus (Val (S Z))
        ])
    (foldl1 Seq
        [ Mod "n" Minus (Val (S Z))
        , Call "fibrec"
        , Mod "x1" Plus (Var "x2")
        , Swap "x1" "x2"
        ])
    (Bin (Var "x1") Eq (Var "x2"))

fibrec :: P -> P
fibrec n | Just res <- run [("fibrec", fibrecStm)] [("n", n)] (Call "fibrec") >>= return . find "x1" = res

fibrecPair :: P -> (P, P)
fibrecPair n | Just res <- run [("fibrec", fibrecStm)] [("n", n)] (Call "fibrec") >>= \env -> return (find "x1" env, find "x2" env) = res

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
    [ Mod "x1" Plus (Val (S Z))
    , Mod "x2" Plus (Val (S Z))
    , If (Bin (Var "n") Eq (Val Z))
        Skip
        (Do (Bin (Var "x1") Eq (Var "x2"))
            (foldl1 Seq
                [ Mod "x1" Plus (Var "x2")
                , Swap "x1" "x2"
                , Mod "n" Minus (Val (S Z))
                ])
            Skip
            (Bin (Var "n") Eq (Val Z)))
        (Bin (Var "x1") Eq (Var "x2"))
    ]

fibiter :: P -> P
fibiter n | Just res <- run [("fibiter", fibiterStm)] [("n", n)] (Call "fibiter") >>= return . find "x1" = res

fibiterPair :: P -> (P, P)
fibiterPair n | Just res <- run [("fibiter", fibiterStm)] [("n", n)] (Call "fibiter") >>= \env -> return (find "x1" env, find "x2" env) = res

fibiterTriple :: P -> P -> P -> (P, P, P)
fibiterTriple n x1 x2 | Just res <- run [("fibiter", fibiterStm)] [("n", n), ("x1", x1), ("x2", x2)] (Call "fibiter") >>= \env -> return (find "n" env, find "x1" env, find "x2" env) = res

fibiterUncall :: P -> P -> P
fibiterUncall x1 x2 | Just res <- run [("fibiter", fibiterStm)] [("x1", x1), ("x2", x2)] (Uncall "fibiter") >>= return . find "n" = res

fibiterUncall2 :: P -> P -> P -> (P, P, P)
fibiterUncall2 n x1 x2 | Just res <- run [("fibiter", fibiterStm)] [("n", n), ("x1", x1), ("x2", x2)] (Uncall "fibiter") >>= \env -> return (find "n" env, find "x1" env, find "x2" env) = res




{-
There are no parameters to procedures, so all variable passing is done by side-effects on the global store.
-}
