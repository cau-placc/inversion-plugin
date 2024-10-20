{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Interpreter2 where

type VarName = String

data Cmd = Skip
         | Assign VarName LExpr
         | Seq Cmd Cmd
         | Ite BExpr Cmd Cmd
         | While BExpr Cmd
  deriving Show

data LExpr = Var String
           | Nil
           | Cons Char LExpr
           | Head LExpr
           | Tail LExpr
  deriving Show

data BExpr = Tru
           | Eq LExpr LExpr
           | Not BExpr
           | And BExpr BExpr
           | Or BExpr BExpr
  deriving Show

type Env = [(VarName, String)]

evalL :: Env -> LExpr -> Maybe String
evalL env (Var v)    = lookup v env
evalL _   Nil        = Just []
evalL env (Cons x e) = (x :) <$> evalL env e
evalL env (Head e)   = return . head <$> evalL env e
evalL env (Tail e)   = tail <$> evalL env e

evalB :: Env -> BExpr -> Maybe Bool
evalB _   Tru         = Just True
evalB env (Eq e1 e2)  = (==) <$> evalL env e1 <*> evalL env e2
evalB env (Not e)     = not  <$> evalB env e
evalB env (And e1 e2) = (&&) <$> evalB env e1 <*> evalB env e2
evalB env (Or e1 e2)  = (||) <$> evalB env e1 <*> evalB env e2

run :: Env -> Cmd -> Maybe Env
run env Skip          = Just env
run env (Assign v a)  = evalL env a >>= \i -> Just ((v, i) : env)
run env (Seq c1 c2)   = run env c1 >>= \env' -> run env' c2
run env (Ite e c1 c2) = evalB env e >>= \b -> run env (if b then c1 else c2)
run env (While e c)   = evalB env e >>= \b -> run env (if b then Seq c (While e c) else Skip)

--

-- Matching test program
-- Expects inputs in variables Xs and Ys, output is Xs with Xs == [] if Xs was part of Ys

{-
xs = "allo" # zu suchendes wort
ys = "aloallo" # zu durchsuchendes wort

while len(ys) != 0:
    as1 = xs[:]
    bs = ys[:]
    while len(as1) != 0 and len(bs) != 0:
        if as1[:1] == bs[:1]:
            as1 = as1[1:]
            bs = bs[1:]
        else:
            bs = []
    if len(as1) == 0:
        ys = []
        xs = []
    else:
        ys = ys[1:]
print(len(xs) == 0)
-}

example :: Cmd
example =
  While (Not (Eq (Var "Ys") Nil)) (foldl1 Seq
    [ Assign "As" (Var "Xs")
    , Assign "Bs" (Var "Ys")
    , While (And (Not (Eq (Var "As") Nil)) (Not (Eq (Var "Bs") Nil)))
        (Ite (Eq (Head (Var "As")) (Head (Var "Bs")))
          (foldl1 Seq [ Assign "As" (Tail (Var "As"))
                      , Assign "Bs" (Tail (Var "Bs"))
                      ])
          (Assign "Bs" Nil))
    , Ite (Eq (Var "As") Nil)
        (foldl1 Seq [ Assign "Ys" Nil
                    , Assign "Xs" Nil
                    ])
        (Assign "Ys" (Tail (Var "Ys")))
    ])

test :: String -> String -> Bool
test xs ys = maybe undefined id (run [("Xs", xs), ("Ys", ys)] example >>= fmap null . lookup "Xs")

-- Test with: head $ $(inv 'test) (Just 3628800)

--

-- Equivalent test program in Haskell

ref :: Eq a => [a] -> [a] -> Bool
ref [] _      = True
ref _  []     = False
ref xs (y:ys) = ref' xs (y:ys) || ref xs ys
  where ref' []      _     = True
        ref' (x:xs) (y:ys) = x == y && ref' xs ys
        ref' _      _      = False


-- $(inv 'refP True) (Just (P.S (P.S (P.S (P.S (P.S (P.S Z)))))))

-- Test with: head $ $(inv 'ref True) (Just 3628800)
