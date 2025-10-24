{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Lisp where

unwords2 :: [String] -> String
unwords2 [] = ""
unwords2 [x] = x
unwords2 (x:xs) = x ++ " " ++ unwords2 xs

{-data P = Z | B | C | D | E | F
  deriving (Eq, Show)

toInt :: P -> Int
toInt Z = 0
toInt B = 1
toInt C = 2
toInt D = 3
toInt E = 4
toInt F = 5-}

data P = Z | S P
  deriving (Eq, Show)

toInt Z = 0
toInt (S n) = 1 + toInt n

data Pair a b = Pair a b --TODO: Use tuples
  deriving (Eq, Show)

snd2 :: Pair a b -> b
snd2 (Pair _ y) = y

lookup2 :: Eq a => a -> [Pair a b] -> Maybe b
lookup2 _ [] = Nothing
lookup2 x (Pair x' y : ps) = if x == x' then Just y else lookup2 x ps
lookup2 x (Pair x' y : ps) | x == x' = Just y
                           | x /= x' = lookup2 x ps

type Env = [Pair P Exp]

data Exp = Lit Literal
         | Var P
         | Lambda P Exp
         | Closure P Exp Env
         | List [Exp]
         | QuoteLit
         | ListLit
  deriving (Eq, Show)

data Literal = I | Love | You
  deriving (Eq, Show)

pretty :: Exp -> String
pretty (Var x) = show (toInt x)
pretty (Lambda x e) = "(lambda (" ++ show (toInt x) ++ ") " ++ pretty e ++ ")"
pretty (Closure x e env) = "(closure " ++ show (toInt x) ++ " " ++ pretty e ++ " " ++ show env ++ ")"
pretty (List es) = "(" ++ unwords2 (map pretty es) ++ ")"
pretty QuoteLit = "quote"
pretty ListLit = "list"
pretty (Lit I) = "I"
pretty (Lit Love) = "love"
pretty (Lit You) = "you"

{-type Peano = P

data Symbol = Lambda | Quote | List
  deriving (Eq, Show)

data Lisp = Var Peano
          | Symbol Symbol
          | List [Lisp]
          | Closure Peano Exp Env-}

-- Test: eval (List [Lambda Z (Lambda (S Z) (Var Z)), Lambda (S (S Z)) (Var (S (S Z)))])
-- Test: eval (List [Lambda Z (List [Var Z, Lambda (S Z) (Var Z)]), Lambda (S (S Z)) (Var (S (S Z)))])
-- Expected result: Closure (S Z) (Var Z) [Pair Z (Closure (S (S Z)) (Var (S (S Z))) [])]
-- Test: map (fmap pretty) $ take 5 $ $(inv 'eval True) $ Closure (S Z) (Var Z) [Pair Z (Closure (S (S Z)) (Var (S (S Z))) [])]
-- Test: map (fmap showFree) $ take 5 $ $(inv 'eval False) $ Closure (S Z) (Var Z) [Pair Z (Closure (S (S Z)) (Var (S (S Z))) [])]
-- Test: take 1 $ $(inOutClassInv 'eval True [[| var 0 |]] [| var 0 |])
-- Test: take 1 $ $(inOutClassInv 'eval True [[| List [Lambda (var 0) (var 1), var 2] |]] [| List [Lambda (var 0) (var 1), var 2] |])
-- Test: take 1 $ $(inOutClassInv 'eval True [[| List [Lambda Z (var 1), List [QuoteLit, Lambda Z (var 2)]] |]] [| List [Lambda Z (var 1), List [QuoteLit, Lambda Z (var 2)]] |])
eval :: Exp -> Exp
eval = eval' []
  where
    eval' :: Env -> Exp -> Exp
    eval' env (Var x) = case lookup2 x env of
      Just e -> e
    eval' env (Lambda x e) = (Closure x e env)
    eval' env (List [QuoteLit,e]) | noClosures e = e
    eval' env (List (ListLit:es)) | all noClosures es = List (map (eval' env) es)
    eval' env (List [e1,e2]) = case eval' env e1 of
      Closure x e3 env' -> eval' (Pair x (eval' env e2) : env') e3

noClosures :: Exp -> Bool
noClosures (Var x) = True
noClosures (Lambda _ e) = noClosures e
noClosures (Closure _ _ _) = False
noClosures (List es) = all noClosures es
noClosures QuoteLit = True
noClosures ListLit = True
noClosures (Lit _) = True

iLoveYou1 :: Exp
iLoveYou1 = List [Lit I, Lit Love, Lit You]

iLoveYou2 :: Exp
iLoveYou2 = List [List [QuoteLit, Lit I], List [QuoteLit, Lit Love], List [QuoteLit, Lit You]]

-- take 1 $ $(inv 'eval True) (List [Lit I,Lit Love,Lit You])

-- Test: eval quine
--quine :: Exp
--quine = List [Lambda Z (List [ListLit, Var Z, List [ListLit, List [QuoteLit, QuoteLit], Var Z]]), List [QuoteLit, Lambda Z (List [ListLit, Var Z, List [ListLit, List [QuoteLit, QuoteLit], Var Z]])]]

-- Test: take 1 $ $(inv 'isQuine True) True
isQuine :: Exp -> Bool
isQuine e = eval e == e

-- Test: take 1 $ $(inv 'isQuine2 True) True
isQuine2 :: Exp -> Bool
isQuine2 e@(List [x, List [QuoteLit, Lambda Z (List [ListLit, Var Z, List [ListLit, List [QuoteLit, QuoteLit], Var Z]])]]) = eval e == e
{-
testExp2 :: (Exp -> Bool) -> Exp2 -> Bool
testExp2 p e = p e && testExp' e
  where
    testExp' :: Exp2 -> Bool
    testExp' (Var2 _) = True
    testExp' (Lambda2 _ e) = testExp2 p e
    testExp' (App2 e1 e2) = testExp2 p e1 && testExp2 p e2
    testExp' (Closure2 _ e env) = testExp2 p e && all (testExp2 p . snd2) env
    testExp' (Quote2 e) = testExp2 p e
    testExp' (List2 es) = all (testExp2 p) es

noClosure2 :: Exp2 -> Bool
noClosure2 (Closure2 _ _ _) = True
noClosure2 _ = False

-- Test: eval2 (App2 (Lambda2 Z (Lambda2 (S Z) (Var2 Z))) (Lambda2 (S (S Z)) (Var2 (S (S Z)))))
-- Test: eval2 (App2 (Lambda2 Z (App2 (Var2 Z) (Lambda2 (S Z) (Var2 Z)))) (Lambda2 (S (S Z)) (Var2 (S (S Z)))))
-- Closure2 (S Z) (Var2 Z) [Pair Z (Closure2 (S (S Z)) (Var2 (S (S Z))) [])]
-- map (fmap pretty2) $ take 5 $ $(inv 'eval2 True) $ Closure2 (S Z) (Var2 Z) [Pair Z (Closure2 (S (S Z)) (Var2 (S (S Z))) [])]
-- Test: take 1 $ $(inOutClassInv 'eval2 True [[| var 0 |]] [| var 0 |])

eval2 :: Exp2 -> Exp2
eval2 = eval' []
  where
    eval' :: Env2 -> Exp2 -> Exp2
    eval' env (Var2 x) = case lookup2 x env of
      Just e -> e
    eval' env (Lambda2 x e) = (Closure2 x e env)
    eval' env (App2 e1 e2) = case eval' env e1 of
      Closure2 x e3 env' -> eval' (Pair x (eval' env e2) : env') e3
    eval' env (Quote2 e) | testExp2 noClosure2 e = e
    eval' env (List2 es) | all (testExp2 noClosure2) es = List2 (map (eval' env) es)

-- Test: take 1 $ $(inv 'isQuine2 True) True
isQuine2 :: Exp2 -> Bool
isQuine2 e = eval2 e == e

isApp2 :: Exp2 -> Bool
isApp2 (App2 (Lambda2 _ _) _) = True
isApp2 _ = False

-- Test: take 1 $ $(inv 'isQuine2' True) True
isQuine2' :: Exp2 -> Bool
isQuine2' e | isApp2 e = eval2 e == e

--List [Lambda Z (List [ListLit, Var Z, List [ListLit, List [QuoteLit, QuoteLit], Var Z]]), List [QuoteLit, Lambda Z (List [ListLit, Var Z, List [ListLit, List [QuoteLit, QuoteLit], Var Z]])]]
quine2 :: Exp2
quine2 = App2 (Lambda2 Z (List2 [Var2 Z, List2 [List [QuoteLit, QuoteLit], Var Z]])) (List [QuoteLit, Lambda Z (List [ListLit, Var Z, List [ListLit, List [QuoteLit, QuoteLit], Var Z]])])















-- Test: eval (List [Lambda Z (Lambda (S Z) (Var Z)), Lambda (S (S Z)) (Var (S (S Z)))])
-- Test: eval (List [Lambda Z (List [Var Z, Lambda (S Z) (Var Z)]), Lambda (S (S Z)) (Var (S (S Z)))])
-- Closure (S Z) (Var Z) [Pair Z (Closure (S (S Z)) (Var (S (S Z))) [])]

eval :: Exp -> Exp
eval = eval' []
  where
    eval' :: Env -> Exp -> Exp
    eval' env (Var x) = case lookup2 x env of
      Just e -> e
    eval' env (Lambda x e) = (Closure x e env)
    eval' env (List [e1, e2]) = case eval' env e1 of --TODO: same env
      Closure x e3 env' -> eval' (Pair x (eval' env e2) : env') e3
      --(QuoteLit, env') -> (e2,
    --eval' env (List (e1:es)) = case eval' env e1 of
    --  (ListLit, env') -> (List (map eval' env ), env')
      --(e1', env') -> case eval' env' e2 of
      --  (e2', env'') -> (List [e1', e2'], env'')
    {-eval' env (List [e1, e2]) = case eval' env e1 of --TODO: same env
      (Lambda x e3, env') -> case eval' env' e2 of
        (e2', env'') -> eval' ((x, e2') : env'') e3
      (e1', env') -> case eval' env' e2 of
        (e2', env'') -> (List [e1', e2'], env'')-}
    --eval' env (List es) = foldr (\e (List es', env') -> case eval' env' e of
    --  (e', env'') -> (List (e' : es'), env'')) (List [], env) es

{-eval2 :: Exp -> (Exp, Env)
eval2 = eval' []
  where
    eval' :: Env -> Exp -> (Exp, Env)
    eval' env (Var x) = case lookup x env of
      Just e -> (e, env)
      --Nothing -> Var x
    eval' env (List [e1, e2]) = case eval' env e1 of --TODO: same env
      (Lambda x e3, env') -> case eval' env e2 of
        (e2', _) -> eval' ((x, e2') : env') e3
      (QuoteLit, env') -> (e2, env')
    eval' env (List (e1:es)) = case eval' env e1 of
      (ListLit, env') -> (List (map eval' env ), env')
      --(e1', env') -> case eval' env' e2 of
      --  (e2', env'') -> (List [e1', e2'], env'')
    {-eval' env (List [e1, e2]) = case eval' env e1 of --TODO: same env
      (Lambda x e3, env') -> case eval' env' e2 of
        (e2', env'') -> eval' ((x, e2') : env'') e3
      (e1', env') -> case eval' env' e2 of
        (e2', env'') -> (List [e1', e2'], env'')-}
    --eval' env (List es) = foldr (\e (List es', env') -> case eval' env' e of
    --  (e', env'') -> (List (e' : es'), env'')) (List [], env) es
    eval' env (Lambda x e) = (Lambda x e, env)-}


{-eval3 :: Exp -> Exp
eval3 = fst . eval' []
  where
    eval' :: Env -> Exp -> (Exp, Env)
    eval' env (Var x) = case lookup x env of
      Just e -> (e, env)
    eval' env (List [e1, e2]) = case eval' env e1 of
      (Lambda x e3, env') -> eval' ((x, fst (eval' env e2)) : env') e3
      (QuoteLit, _) -> (e2, env)
    eval' env (List (e1:es)) = case eval' env e1 of
      (ListLit, _) -> (List (map (fst . eval' env) es), env)
    eval' env (Lambda x e) = (Lambda x e, env)

eval2 :: Exp -> Exp
eval2 = eval' []
  where
    eval' :: Env -> Exp -> Exp
    eval' env (Var x) = case lookup x env of
      Just e -> e
    eval' env (List [e1, e2]) = case eval' env e1 of
      Lambda x e3 -> eval' ((x, eval' env e2) : env) e3
      QuoteLit -> e2
    eval' env (List (e1:es)) = case eval' env e1 of
      ListLit -> List (map (eval' env) es)
    eval' env (Lambda x e) = Lambda x e-}

{-eval :: Exp -> Exp
--eval (Var x) = Var x
eval (List [e1, e2]) = case eval e1 of
  Lambda x e3 -> eval (subst x (eval e2) e3)
  QuoteLit -> e2
  ListLit -> List [eval e2]
  e1' -> List [e1', eval e2] --TODO: Pattern guards
eval (List (ListLit:xs)) = List (map eval xs)
--eval (List es) = List (map eval es)
eval (Lambda x e) = Lambda x e
--eval ListLit = ListLit
--eval QuoteLit = QuoteLit-}

subst :: P -> Exp -> Exp -> Exp
subst x e (Var y) = if x == y then e else Var y
subst x e (List es) = List (map (subst x e) es)
subst x e (Lambda y e') = if x == y then Lambda y e' else Lambda y (subst x e e')
--subst _ _ ListLit = ListLit
--subst _ _ QuoteLit = QuoteLit


--((lambda (x) (list x (list (quote quote) x))) (quote (lambda (x) (list x (list (quote quote) x)))))
--test = List [Lambda Z (List [ListLit, Var Z, List [ListLit, List [QuoteLit, QuoteLit], Var Z]]), List [QuoteLit, Lambda Z (List [ListLit, Var Z, List [ListLit, List [QuoteLit, QuoteLit], Var Z]])]]

--(((lambda (x) (lambda (y) x)) (lambda (z) z)) (lambda (a) a))
test2 = List [List [Lambda (S (S Z)) (Lambda (S (S (S Z))) (Var (S (S Z)))), Lambda (S Z) (Var (S Z))], Lambda Z (Var Z)]

isApp :: Exp -> Bool
isApp (List [Lambda _ _,_]) = True
isApp _ = False

isQuine :: Exp -> Bool
--isQuine e | isApp e = eval2 e == e
--isQuine e {- | isApp e-} = eval2 e == e

isQuine e | isApp e = eval e == e

--Test: (lambda (y) x)     [x -> lambda (z) z] )
-- (Lambda (S Z) (Var Z), [(Z, Lambda (S (S Z)) (Var (S (S Z))))])

--((lambda (x) (x (lambda (y) x))) (lambda (z) z))
--((lambda (x) (x (lambda (y) x))))
-}
