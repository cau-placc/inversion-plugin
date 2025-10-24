{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

-- TODO: Taken from "From Checking to Inference via Driving and Dag Grammars"

module Typechecker where

data Type = Tv Int2 | Ar Type Type
  deriving (Eq, Show)
data Term = Var Int2 | App Term Term | Abs Int2 Term
  deriving Show
type Env = [(Int2, Type)]
data Proof = Infer Premise Type
  deriving Show
data Premise = Axiom | Elim Proof Proof | Intro Proof
  deriving Show

data Int2 = Z | SZ | SZZ | SZZZ
  deriving (Eq, Show)

typechk (Infer x y) z v = expchk z x y v
expchk (Var x) y z v = axiomchk y x z v
expchk (App x y) z v w = elimchk z x y v w
expchk (Abs x y) z v w = introchk z x y v w
axiomchk Axiom x y z = match z x y
axiomchk x y z v = False
elimchk (Elim x y) z v w x1 =
  typechk x z x1 && typechk y v x1 && conclusion x == Ar (conclusion y) w
elimchk x y z v w = False
introchk (Intro x) y z v w = arrowcheck v x y z w
introchk x y z v w = False
match ((x,y):z) v w = ite (v == x) (w == y) (match z v w)
match x y z = False
arrowcheck (Ar x y) z v w x1 = typechk z w ((v,x):x1) && y == conclusion z
arrowcheck x y z v w = False
conclusion (Infer x y) = y
ite False x y = y
ite True x y = x


--s = Abs 0 (Abs 1 (Abs 2 (App (App (Var 0) (Var 2)) (App (Var 1) (Var 2)))))
--s = Abs Z (Abs (S Z) (Abs (S (S Z)) (App (App (Var Z) (Var (S (S Z)))) (App (Var (S Z)) (Var (S (S Z)))))))
--t = (Ar (Ar (Tv 0) (Ar (Tv 1) (Tv 2))) (Ar (Ar (Tv 0) (Tv 1)) (Ar (Tv 0) (Tv 2))))
--s2 = Abs 0 (Var 0)
--s3 = Abs 0 (Abs 1 (App (Var 0) (Var 1)))

--main typ prf = typechk (Infer prf typ) s []
