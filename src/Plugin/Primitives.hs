{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}

module Plugin.Primitives
  ( Invertible, Lifted
  , inv, partialInv, weakInv, inClassInv, inOutClassInv, var, showFree
  , funPat
  ) where

import Data.List

import Language.Haskell.TH

import Plugin.Effect.Monad
import Plugin.Effect.TH
import Plugin.Lifted

{-# ANN module "HLint: ignore Redundant bracket" #-}

inv :: Name -> Bool -> ExpQ
inv f = flip (partialInv f) []

weakInv :: Name -> Bool -> ExpQ
weakInv name gnf = [| foldr const (error "no weak inverse") . $(inv name gnf) |]

funPat :: FunPat p => Name -> p
funPat f = funPat' f []

class FunPat p where
   funPat' :: Name -> [PatQ] -> p

instance FunPat PatQ where
  funPat' name qps = do
    ps <- zip [1 ..] <$> sequence qps
    let (cons, others) = partition (isConPat . snd) ps
        (conIndices, consPs) = unzip cons
        conEs = map patToExp consPs
        tP = mkTupleP (map snd others)
    partialInvE <- partialInv name False conIndices
    vE <- [| (\a -> [b | b@($(return (anonymizePat tP))) <- $(return $ applyExp partialInvE conEs) a]) |]
    ViewP vE <$> [p| $(return tP):_ |]

patToExp :: Pat -> Exp
patToExp (LitP l)       = LitE l
patToExp (TupP ps)      = TupE $ map (Just . patToExp) ps
patToExp (ConP name ps) = applyExp (ConE name) $ map patToExp ps
patToExp (ParensP p)    = ParensE $ patToExp p
patToExp (ListP ps)     = ListE $ map patToExp ps
patToExp _              = error "Should not happen: non-constructor pattern in patToExp"

-- last (funPat '(++) [p| x |] [p| [x] |]) = x
-- test ( x <- $(inClassInv '(++) [var x, var x]) = x <- nee is nicht!
-- test ((\list -> [res| res@(_, [x]) <- appendInv list ]) -> (_, [x]):_ ) = x
-- test ((\list -> [res| res@(_, [x]) <- fmap (\(x, free2) -> (_, [x])) (appendInInv [var 1] list)]) -> (_, [x]):_ ) = x

-- test $(funPat 'append [p| _ |] [p| _ |]) = x
-- test ((\list -> [res| res@(_, [x]) <- appendInClassInv [[| _ |], [| [x] |]] list) -> (_, [x]):_ ) = x

-- last (funPat '(++) [p| [_, x] |] [p| [P, x] |]) = x
-- (_, var 1) (x, var 2) (P, var 3) (x, var 4)
-- (_, P) $(inClassInv '(++) [[| var 1, var 2 |], [| [var 3, var 4] |])

--TODO: State für VarP-Dinger
--TODO: reanme to varConPatToExp, dabei VarP zu var ...-Exps mit passender id
-- patToExp2 :: Pat -> Exp
-- patToExp2 (LitP l)       = LitE l
-- patToExp2 (TupP ps)      = TupE $ map (Just . patToExp) ps
-- patToExp2 (ConP name ps) = applyExp (ConE name) $ map patToExp ps
-- patToExp2 (ParensP p)    = ParensE $ patToExp p
-- patToExp2 (ListP ps)     = ListE $ map patToExp ps
-- patToExp2 _              = error "Should not happen: non-constructor pattern in patToExp"


-- --TODO: should be the same as supported by convertExp
-- isVarConPat :: Pat -> Bool
-- isVarConPat (VarP _)    = True
-- isVarConPat WildP       = True
-- isVarConPat (LitP _)    = True
-- isVarConPat (TupP ps)   = all isConPat ps
-- isVarConPat (ConP _ ps) = all isConPat ps
-- isVarConPat (ParensP p) = isConPat p
-- isVarConPat (ListP ps)  = all isConPat ps
-- isVarConPat _           = False
-- --TODO: infixp supporten

isConPat :: Pat -> Bool
isConPat (LitP _)    = True
isConPat (TupP ps)   = all isConPat ps
isConPat (ConP _ ps) = all isConPat ps
isConPat (ParensP p) = isConPat p
isConPat (ListP ps)  = all isConPat ps
isConPat _           = False

anonymizePat :: Pat -> Pat
anonymizePat (LitP l)              = LitP l
anonymizePat (VarP _)              = WildP
anonymizePat (TupP ps)             = TupP $ map anonymizePat ps
anonymizePat (UnboxedTupP ps)      = UnboxedTupP $ map anonymizePat ps
anonymizePat (UnboxedSumP p a1 a2) = UnboxedSumP (anonymizePat p) a1 a2
anonymizePat (ConP n ps)           = ConP n $ map anonymizePat ps
anonymizePat (InfixP p1 n p2)      = InfixP (anonymizePat p1) n (anonymizePat p2)
anonymizePat (UInfixP p1 n p2)     = UInfixP (anonymizePat p1) n (anonymizePat p2)
anonymizePat (ParensP p)           = ParensP $ anonymizePat p
anonymizePat (TildeP p)            = TildeP $ anonymizePat p
anonymizePat (BangP p)             = BangP $ anonymizePat p
anonymizePat (AsP _ p)             = anonymizePat p
anonymizePat WildP                 = WildP
anonymizePat (RecP n fps)          = RecP n $ map (fmap anonymizePat) fps
anonymizePat (ListP ps)            = ListP $ map anonymizePat ps
anonymizePat (SigP p ty)           = SigP (anonymizePat p) ty
anonymizePat (ViewP e p)           = ViewP e (anonymizePat p)

instance FunPat p => FunPat (PatQ -> p) where
   funPat' name ps = \p -> funPat' name (ps ++ [p])
