{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Plugin.Primitives
  ( Invertible, Lifted
  , inv, partialInv, weakInv
  , funPat
  ) where

import Control.Monad

import Data.List
import Data.Maybe

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Plugin.Effect.Monad
import Plugin.Effect.TH

{-# ANN module "HLint: ignore Redundant bracket" #-}

inv :: Name -> ExpQ
inv = flip partialInv []

partialInv :: Name -> [Int] -> ExpQ
partialInv name fixedArgs = genericInv name fixedArgs True

genericInv :: Name -> [Int] -> Bool -> ExpQ
genericInv name fixedArgs nf = do
  info <- reify name
  (_, _, ty) <- decomposeForallT <$> case info of
    VarI _ ty' _     -> return ty'
    ClassOpI _ ty' _ -> return ty'
    _                -> fail $ show name ++ " is no function or class method."
  let validFixedArgs = [1 .. arrowArity ty]
      hint = "has to be a subsequence of " ++ show validFixedArgs
  when (any (`notElem` validFixedArgs) fixedArgs) $ fail $
    "Invalid argument index sequence for partial inverse provided (" ++ hint ++ ")."
  vs <- replicateM (length fixedArgs + 1) (newName "p")
  let invE = VarE $ mkNameG_v (fromMaybe "" $ namePackage name) (fromMaybe "" $ nameModule name) $ nameBase $ mkInverseName (nameBase name) (sort $ nub $ map pred fixedArgs) nf
  return $ LamE (map VarP vs) (applyExp invE (map VarE vs))

weakInv :: Name -> ExpQ
weakInv name = [| foldr const (error "no weak inverse") . $(inv name) |]

funPatPartialInv :: Name -> [Int] -> ExpQ
funPatPartialInv name fixedArgs = genericInv name fixedArgs False

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
    partialInvE <- funPatPartialInv name conIndices
    vE <- [| (\a -> [b | b@($(return (anonymizePat tP))) <- $(return $ applyExp partialInvE conEs) a]) |]
    ViewP vE <$> [p| $(return tP):_ |]

patToExp :: Pat -> Exp
patToExp (LitP l)       = LitE l
patToExp (TupP ps)      = TupE $ map (Just . patToExp) ps
patToExp (ConP name ps) = applyExp (ConE name) $ map patToExp ps
patToExp (ParensP p)    = ParensE $ patToExp p
patToExp (ListP ps)     = ListE $ map patToExp ps
patToExp _              = error "Should not happen: non-constructor pattern in patToExp"

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
