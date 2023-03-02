{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Plugin.Trans.PatternMatching
-- Description : Lift pattern expressions
-- Copyright   : (c) Kai-Oliver Prott (2020)
-- Maintainer  : kai.prott@hotmail.de
--
-- This module provides a function to lift a pattern and extract any potential
-- variables that might need to be shared.
module Plugin.Trans.Pat (liftPattern) where

import GHC.Core.ConLike
import GHC.Core.TyCo.Rep
import GHC.Data.Bag
import GHC.Hs.Expr
import GHC.Hs.Extension
import GHC.Hs.Lit
import GHC.Hs.Pat
import GHC.Hs.Type
import GHC.Parser.Annotation
import GHC.Plugins hiding (extendTvSubst, getSrcSpanM, substTy)
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Types.SourceText
import GHC.Utils.Error
import Plugin.Trans.Constr
import Plugin.Trans.CreateSyntax
import Plugin.Trans.Type
import Plugin.Trans.Util

-- | Lift the types of each pattern and
-- rename variables for sharing and newtypes.
liftPattern ::
  TyConMap ->
  LPat GhcTc ->
  TcM (LPat GhcTc)
liftPattern = liftPat

liftPat ::
  TyConMap ->
  LPat GhcTc ->
  TcM (LPat GhcTc)
liftPat tcs (L l p) = do
  r <- setSrcSpanA l $ liftPat' tcs p
  return (L l r)

liftPat' ::
  TyConMap ->
  Pat GhcTc ->
  TcM (Pat GhcTc)
liftPat' tcs (WildPat ty) = do
  -- This can only occur as a top-level pattern.
  -- This means that we should not wrap the type in Nondet.
  WildPat <$> liftInnerTyTcM tcs ty
liftPat' tcs (VarPat x (L l v)) = do
  -- Here we use liftType and not liftInnerType, because this pattern
  -- is guaranteed to not be the top-level pattern after pattern matching.
  -- Thus, the type of this variable really is wrapped in Nondet.
  ty <- liftTypeTcM tcs (varType v)
  let vnew = setVarType v ty
  return (VarPat x (L l vnew))
liftPat' tcs (LazyPat x p) = do
  p' <- liftPat tcs p
  return (LazyPat x p')
liftPat' _ p@AsPat {} =
  panicAny "As-pattern should have been desugared before lifting" p
liftPat' tcs (ParPat x p) = do
  p' <- liftPat tcs p
  return (ParPat x p')
-- ignore any leftover bangs, their strictness is ensured during
-- the pattern match compilation
liftPat' tcs (BangPat _ p) = do
  p' <- liftPat tcs p
  return (unLoc p')
liftPat' _ p@(ListPat (ListPatTc _ Nothing) _) =
  panicAny "List pattern should have been desugared before lifting" p
liftPat' _ p@(ListPat (ListPatTc _ (Just _)) _) = do
  l <- getSrcSpanM
  reportError
    ( mkMsgEnvelope
        l
        neverQualify
        "Overloaded lists are not supported by the plugin"
    )
  failIfErrsM
  return p
liftPat' tcs (TuplePat tys args box) = do
  con <- liftIO (getLiftedCon (tupleDataCon box (length tys)) tcs)
  let lc = noLocA (RealDataCon con)
  args' <- mapM (liftPat tcs) args
  mty <- mkTyConTy <$> getMonadTycon
  tys' <- (mty:) <$> mapM (liftInnerTyTcM tcs) tys
  let det = PrefixCon [] args'
  let res = ConPat (ConPatTc tys' [] [] (EvBinds emptyBag) WpHole) lc det
  return res
liftPat' _ p@SumPat {} = do
  l <- getSrcSpanM
  reportError
    ( mkMsgEnvelope
        l
        neverQualify
        "Unboxed sum types are not supported by the plugin"
    )
  failIfErrsM
  return p
liftPat'
  tcs
  p@ConPat
    { pat_con_ext = x@ConPatTc {cpt_arg_tys = tys},
      pat_args = args,
      pat_con = L l (RealDataCon con)
    } = do
    let recParent = RecSelData (dataConTyCon con)
    args' <- liftConDetail tcs recParent args
    -- The tys are basically type applications for the tyvars of con,
    -- so we have to use liftInnerTy.
    tys' <- mapM (liftInnerTyTcM tcs) tys
    con' <- L l . RealDataCon <$> liftIO (getLiftedCon con tcs)
    mty <- mkTyConTy <$> getMonadTycon
    let x' = x {cpt_arg_tys = mty : tys'}
    let p' = p {pat_args = args', pat_con_ext = x', pat_con = con'}
    return p'
liftPat' _ p@ConPat {} = do
  l <- getSrcSpanM
  reportError
    ( mkMsgEnvelope
        l
        neverQualify
        "Pattern synonyms are not supported by the plugin"
    )
  failIfErrsM
  return p
liftPat' _ p@(ViewPat _ _ _) = do
  l <- getSrcSpanM
  reportError
    ( mkMsgEnvelope
        l
        neverQualify
        "View patterns are not supported by the plugin"
    )
  failIfErrsM
  return p
liftPat' _ p@(SplicePat _ _) = do
  l <- getSrcSpanM
  reportError
    ( mkMsgEnvelope
        l
        neverQualify
        "Spliced patterns are not supported by the plugin"
    )
  failIfErrsM
  return p
liftPat' _ (LitPat _ (HsIntPrim _ i)) = do
  neg <- liftQ [|negate :: Int -> Int|]
  negTy <- unLoc <$> mkApp (mkNewAny neg) (intTy `mkVisFunTyMany` intTy) []
  let negSyn
        | i < 0 = Just (SyntaxExprTc negTy [WpHole] WpHole)
        | otherwise = Nothing
  eq <- liftQ [|(==) :: Int -> Int -> Bool|]
  let eqTy = mkVisFunTys [Scaled Many intTy, Scaled Many intTy] boolTy
  eqTyped <- unLoc <$> mkApp (mkNewAny eq) eqTy []
  let eqSyn = SyntaxExprTc eqTyped [WpHole, WpHole] WpHole
  witness <- liftQ [|fromInteger i :: Int|]
  witnessTy <- unLoc <$> mkApp (mkNewAny witness) intTy []
  let integralLit = HsIntegral (IL (SourceText (show (abs i))) False (abs i))
  let overLit = OverLit (OverLitTc False intTy) integralLit witnessTy
  return (NPat intTy (noLoc overLit) negSyn eqSyn)
liftPat' _ p@(LitPat _ _) = return p
liftPat' _ p@NPat {} = return p
liftPat' _ p@(NPlusKPat _ _ _ _ _ _) = do
  l <- getSrcSpanM
  reportError
    ( mkMsgEnvelope
        l
        neverQualify
        "N+k patterns are not supported by the plugin"
    )
  failIfErrsM
  return p
liftPat' tcs (SigPat _ p _) = liftPat' tcs (unLoc p)
liftPat' tcs (XPat (CoPat _ p _)) = liftPat' tcs p

liftConDetail ::
  TyConMap ->
  RecSelParent ->
  HsConPatDetails GhcTc ->
  TcM (HsConPatDetails GhcTc)
liftConDetail tcs _ (PrefixCon _ args) = do
  args' <- mapM (liftPat tcs) args
  return (PrefixCon [] args')
liftConDetail tcs p (RecCon (HsRecFields flds d)) = do
  flds' <- mapM (liftRecFld tcs p) flds
  return (RecCon (HsRecFields flds' d))
liftConDetail tcs _ (InfixCon arg1 arg2) = do
  arg1' <- liftPat tcs arg1
  arg2' <- liftPat tcs arg2
  return (InfixCon arg1' arg2')

liftRecFld ::
  TyConMap ->
  RecSelParent ->
  LHsRecField GhcTc (LPat GhcTc) ->
  TcM (LHsRecField GhcTc (LPat GhcTc))
liftRecFld tcs p (L l1 (HsRecField x (L l2 idt) pat pn)) = do
  idt' <- liftFieldOcc tcs p idt
  p' <- liftPat tcs pat
  return (L l1 (HsRecField x (L l2 idt') p' pn))

liftFieldOcc ::
  TyConMap ->
  RecSelParent ->
  FieldOcc GhcTc ->
  TcM (FieldOcc GhcTc)
liftFieldOcc tcs p (FieldOcc v _) = do
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  ftc <- getFunTycon
  v' <- liftIO (getLiftedRecSel ftc mty us tcs p v)
  return (FieldOcc v' (noLocA (nameRdrName (varName v'))))
