{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Plugin.Trans.PatternMatching
Description : Lift pattern expressions
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module provides a function to lift a pattern and extract any potential
variables that might need to be shared.
-}
module Plugin.Trans.Pat (liftPattern) where

import GHC.Hs.Pat
import GHC.Hs.Types
import GHC.Hs.Lit
import GHC.Hs.Extension
import GHC.Hs.Expr
import GhcPlugins hiding (getSrcSpanM)
import TcRnTypes
import ConLike
import TcEvidence
import Bag
import TcRnMonad
import ErrUtils

import Plugin.Trans.Type
import Plugin.Trans.Constr
import Plugin.Trans.Util
import Plugin.Trans.CreateSyntax

-- | Lift the types of each pattern and
-- rename variables for sharing and newtypes.
-- The third return comoponent is only needed for newtypes
-- and is only manipulated for newtype constructors.
liftPattern :: TyConMap -> LPat GhcTc
            -> TcM (LPat GhcTc, [(Var, Var)])
liftPattern = liftPat

-- | To prevent returning the variables of top-level var patterns from
-- being returned as newtype-variables
-- (e.g. variables inside a newtype constructor pattern)
-- and to not lift the type of those variables
-- we remember if we are "under" a newtype or not.
liftPat :: TyConMap -> LPat GhcTc
        -> TcM (LPat GhcTc, [(Var, Var)])
liftPat tcs (L l p) = do
  (r, vs1) <- setSrcSpan l $ liftPat' tcs p
  return (L l r, vs1)

liftPat' :: TyConMap -> Pat GhcTc
         -> TcM (Pat GhcTc, [(Var, Var)])
liftPat' tcs (WildPat ty) =
  -- This can only occur as a top-level pattern.
  -- This means that we should not wrap the type in Nondet.
  (, []) . WildPat <$> liftInnerTyTcM tcs ty
liftPat' tcs (VarPat x (L l v)) = do
  -- Get a new variable based on the given one.
  -- We choose a new ID for the pattern variable, because the pattern variable
  -- will be shared while the "old" id is used
  -- for the binding variable after sharing.
  -- This aviods having to replace all mentions of the old variable in the body.
  u <- getUniqueM
  -- Here we use liftType and not liftInnerType, because this pattern
  -- is guaranteed to not be the top-level pattern after pattern matching.
  -- Thus, the type of this variable really is wrapped in Nondet.
  ty <- liftTypeTcM tcs (varType v)
  let vnew = setVarUnique (setVarType v ty) u
  let vold = setVarType v ty
  return (VarPat x (L l vnew), [(vnew, vold)])
liftPat' tcs (LazyPat x p) = do
  (p', vars1) <- liftPat tcs p
  return (LazyPat x p', vars1)
liftPat' _ p@AsPat {} =
  panicAny "As-pattern should have been desugared before lifting" p
liftPat' tcs (ParPat x p) = do
  (p', vars1) <- liftPat tcs p
  return (ParPat x p', vars1)
liftPat' _ p@BangPat {} = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Bang patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _ p@(ListPat (ListPatTc _ Nothing) _) =
  panicAny "List pattern should have been desugared before lifting" p
liftPat' _ p@(ListPat (ListPatTc _ (Just _)) _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' tcs (TuplePat tys args box) = do
  con <- liftIO (getLiftedCon (tupleDataCon box (length tys)) tcs)
  let lc = noLoc (RealDataCon con)
  (args', vs) <- unzip <$> mapM (liftPat tcs) args
  let det = PrefixCon args'
  mty <- mkTyConTy <$> getMonadTycon
  tys' <- (mty:) <$> mapM (liftInnerTyTcM tcs) tys
  return (ConPatOut lc tys' [] [] (EvBinds emptyBag) det WpHole, concat vs)
liftPat' _ p@SumPat {} = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _ p@ConPatIn {} =
  panicAny "Untyped pattern not expected after TC" p
liftPat' tcs p@ConPatOut{ pat_args = args
                        , pat_arg_tys = tys
                        , pat_con = L l (RealDataCon con) } = do
  let recParent = RecSelData (dataConTyCon con)
  (args', varsS) <- liftConDetail tcs recParent args
  -- The tys are basically type applications for the tyvars of con,
  -- so we have to use liftInnerTy.
  tys' <- mapM (liftInnerTyTcM tcs) tys
  mty <- mkTyConTy <$> getMonadTycon
  con' <- L l . RealDataCon <$> liftIO (getLiftedCon con tcs)
  let p' = p { pat_args = args', pat_arg_tys = mty:tys', pat_con = con' }
  return (p', varsS)
liftPat' _ p@ConPatOut{ } = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Pattern synonyms are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _ p@ViewPat {} = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "View patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _ p@(SplicePat _ _) = do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "Spliced patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' _   (LitPat _ (HsIntPrim _ i)) = do
  neg <- liftQ [| negate :: Int -> Int |]
  negTy <- unLoc <$> mkApp (mkNewAny neg) (intTy `mkVisFunTy` intTy) []
  let negSyn = if i < 0 then Just (SyntaxExpr negTy [WpHole] WpHole) else Nothing
  eq <- liftQ [| (==) :: Int -> Int -> Bool |]
  eqTy <- unLoc <$> mkApp (mkNewAny eq) (mkVisFunTys [intTy, intTy] boolTy) []
  let eqSyn = SyntaxExpr eqTy [WpHole, WpHole] WpHole

  witness <- liftQ [| fromInteger i :: Int |]
  witnessTy <- unLoc <$> mkApp (mkNewAny witness) intTy []
  let integralLit = HsIntegral (IL (SourceText (show (abs i))) False (abs i))
  let overLit = OverLit (OverLitTc False intTy) integralLit witnessTy
  return (NPat intTy (noLoc overLit) negSyn eqSyn, [])
liftPat' _   p@(LitPat _ _)  = return (p, [])
liftPat' _   p@NPat {}       = return (p, [])
liftPat' _   p@NPlusKPat {} =  do
  flags <- getDynFlags
  l <- getSrcSpanM
  reportError (mkErrMsg flags l neverQualify
    "N+k patterns are not supported by the plugin")
  failIfErrsM
  return (p, [])
liftPat' tcs (SigPat _ p _) = liftPat' tcs (unLoc p)
liftPat' tcs (CoPat _ _ p _) = liftPat' tcs p
liftPat' _   p@(XPat _) = return (p, [])

liftConDetail :: TyConMap -> RecSelParent -> HsConPatDetails GhcTc
              -> TcM (HsConPatDetails GhcTc, [(Var, Var)])
liftConDetail tcs _ (PrefixCon args) = do
  (args', vs) <- unzip <$> mapM (liftPat tcs) args
  return (PrefixCon args', concat vs)
liftConDetail tcs p (RecCon (HsRecFields flds d)) = do
  (flds', vs) <- unzip <$> mapM (liftRecFld tcs p) flds
  return (RecCon (HsRecFields flds' d), concat vs)
liftConDetail tcs _ (InfixCon arg1 arg2) = do
  (arg1', vs1) <- liftPat tcs arg1
  (arg2', vs2) <- liftPat tcs arg2
  return (InfixCon arg1' arg2', vs1 ++ vs2)

liftRecFld :: TyConMap -> RecSelParent -> LHsRecField GhcTc (LPat GhcTc)
           -> TcM (LHsRecField GhcTc (LPat GhcTc), [(Var, Var)])
liftRecFld tcs p (L l1 (HsRecField (L l2 idt) pat pn)) = do
  idt' <- liftFieldOcc tcs p idt
  (p', vs) <- liftPat tcs pat
  return (L l1 (HsRecField (L l2 idt') p' pn), vs)

liftFieldOcc :: TyConMap -> RecSelParent -> FieldOcc GhcTc
             -> TcM (FieldOcc GhcTc)
liftFieldOcc tcs p (FieldOcc v _) = do
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  ftc <- getFunTycon
  v' <- liftIO (getLiftedRecSel ftc mty us tcs p v)
  return (FieldOcc v' (noLoc (nameRdrName (varName v'))))
liftFieldOcc _   _ x = return x
