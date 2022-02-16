{-# LANGUAGE TemplateHaskell #-}
{-|
Module      : Plugin.Trans.Record
Description : Module to lift record selectors
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains the function to lift the record selector function
that is introduced for each record label.
-}
module Plugin.Trans.Record (liftRecordSel, mkRecSelFun) where

import Control.Applicative

import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Tuple

import GHC.Hs.Binds
import GHC.Hs.Expr
import GHC.Hs.Extension
import TcRnTypes
import Bag
import GhcPlugins
import TcRnMonad
import TcEvidence
import GHC

import Plugin.Trans.Type
import Plugin.Trans.Pat
import Plugin.Trans.Constr
import Plugin.Trans.Util
import Plugin.Trans.CreateSyntax
import Plugin.Effect.Util
import Plugin.Trans.Var

-- | Lift the given record selector function, if possible.
-- Record selectors stay as a unary function after lifting and thus need
-- a lifting scheme that is different from ordinary functions.
liftRecordSel :: TyConMap -> HsBindLR GhcTc GhcTc
              -> TcM (Maybe (HsBindLR GhcTc GhcTc))
liftRecordSel tcs (AbsBinds _ tvs evs ex evb bs sig)
  | [L l (FunBind x _ mg wrap ticks)] <- bagToList bs,
    [ABE _ p m w s] <- ex = do
      u <- getUniqueM
      ftc <- getFunTycon
      us1 <- getUniqueSupplyM
      us2 <- getUniqueSupplyM

      let parent = case idDetails p of
            RecSelId parTc _ -> parTc
            _ -> panicBndrUnsafe
                   "Expected RecSel in record selector definition" p

      -- Look up how the lifted record selector should look.
      mty <- mkTyConTy <$> getMonadTycon
      p' <- liftIO (getLiftedRecSel ftc mty us1 tcs parent p)
      -- Lift its type.
      m' <- setVarType (setVarUnique (
            setVarName m (setNameUnique (varName m) u)) u)
              <$> liftIO (liftResultTy ftc mty us2 tcs (varType m))
      -- Lift its implementation.
      mg' <- liftRecSelMG tcs m' mg

      -- Create the correct export entries and stuff.
      let selB = listToBag [L l (FunBind x (noLoc m') mg' wrap ticks)]
      let ex' = ABE noExtField p' m' w s
      let b' = AbsBinds noExtField tvs evs [ex'] evb selB sig

      -- Update its type in the environment
      tenv_var <- tcg_type_env_var <$> getGblEnv
      tenv <- readTcRef tenv_var
      writeTcRef tenv_var (extendTypeEnvWithIds tenv [p'])
      return (Just b')
liftRecordSel _ _ = return Nothing

-- | Lift the MatchGroup of a record selector.
liftRecSelMG :: TyConMap -> Var
             -> MatchGroup GhcTc (LHsExpr GhcTc)
             -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
liftRecSelMG tcs f (MG (MatchGroupTc args res) (L _ alts) orig)
  = do
    args' <- mapM (liftInnerTyTcM tcs) args
    -- Lift the result type of this match group accordingly.
    res' <- liftTypeTcM tcs res
    alts' <- mapM (liftRecSelAlt tcs f) alts
    return (MG (MatchGroupTc args' res') (noLoc alts') orig)
liftRecSelMG _ _ x = return x

-- | Lift an alternative of a record selector.
liftRecSelAlt :: TyConMap -> Var -> LMatch GhcTc (LHsExpr GhcTc)
              -> TcM (LMatch GhcTc (LHsExpr GhcTc))
liftRecSelAlt tcs f (L _ (Match _ ctxt [pat] rhs)) = do
  -- Lift any left-side pattern.
  (pat', vs) <- liftPattern tcs pat
  -- Potentially lift any unlifted newtype variables.
  let ctxt' = ctxt { mc_fun = noLoc (varName f) }
  -- Replace any variables on the right side.
  -- Thankfully, a record selector is always just a single variable on the rhs.
  rhs' <- everywhere (mkT (replaceVarExpr (map swap vs)))
            <$> everywhereM (mkM (replaceRecErr tcs)) rhs
  return (noLoc (Match noExtField ctxt' [pat'] rhs'))
liftRecSelAlt _ _ x = return x

replaceRecErr :: TyConMap -> HsExpr GhcTc -> TcM (HsExpr GhcTc)
-- something like (recSelError @... "[SomeError]"#)
replaceRecErr tcs e@(HsApp _ (L _ (HsWrap _ _ (HsVar _ (L _ v)))) (L _ _))
  | v == rEC_SEL_ERROR_ID = do
    f <- liftQ [| Control.Applicative.empty |]
    ty <- getTypeOrPanic (noLoc e) >>= liftTypeTcM tcs
    unLoc <$> mkApp (mkNewAny f) ty []
replaceRecErr _   e = return e

-- | Substitute variables in the given expression.
replaceVarExpr :: [(Var, Var)] -> HsExpr GhcTc -> HsExpr GhcTc
replaceVarExpr vs (HsVar _ (L l v))
  | Just v' <- lookup v vs = HsVar noExtField (L l v')
replaceVarExpr _  e        = e

mkRecSelFun :: TyConMap -> Var -> TcM (LHsBind GhcTc)
mkRecSelFun tcs v = do
  ftc <- getFunTycon
  mtc <- getMonadTycon
  let mty = mkTyConTy mtc
  us <- getUniqueSupplyM

  th <- liftQ [| \sel -> returnFLF $ \record -> record >>= sel |]

  let (pis, ty) = splitForAllTys (varType v)
  let (unliftedArg, unliftedRes) = splitFunTy ty
  Just (oldTc, _) <- return $ splitTyConApp_maybe unliftedArg
  v' <- liftIO (getLiftedRecSel ftc mty us tcs (RecSelData oldTc) v)
  arg <- liftInnerTyTcM tcs unliftedArg
  res <- liftTypeTcM tcs unliftedRes


  let monotype = mkTyConApp mtc [mkTyConApp ftc [mty, arg, bindingType res]]
  let polytype = mkForAllTys (map (`Bndr` Inferred) pis) monotype

  let w = foldr ((<.>) . toWrap) WpHole pis
  let wrappedV = mkHsWrap w (HsVar noExtField (noLoc v'))

  let thtype = (arg `mkVisFunTy` res) `mkVisFunTy` monotype
  e <- mkApp (mkNewAny th) thtype [noLoc wrappedV]

  u1 <- getUniqueM
  u2 <- getUniqueM
  let str = occNameString (occName v)
  let unliftedStr = take (length str - length "$FLsel") str
  let occ = addNameSuffix $ mkOccName (occNameSpace (occName v)) unliftedStr
  mdl <- tcg_mod <$> getGblEnv
  let name = mkExternalName (varUnique v) mdl occ noSrcSpan
  let preparedId = setIdDetails (setVarName v name) VanillaId
  let monoV = mkLocalVar VanillaId (mkClonedInternalName u1 name) monotype vanillaIdInfo
  let polyV = setVarType (setVarName preparedId (setNameUnique name u2)) polytype

  let bdy = GRHS noExtField [] e
  let rhs = GRHSs noExtField [noLoc bdy] (noLoc (EmptyLocalBinds noExtField))
  let ctxt = FunRhs (noLoc (varName monoV)) Prefix NoSrcStrict
  let clause = Match noExtField ctxt [] rhs
  let mg = MG (MatchGroupTc [] monotype) (noLoc [noLoc clause]) Generated
  let fb = FunBind emptyNameSet (noLoc monoV) mg WpHole []
  let export = ABE noExtField polyV monoV WpHole (SpecPrags [])
  let absB = AbsBinds noExtField pis [] [export] [] (unitBag (noLoc fb)) False

  tenv <- getGblEnv >>= readTcRef . tcg_type_env_var
  let tenv' = plusTypeEnv tenv (typeEnvFromEntities [polyV] [] [])
  getGblEnv >>= \gbl -> writeTcRef (tcg_type_env_var gbl) tenv'
  return (noLoc absB)
  where
    toWrap tyvar = WpTyApp (mkTyVarTy tyvar)
