{-# LANGUAGE TupleSections #-}
{-|
Module      : Plugin.Trans.DictInstFun
Description : Lift the dictionary binding of a type class.
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a function to lift the dictionary binding of a type
class. It is not lifted like a normal function.
-}
module Plugin.Trans.DictInstFun (liftDictInstFun) where

import Data.List

import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Expr
import InstEnv
import ConLike
import TcRnTypes
import TyCoRep
import TcEvidence
import TcRnMonad
import GhcPlugins
import Bag

import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Constr

-- | Lift the dictionary binding of a type class.
-- It is not lifted like a normal function.
liftDictInstFun :: HsBindLR GhcTc GhcTc -> TyConMap
                -> [(ClsInst, ClsInst)] -> TcM (Maybe (HsBindLR GhcTc GhcTc))
liftDictInstFun bind tcs clsInsts = do
  -- Find the correct binding we have to lift from the potential AbsBinds.
  let exported = if isAbsBinds bind then map abe_poly (abs_exports bind) else []
  -- Find the corresponding lifted instance information.
  Just (new, _) <- return $ find (\(_,oldInst) -> is_dfun oldInst `elem` exported ) clsInsts
  -- Perform the actual lifting.
  liftDictInstBinding tcs new bind

-- | Lift the dictionary binding of a type class
-- by using its lifted instance info.
-- It is not lifted like a normal function.
liftDictInstBinding :: TyConMap -> ClsInst -> HsBindLR GhcTc GhcTc
                    -> TcM (Maybe (HsBindLR GhcTc GhcTc))
liftDictInstBinding tcs cls (AbsBinds _ tvs evs ex evb bs sig)
  | [L _ (VarBind _ _ e inl)] <- bagToList bs,
    [ABE _ _ m w s] <- ex = do
      -- The new poly var is the one from the given clsInst.
      let p' = is_dfun cls
      -- The monomorphic one has to be updated for the new type constructors.
      m' <- setVarType m <$> liftInnerTyTcM tcs (varType m)

      -- Each function and superclass selector uses the same wrapper,
      -- that applies all tvs and then all evs.
      -- So we create it once, and use it everywhere.
      let replaceEv ev = setVarType ev <$> liftInnerTyTcM tcs (varType ev)
      allevsids <- mapM replaceEv evs
      let evWraps = map (WpEvApp . EvExpr . evId) allevsids
      let tyWraps = map (WpTyApp . mkTyVarTy) tvs
      let wrap = foldl (<.>) WpHole (reverse evWraps ++ reverse tyWraps)

      -- Lift the actual expression.
      e' <- liftDictExpr cls wrap tcs e

      let vb = listToBag [noLoc (VarBind noExtField m' e' inl)]
      let ex' = [ABE noExtField p' m' w s]
      let b' = AbsBinds noExtField tvs allevsids ex' evb vb sig
      return (Just b')
liftDictInstBinding _ _ _ = return Nothing

-- | Lidt the expression of a dictionary binding.
liftDictExpr :: ClsInst -> HsWrapper -> TyConMap -> LHsExpr GhcTc
             -> TcM (LHsExpr GhcTc)
liftDictExpr cls w tcs (L l ex) = L l <$> liftDictExpr' ex
  where
    -- Applications are translated by lifting both sides.
    liftDictExpr' (HsApp _ e1 e2) =
      HsApp noExtField <$> liftDictExpr cls w tcs e1
                       <*> liftDictExpr cls w tcs e2
    -- The dictionary constructor is lifted by getting the lifted constructor
    -- and lifting its wrapper.
    liftDictExpr' (HsWrap _ cw (HsConLikeOut _ (RealDataCon dc))) = do
      cw' <- liftWrapperTcM tcs cw
      dc' <- liftIO (getLiftedCon dc tcs)
      return (HsWrap noExtField cw' (HsConLikeOut noExtField (RealDataCon dc')))
    liftDictExpr' (HsConLikeOut _ (RealDataCon dc)) = do
      dc' <- liftIO (getLiftedCon dc tcs)
      return (HsConLikeOut noExtField (RealDataCon dc'))
    liftDictExpr' (HsVar _ (L _ v)) = liftInstFunUse v
    -- Other wrappers are discarded and re-create at liftInstFunUse.
    liftDictExpr' (HsWrap _ _ e) = liftDictExpr' e
    liftDictExpr' e = panicAny "Unexpected expression in dictionary function" e

    liftInstFunUse :: Var -> TcM (HsExpr GhcTc)
    liftInstFunUse v = do
      mtc <- getMonadTycon

      -- v has type forall instVars . instConstraints => clsFuncTy,
      -- where clsFuncTy might start with a forall itself.
      -- Instead of putting all Shareable constraints after all foralls,
      -- we want to place them behind instConstraints.
      -- So we split off as many foralls as there are instVars and
      -- then split off as many invisible function args as possible.
      -- But we only do all of this, if the type is not already lifted
      let ty = varType v
      dfLifted <- case splitTyConApp_maybe (snd (splitPiTysInvisible ty)) of
        Just (tc, _) | tc == mtc
          -> setVarType v <$> liftInnerTyTcM tcs ty
        _ -> do
          let (bs1, ty1) = splitPiTysInvisibleN (length (is_tvs cls)) ty
              (bs2, ty2) = splitInvisFunTys ty1
          bs' <- mapM (replacePiTyTcM tcs) (bs1 ++ bs2)
          ty' <- mkPiTys bs' <$> liftTypeTcM tcs ty2
          return (setVarType v ty')

      -- Use the given wrapper expression.
      return (HsWrap noExtField w (HsVar noExtField (noLoc dfLifted)))

-- | Split off all arguments of an invisible function type
-- (e.g., all constraints).
splitInvisFunTys :: Type -> ([TyCoBinder], Type)
splitInvisFunTys (FunTy InvisArg ty1 ty2) =
  let (bs, ty2') = splitInvisFunTys ty2 in (Anon InvisArg ty1 : bs, ty2')
splitInvisFunTys ty = ([], ty)
