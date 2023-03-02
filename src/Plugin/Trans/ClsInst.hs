-- |
-- Module      : Plugin.Trans.ClsInst
-- Description : Functions to handle lifting of instance information
-- Copyright   : (c) Kai-Oliver Prott (2020)
-- Maintainer  : kai.prott@hotmail.de
--
-- This module contains a function to lift the information that GHC has
-- collected about a given instance.
-- The instance functions itself are not lifted here.
module Plugin.Trans.ClsInst (liftInstance) where

import GHC.Core.Class
import GHC.Core.InstEnv
import GHC.Core.Unify
import GHC.Plugins
import GHC.Tc.Types
import Plugin.Trans.Class
import Plugin.Trans.Type
import Plugin.Trans.Var

-- | Lift a given class instance.
liftInstance :: TyConMap -> ClsInst -> TcM ClsInst
liftInstance tcs (ClsInst _ _ _ tvs origCls origTys origDf ov orp) = do
  -- Lookup new class
  cls <- liftIO $ getLiftedClass origCls tcs

  -- Update type constructors
  tys <- mapM (liftInnerTyTcM tcs) origTys
  let tyc = map (fmap fst . splitTyConApp_maybe) tys
  let tyn = map mkRoughMatchTc tyc

  -- Include any shareable constraints that are required by the type variables
  -- bound in the instance head.

  -- Split the lifted type into invisible pi-types (forall, constraints) #
  -- and the rest.

  ftc <- getFunTycon
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  (pis, inner) <-
    splitInvisPiTys
      <$> liftIO (liftInnerTy ftc mty us tcs (varType origDf))

  -- Incorporate the new constraints.
  let dfType = mkPiTys pis inner
  let dfLifted = setVarType origDf dfType

  -- Set other properties of the new dictionary function.
  let info' = setUnfoldingInfo (idInfo dfLifted) NoUnfolding
  u <- getUniqueM
  let df = liftVarName (lazySetIdInfo dfLifted info') u

  return (ClsInst (className cls) tyn (varName df) tvs cls tys df ov orp)
  where
    mkRoughMatchTc (Just tc)
      | isGenerativeTyCon tc Nominal = KnownTc (tyConName tc)
    mkRoughMatchTc _ = OtherTc
