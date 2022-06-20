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

import Control.Monad
import Data.Maybe
import GHC.Core.Class
import GHC.Core.InstEnv
import GHC.Core.Unify
import GHC.Plugins
import GHC.Tc.Types
import Plugin.Trans.Class
import Plugin.Trans.Type
import Plugin.Trans.Util
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

  stc <- getShareClassTycon
  ftc <- getFunTycon
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  (pis, inner) <-
    splitInvisPiTys
      <$> liftIO (liftInnerTyParametrized False stc ftc mty us tcs (varType origDf))
  -- Get named binders (e.g., foralls).
  -- Extract variables from named binders.
  let bs = mapMaybe namedTyCoVarBinder_maybe pis
  uss <- replicateM (length bs) getUniqueSupplyM

  -- Function to apply the shareable type constructor to its args.
  let mkShareType t' = mkTyConApp stc [mty, t']
      -- Create Shareable constraints for all given variables.
      cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
  -- Incorporate the new constraints.
  let dfType = mkPiTys pis (foldr mkInvisFunTyMany inner cons)
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
