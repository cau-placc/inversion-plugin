{-|
Module      : Plugin.Trans.ClsInst
Description : Functions to handle lifting of instance information
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a function to lift the information that GHC has
collected about a given instance.
The instance functions itself are not lifted here.
-}
module Plugin.Trans.ClsInst (liftInstance) where

import GhcPlugins
import Class
import InstEnv
import TcRnTypes

import Plugin.Trans.Type
import Plugin.Trans.Class
import Plugin.Trans.Var
import Plugin.Trans.Util

-- | Lift a given class instance.
liftInstance :: TyConMap -> ClsInst -> TcM ClsInst
liftInstance tcs (ClsInst _ _ _ tvs origCls origTys origDf ov orp) = do
  -- Lookup new class
  cls <- liftIO $ getLiftedClass origCls tcs

  -- Update type constructors
  tys <- mapM (liftInnerTyTcM tcs) origTys
  let tyn = map (fmap (tyConName . fst) . splitTyConApp_maybe) tys

  dfType <- liftInnerTyTcM tcs (varType origDf)
  printAny "tys" tys
  printAny "dfType" dfType
  printAny "(varType origDf)" (varType origDf)
  let dfLifted = setVarType origDf dfType

  -- Set other properties of the new dictionary function.
  let info' = setUnfoldingInfo (idInfo dfLifted) NoUnfolding
  u <- getUniqueM
  let df = liftVarName (lazySetIdInfo dfLifted info') u

  return (ClsInst (className cls) tyn (varName df) tvs cls tys df ov orp)
