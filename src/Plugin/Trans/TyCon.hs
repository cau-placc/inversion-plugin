{-# LANGUAGE RecursiveDo #-}

-- |
-- Module      : Plugin.Trans.TyCon
-- Description : Functions to lift type constructors.
-- Copyright   : (c) Kai-Oliver Prott (2020)
-- Maintainer  : kai.prott@hotmail.de
--
-- This module contains a function to lift a type constructor,
-- regardless of whether or not it stems from a
-- class, data, type or newtype declaration.
module Plugin.Trans.TyCon (liftTycon) where

import Control.Monad
import Data.Maybe
import GHC.Core.Coercion.Axiom
import GHC.Core.FamInstEnv
import GHC.Plugins
import Plugin.Trans.Class
import Plugin.Trans.Constr
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var

-- | Lift a type constructor, if possible.
-- Note that this is part of a fixed-point computation, where the
-- 'UniqFM' in the fourth parameter depends on the output of the computation.
liftTycon ::
  -- | Compiler flags
  DynFlags ->
  -- | Family Instance Environments, both home and external
  FamInstEnvs ->
  -- | '-->' type constructor
  TyCon ->
  -- | Monad type constructor
  TyCon ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Map of old TyCon's from this module to lifted ones
  UniqFM TyCon TyCon ->
  -- | Map of imported old TyCon's to lifted ones
  TyConMap ->
  -- | Type constructor to be lifted
  TyCon ->
  -- | Next fresh unique supply, the original type constructor
  -- and maybe the lifted type constructor
  IO (UniqSupply, (TyCon, Maybe TyCon))
liftTycon dynFlags instEnvs ftycon mtycon supply tcs tcsM tc
  | isVanillaAlgTyCon tc || isClassTyCon tc = mdo
      -- The tycon definition is cyclic, so we use this let-construction.
      let (s1, tmp) = splitUniqSupply supply
          (s2, tmp2) = splitUniqSupply tmp
          (s3, s4) = splitUniqSupply tmp2
          u1 = uniqFromSupply supply
          u2 = uniqFromSupply s2
          isCls = isJust (tyConClass_maybe tc)
          monadKind = liftedTypeKind `mkVisFunTyMany` liftedTypeKind
          mVar = mkTyVar (mkInternalName u1 (mkTyVarOcc "m") noSrcSpan) monadKind
          mBinder = mkAnonTyConBinder VisArg mVar
      -- Lift the rhs of the underlying datatype definition.
      -- For classes, this lifts the implicit datatype for its dictionary.
      (us2, rhs) <-
        liftAlgRhs
          isCls
          dynFlags
          instEnvs
          ftycon
          mVar
          mtycon
          tcs
          tcsM
          tycon
          s1
          (algTyConRhs tc)
      -- Potentially lift any class information
      flav <- case (tyConRepName_maybe tc, tyConClass_maybe tc) of
        (Just p, Just c) ->
          flip ClassTyCon (liftRepName s4 p)
            <$> liftClass dynFlags ftycon mtycon tcs tcsM tycon us2 c
        (Just p, Nothing) -> return (VanillaAlgTyCon (liftRepName s4 p))
        _ ->
          panicAnyUnsafe "Unknown flavour of type constructor" tc
      -- Create the new TyCon.
      let name = liftName (tyConName tc) u2
          tycon =
            mkAlgTyCon
              name
              (if isClassTyCon tc then tyConBinders tc else mBinder : tyConBinders tc)
              (tyConResKind tc)
              (if isClassTyCon tc then tyConRoles tc else Representational : tyConRoles tc)
              Nothing
              []
              rhs
              flav
              (isGadtSyntaxTyCon tc)
      return (s3, (tc, Just tycon))
  | isTypeSynonymTyCon tc = do
      let u = uniqFromSupply supply
          (supply1, tmp) = splitUniqSupply supply
          (supply2, supply3) = splitUniqSupply tmp
      Just (_, origty) <- return $ synTyConDefn_maybe tc
      let mVar = mkTyVar (mkInternalName (uniqFromSupply supply2) (mkVarOcc "m") noSrcSpan)
                         (mkVisFunTyMany liftedTypeKind liftedTypeKind)
      -- lift only the "inner" type of synonyms
      ty <- replaceTyconTyPure tcs
        <$> liftInnerTy ftycon (mkTyVarTy mVar) supply3 tcsM origty
      let name = liftName (tyConName tc) u
          tycon = mkSynonymTyCon
            name (mkAnonTyConBinder VisArg mVar : tyConBinders tc) (tyConResKind tc)
            (Representational : tyConRoles tc) ty (isTauTyCon tc) (isFamFreeTyCon tc)
            (isForgetfulSynTyCon tc)
      return (supply1, (tc, Just tycon))
  | otherwise = return (supply, (tc, Nothing))

-- | Lift the right hand side of a type constructor.
-- Note that this is part of a fixed-point computation, where the
-- 'UniqFM' in the fourth parameter and the
-- 'TyCon' in the sixth parameter depend on the output of the computation.
liftAlgRhs ::
  -- | Is it a class definition or not
  Bool ->
  -- | Compiler flags
  DynFlags ->
  -- | Family Instance Environments, both home and external
  FamInstEnvs ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Monad' type variable
  Var ->
  -- | 'Monad' type constructor
  TyCon ->
  -- | Map of old TyCon's from this module to lifted ones
  UniqFM TyCon TyCon ->
  -- | Map of imported old TyCon's to lifted ones
  TyConMap ->
  -- | Lifted TyCon of this rhs
  TyCon ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Rhs to be lifted
  AlgTyConRhs ->
  -- | Next fresh unique key supply and lifted rhs
  IO (UniqSupply, AlgTyConRhs)
liftAlgRhs
  isClass
  dflags
  instEnvs
  ftycon
  mvar
  mtycon
  tcs
  tcsM
  tycon
  us
  -- Just lift all constructors of a data decl.
  (DataTyCon cns size ne) = case listSplitUniqSupply us of
    [] -> panicAnyUnsafe "Finite Unique supply" ()
    (u : uss) -> do
      cns' <- zipWithM (liftConstr isClass dflags instEnvs ftycon mvar mtycon tcs tcsM tycon) uss cns
      return (u, DataTyCon cns' size ne)
liftAlgRhs
  isClass
  dflags
  instEnvs
  ftycon
  mvar
  mtycon
  tcs
  tcsM
  tycon
  us
  (NewTyCon dc rhs _ co lev) = do
    let (u1, tmp1) = splitUniqSupply us
        (u2, tmp2) = splitUniqSupply tmp1
        (u3, u4) = splitUniqSupply tmp2
    dc' <- liftConstr isClass dflags instEnvs ftycon mvar mtycon tcs tcsM tycon u1 dc
    let mtype = if isClass then mkTyConTy mtycon else mkTyVarTy mvar
    rhs' <- replaceTyconTyPure tcs <$> liftType ftycon mtype u2 tcsM rhs

    -- Only switch unique and name for datatypes, etc.
    -- (see comment above liftTycon)
    let u = if isClass then co_ax_unique co else uniqFromSupply u3
    let axName = co_ax_name co
    let axNameNew = liftName axName u

    let (vars, roles) =
          if isClass
            then (tyConTyVars tycon, tyConRoles tycon)
            else (mvar : tyConTyVars tycon, Representational : tyConRoles tycon)
    -- Create new coercion axiom.
    let (etavs, etaroles, etarhs) = eta_reduce (reverse vars) (reverse roles) rhs'
    let co' = mkNewTypeCoAxiom axNameNew tycon etavs etaroles etarhs
    -- To be conservative, a class is not a newtype, because we add superclass contexts
    if isClass
      then return (u4, DataTyCon [dc'] 1 False)
      else return (u4, NewTyCon dc' rhs' (etavs, etarhs) co' lev)
liftAlgRhs _ _ _ _ _ _ _ _ _ u c = return (u, c)

-- | Eta-reduce type variables of a newtype declaration to generate a
-- more siple newtype coercion.
-- Copied from GHC.Tc.TyCl.Build
eta_reduce ::
  -- | Reversed list of type variables
  [TyVar] ->
  -- | Reversed list of their roles
  [Role] ->
  -- | Type of the rhs
  Type ->
  -- | Eta-reduced type
  -- (tyvars in normal order)
  ([TyVar], [Role], Type)
eta_reduce (a : as) (_ : rs) ty
  | Just (fun, arg) <- splitAppTy_maybe ty,
    Just tv <- getTyVar_maybe arg,
    tv == a,
    not (a `elemVarSet` tyCoVarsOfType fun) =
      eta_reduce as rs fun
eta_reduce tvs rs ty = (reverse tvs, reverse rs, ty)
