{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecursiveDo   #-}
{-|
Module      : Plugin.Trans.TyCon
Description : Functions to lift type constructors.
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a function to lift a type constructor,
regardless of whether or not it stems from a
class, data, type or newtype declaration.
-}
module Plugin.Trans.TyCon (liftTycon) where

import Control.Monad

import GhcPlugins
import UniqMap
import CoAxiom
import FamInstEnv

import Plugin.Trans.Constr
import Plugin.Trans.Class
import Plugin.Trans.Type
import Plugin.Trans.Var
import Plugin.Trans.Util

-- We ONLY want to keep the original version of (Data/New/Syn) definitions.
-- Thios is why we assign them a new Unique and name, while other TyCons
-- (currently only classes) get to keep their name.
-- When entering information about the new and updated TyCons into environments,
-- The new unique ensures that we do not override any information that we need
-- to keep, in contrast to the unchanged Unique for Typeclasses, etc.
-- | Lift a type constructor, if possible.
-- Note that this is part of a fixed-point computation, where the
-- 'UniqMap' in the fourth parameter depends on the output of the computation.
liftTycon :: DynFlags            -- ^ Compiler flags
          -> FamInstEnvs         -- ^ Family Instance Environments, both home and external
          -> TyCon               -- ^ 'Fun' type constructor
          -> TyCon               -- ^ 'Monad' type constructor
          -> UniqSupply          -- ^ Fresh supply of unique keys
          -> UniqMap TyCon TyCon -- ^ Map of old TyCon's from this module to lifted ones
          -> TyConMap            -- ^ Map of imported old TyCon's to lifted ones
          -> TyCon               -- ^ Type constructor to be lifted
          -> IO (UniqSupply, (TyCon, Maybe TyCon))
          -- ^ Next fresh unique supply, the original type constructor
          -- and maybe the lifted type constructor
liftTycon dflags instEnvs ftycon mtycon supply tcs tcsM tc
  | isVanillaAlgTyCon tc || isClassTyCon tc = mdo
    -- The tycon definition is cyclic, so we use this let-construction.
    let u = uniqFromSupply supply
        (supply1, other) = splitUniqSupply supply
        (supply2, supply3) = splitUniqSupply supply1
    -- Lift the rhs of the underlying datatype definition.
    -- For classes, this lifts the implicit datatype for its dictionary.
    let mVar = mkTyVar (mkInternalName (uniqFromSupply supply2) (mkVarOcc "m") noSrcSpan) (mkVisFunTy liftedTypeKind liftedTypeKind)
    (us2, rhs) <- liftAlgRhs (isClassTyCon tc) dflags instEnvs ftycon mVar mtycon tcs tcsM tycon other
      (algTyConRhs tc)
    -- Potentially lift any class information
    flav <- case (tyConRepName_maybe tc, tyConClass_maybe tc) of
          (Just p, Just c ) -> flip ClassTyCon p <$>
            liftClass ftycon mtycon tcs tcsM tycon us2 c
          (Just p, Nothing) -> return (VanillaAlgTyCon p)
          _                 ->
            panicAnyUnsafe "Unknown flavour of type constructor" tc
    -- Create the new TyCon.
    let mBinder = mkAnonTyConBinder VisArg mVar
    let name = liftName (tyConName tc) u
        tycon = mkAlgTyCon
          name (if isClassTyCon tc then tyConBinders tc else mBinder : tyConBinders tc) (tyConResKind tc)
          (if isClassTyCon tc then tyConRoles tc else Representational : tyConRoles tc) Nothing []
          rhs flav (isGadtSyntaxTyCon tc)
    return (supply3, (tc, Just tycon))
  | isTypeSynonymTyCon tc = do
    let u = uniqFromSupply supply
        (supply1, supply2) = splitUniqSupply supply
    Just (_, origty) <- return $ synTyConDefn_maybe tc
    -- lift only the "inner" type of synonyms
    ty <- replaceTyconTyPure tcs
      <$> liftInnerTy ftycon (mkTyConTy mtycon) supply2 tcsM origty
    let name | isClassTyCon tc = tyConName tc
             | otherwise       = liftName (tyConName tc) u
        tycon = mkSynonymTyCon
          name (tyConBinders tc) (tyConResKind tc)
          (tyConRoles tc) ty (isTauTyCon tc) (isFamFreeTyCon tc)
    return (supply1, (tc, Just tycon))
  | isFamilyTyCon tc = mdo
      let u1 = uniqFromSupply supply
          (supply', other) = splitUniqSupply supply
          u2 = uniqFromSupply other
          name = liftName (tyConName tc) u1
          flav = case famTyConFlav_maybe tc of
            Nothing
              -> panicAnyUnsafe "Type family is missing its flavour" tc
            Just (DataFamilyTyCon nm)
              -> DataFamilyTyCon (liftName nm u2)
            Just OpenSynFamilyTyCon
              -> OpenSynFamilyTyCon
            Just (ClosedSynFamilyTyCon mbax)
              -> ClosedSynFamilyTyCon (fmap (liftFamAx u2 tycon) mbax)
            Just AbstractClosedSynFamilyTyCon
              -> AbstractClosedSynFamilyTyCon
            Just (BuiltInSynFamTyCon b)
              -> BuiltInSynFamTyCon b
          parent = case tyConFlavour tc of
            DataFamilyFlavour     p -> p
            OpenTypeFamilyFlavour p -> p
            _                       -> Nothing
      parent' <- maybe (return Nothing)
                   (fmap Just . lookupTyConMap GetNew tcsM) parent
      let parentCls = parent' >>= lookupUniqMap tcs >>= tyConClass_maybe
          tycon = mkFamilyTyCon name (tyConBinders tc) (tyConResKind tc)
                    (tyConFamilyResVar_maybe tc) flav parentCls
                    (tyConInjectivityInfo tc)
      return (supply', (tc, Just tycon))
  | otherwise = return (supply, (tc, Nothing))

-- Sadly, newtype constr have to be treated differently than data constr
-- They are treated more like a type synonym, as we would end up with a double
-- nesting of the monad/nondet type.
-- Consider newtype New a = a and assume we lift this type like normal
-- to newtype NewND a = ND a.
-- Remember that at runtime, NewND and New are transparent, e.g. at runtime
-- each occurrence of NewND and New is de-facto removed.
-- Thus, if we look at a funcion type
-- test :: New a -> a, its lifted version is test :: ND (NewND a) --> ND a.
-- If we were to treat NewND as we said above, at runtime test would
-- have effectively the following signature:
-- test :: ND (ND a) --> ND a, which has one application of ND too much.
-- Thus, we use the lifting of type synonyms for newtypes, as that gets rid
-- of the inner ND application.
-- BUT for the newtypes that represent dictionaries for class definitions,
-- we have to use the normal constructor lifting.
-- This is required, because the argument of that newtype is the same as
-- the type of the function from the typeclass. The function type gets
-- lifted normally, and so we do the same with the newtype constructor.
-- (At least without kind polymorphism), a Class cannot occur nested inside of
-- another type like in the example with test.
-- So the special treatment of newtype constructors for classes
-- does not result in any (further) problems.
-- | Lift the right hand side of a type constructor.
-- Note that this is part of a fixed-point computation, where the
-- 'UniqMap' in the fourth parameter and the
-- 'TyCon' in the sixth parameter depend on the output of the computation.
liftAlgRhs :: Bool                -- ^ Is it a class definition or not
           -> DynFlags            -- ^ Compiler flags
           -> FamInstEnvs         -- ^ Family Instance Environments, both home and external
           -> TyCon               -- ^ 'Fun' type constructor
           -> Var                 -- ^ 'Monad' type variable
           -> TyCon               -- ^ 'Monad' type constructor
           -> UniqMap TyCon TyCon -- ^ Map of old TyCon's from this module to lifted ones
           -> TyConMap            -- ^ Map of imported old TyCon's to lifted ones
           -> TyCon               -- ^ Lifted TyCon of this rhs
           -> UniqSupply          -- ^ Fresh supply of unique keys
           -> AlgTyConRhs         -- ^ Rhs to be lifted
           -> IO (UniqSupply, AlgTyConRhs)
          -- ^ Next fresh unique key supply and lifted rhs
liftAlgRhs isClass dflags instEnvs ftycon mvar mtycon tcs tcsM tycon us
  -- Just lift all constructors of a data decl.
  (DataTyCon cns size ne) = do
    let uss = listSplitUniqSupply us
    cns' <- zipWithM
      (liftConstr isClass dflags instEnvs ftycon mvar mtycon tcs tcsM tycon) (tail uss) cns
    return (head uss, DataTyCon cns' size ne)
liftAlgRhs isClass dflags instEnvs ftycon mvar mtycon tcs tcsM tycon us
  -- Depending on the origin of this newtype declaration (class or not),
  -- Perform a full lifting or just and inner lifting.
  (NewTyCon dc rhs _ co lev) = do
    let (u1, tmp1) = splitUniqSupply us
        (u2, tmp2) = splitUniqSupply tmp1
        (u3, u4  ) = splitUniqSupply tmp2
    dc' <- liftConstr isClass dflags instEnvs ftycon mvar mtycon tcs tcsM tycon u1 dc
    let mtype = if isClass then mkTyConTy mtycon else mkTyVarTy mvar
    rhs' <- replaceTyconTyPure tcs <$> liftType ftycon mtype u2 tcsM rhs

    -- Only switch unique and name for datatypes, etc.
    -- (see comment above liftTycon)
    let u = if isClass then co_ax_unique co else uniqFromSupply u3
    let axName = co_ax_name co
    let axNameNew | isClass   = setNameUnique axName u
                  | otherwise = liftName axName u

    -- Create new coercion axiom.
    let (etavs, etaroles, etarhs) = etaReduce (reverse (tyConTyVars tycon))
                                      (reverse (tyConRoles tycon)) rhs'
    let co' = mkNewTypeCoAxiom axNameNew tycon etavs etaroles etarhs
    return (u4, NewTyCon dc' rhs' (etavs, etarhs) co' lev)
liftAlgRhs _ _ _ _ _ _ _ _ _ u c = return (u, c)

liftFamAx :: Unique -> TyCon -> CoAxiom Branched -> CoAxiom Branched
liftFamAx _ _ _ = panicAnyUnsafe "Type families not supported" ()

-- | Eta-reduce type variables of a newtype declaration to generate a
-- more siple newtype coercion.
-- Copied from GHC.Tc.TyCl.Build
etaReduce :: [TyVar]       -- ^ Reversed list of type variables
           -> [Role]        -- ^ Reversed list of their roles
           -> Type          -- ^ Type of the rhs
           -> ([TyVar], [Role], Type)  -- ^ Eta-reduced type
                                       -- (tyvars in normal order)
etaReduce (a:as) (_:rs) ty | Just (fun, arg) <- splitAppTy_maybe ty,
                              Just tv <- getTyVar_maybe arg,
                              tv == a,
                              not (a `elemVarSet` tyCoVarsOfType fun)
                            = etaReduce as rs fun
etaReduce tvs rs ty = (reverse tvs, reverse rs, ty)
