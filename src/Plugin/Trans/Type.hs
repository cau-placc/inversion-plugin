{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Plugin.Trans.Type
-- Description : Various functions to get or lift type-related things
-- Copyright   : (c) Kai-Oliver Prott (2020)
-- Maintainer  : kai.prott@hotmail.de
--
-- This module contains our various functions to lift types and everything else
-- that is concerned with loading, dissecting or transforming type-related things.
module Plugin.Trans.Type where

import Control.Monad
import Control.Arrow
import Control.Exception
import Data.IORef
import Data.List
import Data.Maybe
import Data.Generics.Aliases
import Data.Generics.Schemes
import GHC
import GHC.Core.Class
import GHC.Core.Predicate
import GHC.Core.TyCo.Rep
import GHC.Iface.Env
import GHC.Iface.Syntax
import GHC.Plugins hiding (extendTvSubst, substTy)
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Env
import GHC.Tc.Utils.Instantiate
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.TcType
import GHC.Unit.Finder
import GHC.Unit.External
import Language.Haskell.TH.Syntax
  ( ModName (..),
    Name (..),
    NameFlavour (..),
    OccName (..),
    PkgName (..),
  )

import Plugin.Trans.Util
import Plugin.Effect.Monad
import Plugin.Trans.Import
import Plugin.Trans.Var

-- This Type contains an IORef, because looking up the mapping between
-- new <-> old type constructors needs IO.
-- We do not want to lookup the full mapping on plugin startup, as
-- we will probably only need a fraction of those anyway

-- | A mapping between the lifted and unlifted version of each type constructor,
-- loaded in lazily.
type TyConMap =
  ( Env TcGblEnv TcLclEnv,
    TcRef
      ( UniqFM TyCon TyCon, -- Old -> New
        UniqFM TyCon TyCon, -- New -> Old
        UniqSet TyCon, -- Old
        UniqSet TyCon -- New
      )
  )

-- | Get the 'FL' monad type constructor.
getMonadTycon :: TcM TyCon
getMonadTycon = do
  let mdlStr = "Plugin.Effect.Monad"
  let nmStr = "FL"
  getTyCon mdlStr nmStr

-- | Get the '-->' function type constructor.
getFunTycon :: TcM TyCon
getFunTycon = do
  let mdlStr = "Plugin.Effect.Monad"
  let nmStr = "-->"
  getTyCon mdlStr nmStr

-- | Get the 'Lifted' (type family) type constructor.
getLiftedTycon :: TcM TyCon
getLiftedTycon = do
  let mdlStr = "Plugin.Lifted"
  let nmStr = "Lifted"
  getTyCon mdlStr nmStr

-- | Get the 'Sharing' type constructor.
getSharingTycon :: TcM TyCon
getSharingTycon = do
  let mdlStr = "Plugin.Effect.Monad"
  let nmStr = "MonadShare"
  getTyCon mdlStr nmStr

-- | Get the 'Shareable' class type constructor.
getShareClassTycon :: TcM TyCon
getShareClassTycon = case ''Shareable of
  Name (OccName occ) (NameG _ (PkgName pkg) (ModName mdl)) ->
    getTyConPkg pkg mdl occ
  _ -> panicAny "Failed to retrieve Shareable TyCon" ()

-- | Get the 'Shareable' class.
getShareClass :: TcM Class
getShareClass = fromJust . tyConClass_maybe <$> getShareClassTycon

-- | Get the 'Shareable' dictionary type.
getShareClassDictType :: TcM Type
getShareClassDictType = do
  cls <- getShareClass
  let (tyvars, _, _, _) = classBigSig cls
  let clas_tyvars = snd (tcSuperSkolTyVars tyvars)
  return (mkClassPred cls (mkTyVarTys clas_tyvars))

-- | Get the 'Normalform' class type constructor.
getNFClassTycon :: TcM TyCon
getNFClassTycon = case ''NormalForm of
  Name (OccName occ) (NameG _ (PkgName pkg) (ModName mdl)) ->
    getTyConPkg pkg mdl occ
  _ -> panicAny "Failed to retrieve Normalform TyCon" ()

-- | Get the 'Generic' class type constructor.
getGenericClassTycon :: TcM TyCon
getGenericClassTycon = getTyConPkg "base" "GHC.Generics" "Generic"

-- | Get a type constructor from the given module and with the given name.
getTyCon ::
  -- | Module name
  String ->
  -- | TyCon name
  String ->
  TcM TyCon
getTyCon mname name = do
  mdl <- findImportedOrPanic mname
  tcLookupTyCon =<< lookupOrig mdl (mkTcOcc name)

-- | Get a type constructor from the given
-- package, module and with the given name.
getTyConPkg ::
  -- | Package name
  String ->
  -- | Module name
  String ->
  -- | TyCon name
  String ->
  TcM TyCon
getTyConPkg pname mname name = do
  mdl <- findImportedPkgOrPanic mname pname
  tcLookupTyCon =<< lookupOrig mdl (mkTcOcc name)

{- If we have a type like (T (a -> b)), the correct lifted type is
   ND (TND (ND a -> ND b))
   Note that the function type is NOT lifted, as that lifting is integrated in
   the lifted type constructor ND
   So sometimes we do not want to lift the outermost part of a type that occurs
   somewhere nested.
   This can even occurr in more complex settings
   (T a) (a -> b) should be lifted to
   ND ((TND a) (ND a -> ND b)
   This is why we use liftInnerTy instead of liftType for nested types.

   Normally we want to add Shareable constraints to every type variable,
   using QuantifiedConstraints if possible.
   If this is undesired, use liftTypeNoShareable
-}

-- | Lift a type with the given parameters and add 'Shareable' constraints.
liftType ::
  -- | 'Shareable' type constructor
  TyCon ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Type constructor map between lifted <-> unlifted
  TyConMap ->
  -- | Type to be lifted
  Type ->
  -- | Lifted type with 'Shareable' constraints
  IO Type
liftType = liftTypeParametrized True

-- | Lift a type and add 'Shareable' constraints.
liftTypeTcM :: TyConMap -> Type -> TcM Type
liftTypeTcM tcs ty = do
  stc <- getShareClassTycon
  ftc <- getFunTycon
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  liftIO (liftType stc ftc mty us tcs ty)

-- | Lift a type with the given parameters,
-- without adding 'Shareable' constraints.
liftTypeNoShareable ::
  -- | 'Shareable' type constructor
  TyCon ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Type constructor map
  TyConMap ->
  -- | Type to be lifted
  Type ->
  -- | Lifted type, no 'Shareable' constraints
  IO Type
liftTypeNoShareable = liftTypeParametrized False

-- | Lift a type with the given parameters.
-- If the first parameter is True, add 'Shareable' constraints.
liftTypeParametrized ::
  -- | Add 'Shareable' constraints or not.
  Bool ->
  -- | 'Shareable' type constructor
  TyCon ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Type constructor map
  TyConMap ->
  -- | Type to be lifted
  Type ->
  -- | Lifted type
  IO Type
liftTypeParametrized sh stc ftc mty s tcs  = liftType' s
  where
    liftType' :: UniqSupply -> Type -> IO Type
    liftType' us ft@(ForAllTy b ty)
      -- If we are supposed to add 'Shareable' constraints, do it.
      | sh = do
          let -- Get required fresh unique keys.
              (u1, u2) = splitUniqSupply us
              uss = listSplitUniqSupply u1
              -- Split off invisible pi-types (e.g., forall and constraints)
              (pis, inner) = splitInvisPiTys ft
              -- Get all named binders (e.g., forall)
              bs = mapMaybe namedTyCoVarBinder_maybe pis
              -- Function to create 'Shareable' type
              mkShareType t' = mkTyConApp stc [mty, t']
              -- Make a 'Sharable' constraint for each variable
              cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
          -- Update any type constructors of the pre-existing constraints.
          pis' <- mapM (replacePiTy stc ftc mty us tcs) pis
          -- Include 'Shareable' constraints.
          mkPiTys pis' . flip (foldr mkInvisFunTyMany) cons
            -- use the top-level version to get the isDictTy check
            <$> liftTypeParametrized sh stc ftc mty u2 tcs inner
      | otherwise = ForAllTy b <$> liftTypeParametrized sh stc ftc mty us tcs ty
    -- Types to the left of and invisible function type (=>) are constraints.
    liftType' us (FunTy InvisArg m ty1 ty2) =
      FunTy InvisArg m <$> liftInnerTyParametrized sh stc ftc mty s tcs ty1
        <*> liftType' us ty2
    -- Wrap a visible function type in our monad, except when it is a
    -- visible dictionary applictation (not possible in GHC yet).-
    liftType' us (FunTy VisArg m ty1 ty2)
      | isDictTy ty1 =
          FunTy VisArg m <$> liftInnerTyParametrized sh stc ftc mty s tcs ty1
            <*> liftType' us ty2
      | otherwise = do
          let (u1, u2) = splitUniqSupply us
          ty1' <- liftInnerTyParametrized sh stc ftc mty u1 tcs ty1
          ty2' <- liftInnerTyParametrized sh stc ftc mty u2 tcs ty2
          return (mkAppTy mty (mkTyConApp ftc [mty, ty1', ty2']))
    liftType' us (CastTy ty kc) =
      flip CastTy kc <$> liftType' us ty
    liftType' _ (CoercionTy c) =
      return (CoercionTy c)
    liftType' _ ty@(LitTy _) =
      return (mkAppTy mty ty)
    -- Lift a type application.
    liftType' us (AppTy ty1 ty2) =
      let (u1, u2) = splitUniqSupply us
       in (mkAppTy mty .) . AppTy
            <$> liftInnerTyParametrized sh stc ftc mty u1 tcs ty1
            <*> liftInnerTyParametrized sh stc ftc mty u2 tcs ty2
    -- Lift a type application of a type constructor.
    -- If it is a type class constraint or ANY, do not wrap it with our monad.
    liftType' us (TyConApp tc tys)
      | Just ty <- synTyConRhs_maybe tc,
        [] <- tys,
        TyConApp tc' tys' <- ty,
        isJust (tyConClass_maybe tc' >>= flip isCallStackPred tys')
        = return $ TyConApp tc tys
      | anyTyCon == tc || liftedRepTyCon == tc || manyDataConTyCon == tc || oneDataConTyCon == tc
        = return $ TyConApp tc tys
      | isClassTyCon tc = do
          tc' <- lookupTyConMap GetNew tcs tc
          tys' <- mapM (liftInnerTyParametrized sh stc ftc mty us tcs) tys
          return (TyConApp tc' tys')
      | otherwise = do
          tc' <- lookupTyConMap GetNew tcs tc
          tys' <- mapM (liftInnerTyParametrized sh stc ftc mty us tcs) tys
          if tc' == intTyCon
            then return (mkAppTy mty (mkTyConTy intTyCon))
            else return (mkAppTy mty (TyConApp tc' (mty : tys')))
    liftType' _ ty@(TyVarTy _) =
      return (mkAppTy mty ty)

replacePiTyTcM :: TyConMap -> TyBinder -> TcM TyBinder
replacePiTyTcM tcs b = do
  mtc <- getMonadTycon
  stc <- getMonadTycon
  ftc <- getFunTycon
  us <- getUniqueSupplyM
  liftIO (replacePiTy stc ftc (mkTyConTy mtc) us tcs b)

-- | Update type constructors in a pi-type
replacePiTy :: TyCon -> TyCon -> Type -> UniqSupply -> TyConMap -> TyBinder -> IO TyBinder
replacePiTy _ _ _ _ _ (Named b) = return (Named b)
replacePiTy stc ftc mty us tcs (Anon f (Scaled m t)) =
  (\m' t' -> Anon f (Scaled m' t'))
    <$> replaceTyconTy tcs m <*> liftInnerTy stc ftc mty us tcs t

-- | Create 'Shareable' constraint for the given type variable.
mkShareable :: (Type -> Type) -> UniqSupply -> TyCoVarBinder -> Maybe Type
mkShareable mkShareType us b = mkShareableFor us mkShareType b Nothing

-- | Create 'Shareable' constraint for the given type variable and
-- add it as an invisible argument in front of the given type.
-- Returns Nothing if the type variable has an incompatible result kind.
mkShareableFor ::
  UniqSupply ->
  (Type -> Type) ->
  TyCoVarBinder ->
  Maybe Type ->
  Maybe Type
mkShareableFor us mkShareType b@(Bndr v _) rest =
  let args = fst (splitFunTys (tyVarKind v))
      (u1, u2) = splitUniqSupply us
      vs = zipWith (\(Scaled _ t) -> mkTyVarWith t) args (uniqsFromSupply u1)
      bs = map (`Bndr` Inferred) vs
      vskinds = map mkTyVarTy vs
      innr = map ((. Just) . mkShareableFor u2 mkShareType) bs
      -- innr = [\ty -> ForAllTy b . (Shareable bty => ty)]
      current = mkShareType (mkAppTys (mkTyVarTy v) vskinds)
      constraint = foldrM (\f c -> f c) current innr
   in if snd (splitFunTys (tyVarKind v)) `eqType` liftedTypeKind
        then -- only include it iff the result kind of v == Type
        case rest of
          Nothing -> constraint
          Just r -> fmap (ForAllTy b . (`mkInvisFunTyMany` r)) constraint
        else Nothing

-- | Create a type variable with the given kind and unique key.
mkTyVarWith :: Kind -> Unique -> TyVar
mkTyVarWith k u = mkTyVar (mkSystemName u (mkTyVarOcc ("v_" ++ show u))) k

liftTypeIfRequiredTcM :: TyConMap -> Type -> TcM Type
liftTypeIfRequiredTcM tcs ty = do
  mtc <- getMonadTycon
  ftc <- getFunTycon
  stc <- getShareClassTycon
  us <- getUniqueSupplyM
  liftIO $ liftTypeIfRequired stc ftc mtc us tcs ty

-- | Lift a type if it is not lifted already.
liftTypeIfRequired ::
  TyCon ->
  TyCon ->
  TyCon ->
  UniqSupply ->
  TyConMap ->
  Type ->
  IO Type
liftTypeIfRequired stc ftc mtycon us tcs ty =
  case splitTyConApp_maybe (snd (splitInvisPiTys ty)) of
    -- The type might already be lifted, if this is a class method
    -- from an imported (non built-in) class
    Just (tc, _) | tc == mtycon -> replaceTyconTy tcs ty
    _ -> liftType stc ftc (mkTyConTy mtycon) us tcs ty

-- | Lift a type with the given arguments and
-- without wrapping it in our monad at the top of the type.
-- Fails if the type has an invisible pi-type (e,.g., forall, constraint)
-- at the top.
liftInnerTy ::
  -- | 'Shareable' type constructor
  TyCon ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Type constructor map
  TyConMap ->
  -- | Type to be lifted
  Type ->
  -- | Lifted type with 'Shareable' constraints
  IO Type
liftInnerTy = liftInnerTyParametrized True

-- | Lift a type without wrapping it in our monad at the top of the type.
-- Fails if the type has an invisible pi-type (e,.g., forall, constraint)
-- at the top.
liftInnerTyTcM :: TyConMap -> Type -> TcM Type
liftInnerTyTcM tcs ty = do
  stc <- getShareClassTycon
  ftc <- getFunTycon
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  liftIO (liftInnerTy stc ftc mty us tcs ty)

-- | Lift a type without wrapping it in our monad at the top of the type.
-- Fails if the type has an invisible pi-type (e,.g., forall, constraint)
-- at the top. The function will only add 'Shareable' constraints if
-- the first argument is True.
liftInnerTyParametrized ::
  -- | Add 'Shareable' constraints or not.
  Bool ->
  -- | 'Shareable' type constructor
  TyCon ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Type constructor map
  TyConMap ->
  -- | Type to be lifted
  Type ->
  -- | Lifted type
  IO Type
liftInnerTyParametrized b stc ftc mty us tcs ty = do
  ty' <- liftTypeParametrized b stc ftc mty us tcs ty
  return $ case splitTyConApp_maybe ty' of
    Just (tc, [inner])
      | mkTyConTy tc `eqType` mty ->
          inner
    _ -> case splitAppTy_maybe ty' of
      Just (ty1, ty2) | ty1 `eqType` mty -> ty2
      _                                  -> ty'

-- | Lift the type of a data value constructor.
liftConType ::
  TyCon ->
  TyCon ->
  Type ->
  UniqSupply ->
  TyConMap ->
  Type ->
  IO Type
liftConType = liftConTypeWith False

-- | Lift the type of a newtype value constructor.
liftNewConType ::
  TyCon ->
  TyCon ->
  Type ->
  UniqSupply ->
  TyConMap ->
  Type ->
  IO Type
liftNewConType = liftConTypeWith True

-- When lifting the type of a constructor, we only want to lift constructor args
-- and not `->` or the result.
-- To do this, we generally do not create any applications of mty,
-- but instead switch to the normal lifting function
-- when we are to the left of an arrow.
-- For newtypes, we also do not want to wrap the constructor args,
-- so use liftInnerTy to the left of functions, if required

-- | Lift a data or newtype value constructor.
liftConTypeWith ::
  -- | Is a newtype value constructor
  Bool ->
  -- | 'Shareable' type constructor
  TyCon ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Type constructor map
  TyConMap ->
  -- | Type to be lifted
  Type ->
  -- | Lifted type
  IO Type
liftConTypeWith isNew stc ftc mty us tcs = liftType'
  where
    liftType' :: Type -> IO Type
    liftType' (ForAllTy bs ty) =
      ForAllTy bs <$> liftType' ty
    liftType' (FunTy InvisArg m ty1 ty2) =
      FunTy InvisArg m <$> replaceTyconTy tcs ty1 <*> liftType' ty2
    liftType' (FunTy VisArg m ty1 ty2)
      | isDictTy ty1 =
          FunTy VisArg m <$> replaceTyconTy tcs ty1 <*> liftType' ty2
      | isNew =
          FunTy VisArg m <$> liftInnerTy stc ftc mty us tcs ty1 <*> liftType' ty2
      | otherwise =
          FunTy VisArg m <$> liftType stc ftc mty us tcs ty1 <*> liftType' ty2
    liftType' (CastTy ty kc) =
      flip CastTy kc <$> liftType' ty
    liftType' (CoercionTy c) =
      return (CoercionTy c)
    liftType' (LitTy l) =
      return (LitTy l)
    liftType' (AppTy ty1 ty2) =
      AppTy <$> liftInnerTy stc ftc mty us tcs ty1
        <*> liftInnerTy stc ftc mty us tcs ty2
    liftType' (TyConApp tc tys) = do
      tc' <- lookupTyConMap GetNew tcs tc
      tys' <- mapM (liftInnerTy stc ftc mty us tcs) tys
      return (TyConApp tc' tys')
    liftType' (TyVarTy v) =
      return (TyVarTy v)

-- | Replace all type constructors in a type with its lifted version.
replaceTyconTy :: TyConMap -> Type -> IO Type
replaceTyconTy tcs = replaceTyconTy'
  where
    replaceTyconTy' (ForAllTy b ty) =
      ForAllTy b <$> replaceTyconTy' ty
    replaceTyconTy' (FunTy f m ty1 ty2) =
      FunTy f m <$> replaceTyconTy' ty1 <*> replaceTyconTy' ty2
    replaceTyconTy' (CastTy ty kc) =
      flip CastTy kc <$> replaceTyconTy' ty
    replaceTyconTy' (CoercionTy c) =
      return (CoercionTy c)
    replaceTyconTy' (LitTy l) =
      return (LitTy l)
    replaceTyconTy' (AppTy ty1 ty2) =
      AppTy <$> replaceTyconTy' ty1 <*> replaceTyconTy' ty2
    replaceTyconTy' (TyConApp tc tys)
      | tc == unrestrictedFunTyCon = do
          tc' <- lookupTyConMap GetNew tcs funTyCon
          tys' <- mapM (replaceTyconTy tcs) tys
          return (TyConApp tc' (manyDataConTy : tys'))
      | otherwise = do
          tc' <- lookupTyConMap GetNew tcs tc
          tys' <- mapM (replaceTyconTy tcs) tys
          return (TyConApp tc' tys')
    replaceTyconTy' (TyVarTy v) =
      return (TyVarTy v)

replaceTyconScaled :: TyConMap -> Scaled Type -> IO (Scaled Type)
replaceTyconScaled tcs (Scaled m ty) =
  Scaled <$> replaceTyconTy tcs m <*> replaceTyconTy tcs ty

-- A default method for "Class cls" with a default type sig of
-- DefaultConstraints => classFunTy
-- has a type
-- forall cls. Class cls => DefaultConstraints => classFunTy
-- It should be lifted to
-- forall cls. Class cls => Shareable cls => DefaultConstraints => classFunTy
-- Whereas the normal lifting would include the Shareable after all
-- DefaultConstraints, which we DO NOT want.
liftDefaultType :: TyConMap -> Class -> Type -> TcM Type
liftDefaultType tcs cls ty = do
  -- if cls has N class type variables,
  -- we have to split off N forall's and the class constraint.
  let (bs1, ty1) = splitInvisPiTysN (classArity cls + 1) ty
      bs = mapMaybe namedTyCoVarBinder_maybe bs1
  uss <- replicateM (length bs) getUniqueSupplyM
  mtc <- getMonadTycon
  stc <- getShareClassTycon
  let mkShareType t' = mkTyConApp stc [mkTyConTy mtc, t']
      cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
  bs' <- mapM (replacePiTyTcM tcs) bs1
  mkPiTys bs' . flip (foldr mkInvisFunTyMany) cons
    <$> liftTypeTcM tcs ty1

-- | Lift only the result type of a type.
-- Sometimes (e.g. for records) we only need to lift the result of a type
liftResultTy ::
  -- | 'Shareable' type constructor
  TyCon ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Type constructor map
  TyConMap ->
  -- | Type to be lifted
  Type ->
  -- | Lifted type
  IO Type
liftResultTy stc ftc mty us tcs = liftResultTy'
  where
    liftResultTy' (ForAllTy b ty) =
      ForAllTy b <$> liftResultTy' ty
    liftResultTy' (FunTy f m ty1 ty2) =
      FunTy f m <$> replaceTyconTy tcs ty1 <*> liftResultTy' ty2
    liftResultTy' (CastTy ty kc) =
      flip CastTy kc <$> liftResultTy' ty
    liftResultTy' ty = liftTypeNoShareable stc ftc mty us tcs ty

-- When lifting the type applications in a HsWrapper,
-- we have to remember that the type variables
-- (that are instantiated by this wrapper)
-- are already wrapped in the monadic type.
-- Thus, we use liftInnerTy

-- | Lift the type applications and update type constructors inside a wrapper.
-- Reomves any evidence applications.
liftWrapper ::
  -- | inner lifting or not
  Bool ->
  -- | 'Shareable' type constructor
  TyCon ->
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Type constructor map
  TyConMap ->
  -- | Wrapper to be lifted
  HsWrapper ->
  -- | Lifted wrapper
  IO HsWrapper
liftWrapper b stc ftc mty us tcs = liftWrapper'
  where
    liftWrapper' (WpCompose w1 w2) =
      WpCompose <$> liftWrapper' w1 <*> liftWrapper' w2
    liftWrapper' (WpFun w1 w2 (Scaled m ty) sd) =
      (\w1' w2' m' ty' -> WpFun w1' w2' (Scaled m' ty') sd)
        <$> liftWrapper' w1
        <*> liftWrapper' w2
        <*> replaceTyconTy tcs m
        <*> (if b then liftTypeNoShareable else liftInnerTy)
          stc
          ftc
          mty
          us
          tcs
          ty
    liftWrapper' (WpCast (SubCo (Refl ty))) =
      WpCast . SubCo . Refl <$> replaceTyconTy tcs ty
    liftWrapper' (WpTyApp appl)
      | TyConApp tc [inner] <- appl,
        mkTyConTy tc `eqType` mty =
          WpTyApp <$> replaceTyconTy tcs inner
      | otherwise = WpTyApp <$> liftInnerTy stc ftc mty us tcs appl
    liftWrapper' (WpTyLam v) = return (WpTyLam v)
    -- remove any other thing that was here after typechecking
    liftWrapper' _ = return WpHole

-- | Lift the type applications and update type constructors inside a wrapper.
-- Reomves any evidence applications.
liftWrapperTcM :: Bool -> TyConMap -> HsWrapper -> TcM HsWrapper
liftWrapperTcM b tcs w = do
  stc <- getShareClassTycon
  ftc <- getFunTycon
  mty <- mkTyConTy <$> getMonadTycon
  us <- getUniqueSupplyM
  liftIO (liftWrapper b stc ftc mty us tcs w)

-- | Update type constructors inside a wrapper.
replaceWrapper :: TyConMap -> HsWrapper -> TcM HsWrapper
replaceWrapper tcs = replaceWrapper'
  where
    replaceWrapper' (WpCompose w1 w2) =
      WpCompose <$> replaceWrapper' w1 <*> replaceWrapper' w2
    replaceWrapper' (WpFun w1 w2 (Scaled m ty) sd) =
      (\w1' w2' m' ty' -> WpFun w1' w2' (Scaled m' ty') sd)
        <$> replaceWrapper' w1
        <*> replaceWrapper' w2
        <*> liftInnerTyTcM tcs m
        <*> liftInnerTyTcM tcs ty
    replaceWrapper' (WpCast (SubCo (Refl ty))) =
      WpCast . SubCo . Refl <$> liftInnerTyTcM tcs ty
    replaceWrapper' (WpTyApp appl) =
      WpTyApp <$> liftInnerTyTcM tcs appl
    replaceWrapper' (WpEvApp t) =
      WpEvApp <$> everywhereM (mkM replaceCore) t
    replaceWrapper' w =
      return w

    replaceCore v = setVarType v <$> liftInnerTyTcM tcs (varType v)

-- | Lift the error branch (e.g., of a missing type class implementation)
-- expression generated by GHC.
-- The error branch on a GHC error is something like
-- Control.Exception.Base.errFun @ 'GHC.Types.LiftedRep @ a "..."#.
-- Here, we want to lift the type applications, EXCEPT the LiftedRep.
liftErrorWrapper :: TyConMap -> HsWrapper -> TcM HsWrapper
liftErrorWrapper tcs (WpTyApp ty)
  | maybe True (not . isPromotedDataCon) (fst <$> splitTyConApp_maybe ty) =
      WpTyApp <$> liftTypeTcM tcs ty
liftErrorWrapper _ w = return w

-- | Enumeration of lookup directions for the type constructor map.
data LookupDirection
  = -- | Look up the lifted version with the unlifted.
    GetNew
  | -- | Look up the unlifted version with the lifted.
    GetOld
  deriving (Eq, Show)

-- | Look up the other version of a type constructor in the given map
-- or return the argument unchanged if the requested version does not exist.
-- This function lazily loads any new type constructor mappings on demand.
lookupTyConMap :: LookupDirection -> TyConMap -> TyCon -> IO TyCon
lookupTyConMap d (env, ref) tc = do
  -- Get the current state of our map.
  tcs@(mn, mo, sn, so) <- readIORef ref
  -- Establish the correct variables for the given lookup direction.
  let (m, s) = if d == GetNew then (mn, sn) else (mo, so)
  -- Check if we have all the infos for the given TyCon loaded already.
  if tc `elementOfUniqSet` s
    -- Look the TyCon up, with a default fallback.
    then return (lookupWithDefaultUFM m tc tc)
    -- Otherwise, get the module of the type constructor if available.
    else case mbMdl of
      -- Check if the module is in the home or external package and load it
      -- from there.
      Just mdl | toUnitId (moduleUnit mdl) == homeUnitId_ flags,
                 not (isOneShot (ghcMode flags))
                  -> lookupTyConHome mdl m s tcs
               | otherwise -> lookupTyConExtern mdl m s tcs
      Nothing -> fail $ "TyCon without module: " ++ show (occNameString (occName n))
  where
    -- | Look up a type constructor replacement from a home package module.
    lookupTyConHome mdl m s tcs = do
      -- Get the module interface
      let miface = lookupIfaceByModule (hsc_HPT hsc) emptyPackageIfaceTable mdl
      -- Get the correct declaration to get the original name.
      case miface >>= (find declFinder . mi_decls) of
        Just (_, f) -- Look up the TyCon with the name and load it into our map.
          -> lookupType hsc (ifName f) >>= processResult m s tcs
        -- If no correct declaration was found, update our map to remember
        -- that no replacement exists.
        _ -> processResult m s tcs Nothing

    -- | Look up a type constructor replacement from an external package module.
    lookupTyConExtern mdl m s tcs
      | Just mdl' <- lookupSupportedBuiltInModule mdl = do
        let thisMdl = mkModuleName mdl'
        foundMdl <- findImportedModule hsc thisMdl Nothing >>= \case
           Found _ mdl'' -> return mdl''
           _             -> fail $ "Could not find module for built-in type of the imported module: " ++ mdl'
        result <- runIOEnv env (do
          orig <- lookupOrig foundMdl occ2
          liftIO $ lookupType (env_top env) orig) `catch` (\(SomeException _) -> return Nothing)
        case result of
          Just r  -> processResult m s tcs (Just r)
          Nothing -> fail $ "No lifted type available for: " ++ occNameString (occName n)
      | otherwise =  do
        -- Get the table of external packages.
        ext <- eps_PTE <$> readIORef (hsc_EPS hsc)
        -- Find the correct declaration and insert the result into our map.
        let result = fmap snd (find (tyThingFinder mdl occ2) (nonDetUFMToList ext))
        processResult m s tcs result

    -- | Checks if the given declaration uses the name we are looking for.
    declFinder (_, f) = occName (ifName f) == occ2

    -- | Check if the given TyCon uses the name we are looking for.
    tyThingFinder mdl occ (_, ATyCon tc') = occName n' == occ && nameModule_maybe n' == Just mdl
      where n' = tyConName tc'
    tyThingFinder _   _   _               = False

    -- | Insert a lookup result into the correct map on success.
    -- Regardless of success or not, update the set of TyCons that we have
    -- performed a lookup for.
    processResult m s (mn, mo, sn, so) (Just (ATyCon tc'))
      | GetNew <- d = do
        writeIORef ref (addToUFM m tc tc', mo, addOneToUniqSet s tc, so)
        return tc'
      | otherwise   = do
        writeIORef ref (mn, addToUFM m tc tc', sn, addOneToUniqSet s tc)
        return tc'
    processResult _ s (mn, mo, sn, so) _
      | GetNew <- d = do
        writeIORef ref (mn, mo, addOneToUniqSet s tc, so)
        return tc
      | otherwise   = do
        writeIORef ref (mn, mo, sn, addOneToUniqSet s tc)
        return tc

    hsc = env_top env
    mbMdl = nameModule_maybe n
    flags = hsc_dflags hsc
    n = tyConName tc
    occ2 = case d of
      GetNew -> addNameSuffix (occName n)
      GetOld -> removeNameSuffix (occName n)

-- | Update the type constructors in a type with a pure,
-- side-effect free replacement map.
replaceTyconTyPure :: UniqFM TyCon TyCon -> Type -> Type
replaceTyconTyPure tcs = replaceTyconTy'
  where
    replaceTyconTy' (ForAllTy b ty) =
      ForAllTy b (replaceTyconTy' ty)
    replaceTyconTy' (FunTy f m ty1 ty2) =
      FunTy f m (replaceTyconTy' ty1) (replaceTyconTy' ty2)
    replaceTyconTy' (CastTy ty kc) =
      CastTy (replaceTyconTy' ty) kc
    replaceTyconTy' (CoercionTy c) =
      CoercionTy c
    replaceTyconTy' (LitTy l) =
      LitTy l
    replaceTyconTy' (AppTy ty1 ty2) =
      AppTy (replaceTyconTy' ty1) (replaceTyconTy' ty2)
    replaceTyconTy' (TyConApp tc tys) =
      let tc' = case lookupUFM tcs tc of
            Just x -> x
            _ -> tc
       in TyConApp tc' (map replaceTyconTy' tys)
    replaceTyconTy' (TyVarTy v) = TyVarTy v

-- | Remove any outer application of 'Nondet', if available.
-- Can look through type synonyms.
bindingType :: Type -> Type
bindingType (coreView -> Just ty) = bindingType ty
bindingType (TyConApp _ [ty]) = ty
bindingType ty = ty

isMonoType :: Type -> Bool
isMonoType (ForAllTy _ _) = False
isMonoType _ = True

-- Get only the named binders of an invisible pi-type binder.
namedTyBinders :: [TyBinder] -> [TyVarBinder]
namedTyBinders = mapMaybe (\case Named b -> Just b; Anon _ _ -> Nothing)

-- | Instantiate a type with the given type arguments.
instantiateWith :: [Type] -> Type -> Type
instantiateWith apps ty =
  let (hd, rty) = splitInvisPiTys ty
      isNamed (Named _) = True
      isNamed _ = False
      (named, anon) = partition isNamed hd
      vs = map binderVar (namedTyBinders named)
      subst =
        foldr
          (\(v, a) s -> extendVarEnv s v a)
          emptyTvSubstEnv
          (zip vs apps)
      in_scope = mkInScopeSet (tyCoVarsOfTypes (ty : apps))
   in substTy (mkTCvSubst in_scope (subst, emptyCvSubstEnv)) (mkPiTys anon rty)

-- | Create a wrapper for the given type with the provided
-- type and evidence applications.
createWrapperFor :: Type -> [Type] -> [Var] -> HsWrapper
createWrapperFor ty apps evids =
  let (hd, _) = splitInvisPiTys ty
  in wrapperArg hd apps evids
  where
    wrapperArg (Named _ : xs) (a : as) evs =
      wrapperArg xs as evs <.> WpTyApp a
    wrapperArg (Anon _ _ : xs) tvs (e : es) =
      wrapperArg xs tvs es <.> WpEvApp (EvExpr (evId e))
    wrapperArg _ _ _ =
      WpHole

createWrapperLike :: Type -> [Var] -> [Var] -> HsWrapper
createWrapperLike (ForAllTy _ ty) (v : vs) es =
  WpTyLam v <.> createWrapperLike ty vs es
createWrapperLike (FunTy InvisArg _ _ ty) vs (e : es) =
  WpEvLam e <.> createWrapperLike ty vs es
createWrapperLike _ _ _ = WpHole

collectTyDictArgs :: HsWrapper -> ([TyVar], [EvVar])
collectTyDictArgs (WpCompose w1 w2) =
  let (t1, e1) = collectTyDictArgs w1
      (t2, e2) = collectTyDictArgs w2
   in (t1 ++ t2, e1 ++ e2)
collectTyDictArgs (WpTyLam v) = ([v], [])
collectTyDictArgs (WpEvLam v) = ([], [v])
collectTyDictArgs _ = ([], [])

-- | Tries to create a wrapper of evidence applications,
-- using an entry from the type-indexed list
-- if the type matches that of the wrapper.
-- Otherwise, use one from the other list.
mkEvWrapSimilar :: HsWrapper -> [CoreExpr] -> [(Type, Var)] -> HsWrapper
mkEvWrapSimilar = go []
  where
    go _ _ [] _ = WpHole
    go ws (WpTyApp _) (v : vs) [] =
      WpEvApp (EvExpr v) <.> gos ws vs []
    go ws (WpTyApp ty1) (v : vs) ((ty2, c) : cs)
      | ty1 `eqType` ty2 = WpEvApp (EvExpr (evId c)) <.> gos ws vs cs
      | otherwise = WpEvApp (EvExpr v) <.> gos ws vs ((ty2, c) : cs)
    go ws (WpCompose w1 w2) vs cs = go (w2 : ws) w1 vs cs
    go ws _ vs cs = gos ws vs cs

    gos [] _ _ = WpHole
    gos (w : ws) vs cs = go ws w vs cs

-- | Un-lift a given type. Returns the new type and True iff the type changed.
removeNondet :: Type -> TcM (Type, Bool)
removeNondet = removeNondet' . expandTypeSynonyms
  where
    removeNondet' (ForAllTy b ty) =
      first (ForAllTy b) <$> removeNondet' ty
    removeNondet' (FunTy f m ty1 ty2) = do
      (ty1', b1) <- removeNondet' ty1
      (ty2', b2) <- removeNondet' ty2
      return (FunTy f m ty1' ty2', b1 || b2)
    removeNondet' (CastTy ty kc) =
      first (`CastTy` kc) <$> removeNondet' ty
    removeNondet' (CoercionTy c) =
      return (CoercionTy c, False)
    removeNondet' (LitTy l) =
      return (LitTy l, False)
    removeNondet' (AppTy ty1 ty2) = do
      (ty1', b1) <- removeNondet' ty1
      (ty2', b2) <- removeNondet' ty2
      return (AppTy ty1' ty2', b1 || b2)
    removeNondet' (TyConApp tc [ty1, ty2]) = do
        ftc <- getFunTycon
        ([ty1', ty2'], bs) <- unzip <$> mapM removeNondet' [ty1, ty2]
        if tc == ftc
          then return (FunTy VisArg Many ty1' ty2', or bs)
          else return (TyConApp tc  [ty1', ty2'], or bs)
    removeNondet' (TyConApp tc [ty]) = do
        mtc <- getMonadTycon
        ftc <- getFunTycon
        if tc == mtc
          then removeNondet' ty
          else if tc == ftc
            then first (TyConApp funTyCon . (:[])) <$> removeNondet' ty
            else first (TyConApp tc       . (:[])) <$> removeNondet' ty
    removeNondet' (TyConApp tc args) = do
      (args', bs) <- unzip <$> mapM removeNondet' args
      return (TyConApp tc args', or bs)
    removeNondet' (TyVarTy v) =
      return (TyVarTy v, False)
