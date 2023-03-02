{-# LANGUAGE OverloadedStrings #-}

{- |
 Module      : Plugin.Trans.Constr
 Description : Functions to handle lifting of value constructor declarations
 Copyright   : (c) Kai-Oliver Prott (2020)
 Maintainer  : kai.prott@hotmail.de

 This module contains a function to lift a data or newtype
 constructor declaration and
 functions to get the lifted constructors and record selectors from
 the type constructor map.
-}
module Plugin.Trans.Constr (
  liftConstr,
  liftRepName,
  getLiftedCon,
  getLiftedRecSel,
  RecordLiftingException (..),
) where

import Control.Exception
import Control.Monad
import Data.List
import GHC.Core.FamInstEnv
import GHC.Core.PatSyn
import GHC.Core.TyCo.Rep
import GHC.Plugins
import GHC.Types.Id.Make
import GHC.Types.SourceText
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var

-- | Exception type when lifting of a class fails.
data RecordLiftingException = RecordLiftingException
  { recordWithError :: Var
  , recordSelParent :: RecSelParent
  , errorReason :: String
  }
  deriving (Eq)

instance Show RecordLiftingException where
  show (RecordLiftingException v (RecSelData tycon) s) =
    "ClassLiftingException "
      ++ show (occNameString (occName v))
      ++ "(RecSelData "
      ++ show (occNameString (occName (tyConName tycon)))
      ++ ")"
      ++ show s
  show (RecordLiftingException v (RecSelPatSyn syn) s) =
    "ClassLiftingException "
      ++ show (occNameString (occName v))
      ++ "(RecSelData "
      ++ show (occNameString (occName (patSynName syn)))
      ++ ")"
      ++ show s

instance Exception RecordLiftingException

{- | Lift a value constructor definition.
 Note that this is part of a fixed-point computation, where the
 'UniqFM' in the fifth parameter and the
 'TyCon' in the seventh parameter depend on the output of the computation.
-}
liftConstr ::
  -- | True iff the type constructor defines a type class and should not be renamed
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
  -- | Lifted declaration type constructor
  TyCon ->
  -- | Supply of fresh unique keys
  UniqSupply ->
  -- | Constructor to be lifted
  DataCon ->
  -- | Lifted constructor
  IO DataCon
liftConstr isClass dflags instEnvs ftycon mvar mtycon tcs tcsM tycon s cn = do
  -- Create all required unique keys.
  let (s1, tmp1) = splitUniqSupply s
      (s2, tmp2) = splitUniqSupply tmp1
      (s3, tmp3) = splitUniqSupply tmp2
      (s4, tmp4) = splitUniqSupply tmp3
      (s5, s6) = splitUniqSupply tmp4
      ss = listSplitUniqSupply s4

  -- Lift all constructor arguments and update any type constructors.
  liftedargs <- liftIO (zipWithM liftAndReplaceType ss (dataConOrigArgTys cn))

  -- Create the new worker and constructor names, if required.
  let w = dataConWorkId cn
      origName1 = dataConName cn
      origName2 = varName w
      name1 = liftName origName1 (uniqFromSupply s1)
      name2 = liftName origName2 (uniqFromSupply s2)

  -- Lift any record fields.
  let us = uniqsFromSupply s3
  let fs = zipWith liftField (dataConFieldLabels cn) us

  -- Update the type constructor of the constructor result.
  let origResTy = dataConOrigResTy cn
  let (tcTy, args) = splitAppTys origResTy
  resty <- liftIO (replaceCon (mkAppTys tcTy (if isClass then args else mty : args)))

  let numVars = length (dataConUserTyVarBinders cn)
      srcBang = HsSrcBang NoSourceText NoSrcUnpack NoSrcStrict
      rep = case dataConWrapId_maybe cn of
        Nothing -> NoDataConRep
        Just wrap -> initUs_ s5 $ do
          uWrap <- getUniqueM
          let wrap' = liftName (varName wrap) uWrap
          let bangs = (if isClass then (++) (replicate numVars HsLazy) else id) $ dataConImplBangs cn
          mkDataConRep dflags instEnvs wrap' (Just bangs) dc
      -- Create the new constructor.
      dc =
        mkDataCon
          name1
          (dataConIsInfix cn)
          (maybe (tyConName $ promoteDataCon cn) (liftRepName s6) (tyConRepName_maybe tycon))
          (if isClass then replicate numVars srcBang ++ dataConSrcBangs cn else dataConSrcBangs cn)
          fs
          (if isClass then dataConUnivTyVars cn else mvar : dataConUnivTyVars cn)
          (dataConExTyCoVars cn)
          (if isClass then dataConUserTyVarBinders cn else Bndr mvar SpecifiedSpec : dataConUserTyVarBinders cn)
          (dataConEqSpec cn)
          (dataConTheta cn)
          liftedargs
          resty
          NoRRI
          tycon
          (dataConTag cn)
          (dataConStupidTheta cn)
          worker
          rep
      -- let the worker be created by GHC,
      -- so that the IdInfo (especially unfolding) remains correct
      worker = mkDataConWorkId name2 dc
  return dc
 where
  mty = if isClass then mkTyConTy mtycon else mkTyVarTy mvar
  liftAndReplaceType us (Scaled m ty) =
    Scaled
      <$> (replaceTyconTyPure tcs <$> replaceTyconTy tcsM m)
      <*> (replaceTyconTyPure tcs <$> liftType ftycon mty us tcsM ty)
  replaceCon = fmap (replaceTyconTyPure tcs) . replaceTyconTy tcsM

-- | Lift a record field by renaming its labels.
liftField :: FieldLabel -> Unique -> FieldLabel
liftField (FieldLabel str over sel selName) u = FieldLabel strND over sel selND
 where
  strND = str `appendFS` "ND"
  occND = mkOccNameFS (occNameSpace (occName selName)) strND
  selND = setNameUnique (tidyNameOcc selName occND) u

-- | Get a lifted value constructor from the given one and the TyCon map.
getLiftedCon :: DataCon -> TyConMap -> IO DataCon
getLiftedCon c tcs = do
  tc' <- lookupTyConMap GetNew tcs tc
  case midx of
    Just y -> return (tyConDataCons tc' !! y)
    _ -> return c
 where
  tc = dataConTyCon c
  midx = findIndex ((== dataConName c) . dataConName) (tyConDataCons tc)

-- | Get a lifted recrd selector from the given one and the TyCon map.
getLiftedRecSel ::
  -- | '-->' type constructor
  TyCon ->
  -- | 'Nondet' type
  Type ->
  -- | Fresh supply of unique keys
  UniqSupply ->
  -- | Map of imported old TyCon's to lifted ones
  TyConMap ->
  -- | Origin of the record selector
  RecSelParent ->
  -- | Record selector to be lifted
  Var ->
  -- | Lifted record selector
  IO Var
getLiftedRecSel ftc mty us tcs (RecSelData origTc) v = do
  -- look up the lifted type constructor.
  tc' <- lookupTyConMap GetNew tcs origTc
  -- Get the index of the record selector in its original definition.
  case midx of
    Just y -> do
      -- Check if it is a newtype record.
      let normalNewty = isNewTyCon origTc && not (isClassTyCon origTc)
      -- Lift it accordingly. Note that we only want to lift the result type
      -- of the selector. It should still be a unary function.
      ty <-
        if normalNewty
          then replaceTyconTy tcs (varType v)
          else liftResultTy ftc mty us tcs (varType v)
      -- Use the index to find its new name in the new definition
      let nm = flSelector (tyConFieldLabels tc' !! y)
      return
        ( setIdDetails
            ( setVarName
                ( setVarType
                    ( setVarUnique
                        v
                        (nameUnique nm)
                    )
                    ty
                )
                nm
            )
            (RecSelId (RecSelData tc') False)
        )
    Nothing -> return v
 where
  midx = findIndex ((== varName v) . flSelector) (tyConFieldLabels origTc)
getLiftedRecSel _ _ _ _ p@(RecSelPatSyn _) v =
  throw (RecordLiftingException v p reason)
 where
  reason = "Pattern synonyms are not supported by the plugin yet"

liftRepName :: UniqSupply -> TyConRepName -> TyConRepName
liftRepName u n
  | Just mdl <- nameModule_maybe n = mkExternalName (uniqFromSupply u) mdl (mkOccName (occNameSpace (occName n)) (occNameString (occName n) ++ "FL" ++ show (uniqFromSupply u))) noSrcSpan
  | otherwise = panicAnyUnsafe "no module in repName" n
