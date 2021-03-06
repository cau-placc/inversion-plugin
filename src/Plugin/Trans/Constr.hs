{-# LANGUAGE OverloadedStrings #-}
{-|
Module      : Plugin.Trans.Constr
Description : Functions to handle lifting of value constructor declarations
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a function to lift a data or newtype
constructor declaration and
functions to get the lifted constructors and record selectors from
the type constructor map.
-}
module Plugin.Trans.Constr
  ( liftConstr, getLiftedCon, getLiftedRecSel, RecordLiftingException(..)
  ) where

import Data.List
import Control.Monad
import Control.Exception

import GhcPlugins
import UniqMap
import MkId
import PatSyn
import FamInst

import Plugin.Trans.Type
import Plugin.Trans.Var
import Plugin.Trans.Util

-- | Exception type when lifting of a class fails.
data RecordLiftingException = RecordLiftingException
    { recordWithError :: Var
    , recordSelParent :: RecSelParent
    , errorReason :: String
    }
  deriving (Eq)

instance Show RecordLiftingException where
  show (RecordLiftingException v (RecSelData tycon) s) =
    "ClassLiftingException " ++
    show (occNameString (occName v)) ++
    "(RecSelData " ++ show (occNameString (occName (tyConName tycon))) ++ ")" ++
    show s
  show (RecordLiftingException v (RecSelPatSyn syn) s) =
    "ClassLiftingException " ++
    show (occNameString (occName v)) ++
    "(RecSelData " ++ show (occNameString (occName (patSynName syn))) ++ ")" ++
    show s

instance Exception RecordLiftingException

-- | Lift a value constructor definition.
-- Note that this is part of a fixed-point computation, where the
-- 'UniqMap' in the fifth parameter and the
-- 'TyCon' in the seventh parameter depend on the output of the computation.
liftConstr :: Bool                -- ^ True iff the type constructor should not be renamed
           -> DynFlags            -- ^ Compiler flags
           -> FamInstEnvs         -- ^ Family Instance Environments, both home and external
           -> TyCon               -- ^ 'Fun' type constructor
           -> TyCon               -- ^ 'Nondet' type constructor
           -> UniqMap TyCon TyCon -- ^ Map of old TyCon's from this module to lifted ones
           -> TyConMap            -- ^ Map of imported old TyCon's to lifted ones
           -> TyCon               -- ^ Lifted declaration type constructor
           -> UniqSupply          -- ^ Supply of fresh unique keys
           -> DataCon             -- ^ Constructor to be lifted
           -> IO DataCon          -- ^ Lifted constructor
liftConstr noRename dflags instEnvs ftycon mtycon tcs tcsM tycon s cn = do

  -- Create all required unique keys.
  let (s1, tmp1) = splitUniqSupply s
      (s2, tmp2) = splitUniqSupply tmp1
      (s3, tmp3) = splitUniqSupply tmp2
      (s4, s5  ) = splitUniqSupply tmp3
      ss = listSplitUniqSupply s4

  -- Lift all constructor arguments and update any type constructors.
  argtys <- liftIO (zipWithM liftAndReplaceType ss (dataConOrigArgTys cn))

  -- Create the new worker and constructor names, if required.
  let w        = dataConWorkId cn
      origName1 = dataConName cn
      origName2 = varName w
      (name1, name2) = if noRename
        then (origName1, origName2)
        else (liftName origName1 (uniqFromSupply s1),
              liftName origName2 (uniqFromSupply s2))

  -- Lift any record fields.
  let us = uniqsFromSupply s3
  let fs = zipWith liftField (dataConFieldLabels cn) us

  -- Update the type constructor of the constructor result.
  resty <- liftIO (replaceCon (dataConOrigResTy cn))

  -- Create the new constructor.
  let rep = case dataConWrapId_maybe cn of
              Nothing   -> NoDataConRep
              Just wrap -> initUs_ s5 $ do
                uWrap <- getUniqueM
                let wrap' = if noRename then varName wrap else
                              liftName (varName wrap) uWrap
                let bangs = dataConImplBangs cn
                mkDataConRep dflags instEnvs wrap' (Just bangs) dc
      -- Create the new constructor.
      dc = mkDataCon
        name1 (dataConIsInfix cn) (tyConName $ promoteDataCon cn)
        (dataConSrcBangs cn) fs (dataConUnivTyVars cn)
        (dataConExTyCoVars cn) (dataConUserTyVarBinders cn) (dataConEqSpec cn)
        (dataConTheta cn) argtys resty NoRRI tycon
        (dataConTag cn) (dataConStupidTheta cn) worker rep
      -- let the worker be created by GHC,
      -- so that the IdInfo (especially unfolding) remains correct
      worker = mkDataConWorkId name2 dc
  return dc
  where
    mty = mkTyConTy mtycon
    -- Use the inner type lifting for constructors from newtype declarations,
    -- because we otherwise get a 'Nondet' too much if we coerce its type.
    liftAndReplaceType us = fmap (replaceTyconTyPure tcs)
                          . liftType ftycon mty us tcsM
    replaceCon = fmap (replaceTyconTyPure tcs) . replaceTyconTy tcsM

-- | Lift a record field by renaming its labels.
liftField :: FieldLabel -> Unique -> FieldLabel
liftField (FieldLabel _ over sel) u = FieldLabel strND over selND
  where
    strND = occNameFS occND
    occ   = occName sel
    occND = mkOccName (occNameSpace occ) (occNameString occ ++ "$FLsel")
    selND = setNameUnique (tidyNameOcc sel occND) u

-- | Get a lifted value constructor from the given one and the TyCon map.
getLiftedCon :: DataCon -> TyConMap -> IO DataCon
getLiftedCon c tcs = do
  tc' <- lookupTyConMap GetNew tcs tc
  case midx of
    Just y -> return (tyConDataCons tc' !! y)
    _      -> return c
  where
    tc = dataConTyCon c
    midx = findIndex ((==dataConName c) . dataConName) (tyConDataCons tc)

-- | Get a lifted recrd selector from the given one and the TyCon map.
getLiftedRecSel :: TyCon        -- ^ 'Fun' type constructor
                -> Type         -- ^ 'Nondet' type
                -> UniqSupply   -- ^ Fresh supply of unique keys
                -> TyConMap     -- ^ Map of imported old TyCon's to lifted ones
                -> RecSelParent -- ^ Origin of the record selector
                -> Var          -- ^ Record selector to be lifted
                -> IO Var       -- ^ Lifted record selector
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
      ty <- if normalNewty
        then replaceTyconTy tcs (varType v)
        else liftResultTy ftc mty us tcs (varType v)
      -- Use the index to find its new name in the new definition
      let nm = flSelector (tyConFieldLabels tc' !! y)
      return (setIdDetails (setVarName (setVarType (setVarUnique v
        (nameUnique nm)) ty) nm) (RecSelId (RecSelData tc') False))
    Nothing -> panicAnyUnsafe "getLiftedRecSel: not found" v
  where
    midx = findIndex ((==unliftedNM) . occName . flSelector) (tyConFieldLabels origTc)
    occ = occName v
    str = occNameString occ
    unliftedStr = if specialSuff `isSuffixOf` str
                    then take (length str - length specialSuff) str
                    else str
    specialSuff = "$FLsel" :: String
    unliftedNM = mkOccName (occNameSpace occ) unliftedStr
getLiftedRecSel _ _ _ _ p@(RecSelPatSyn _) v =
  throw (RecordLiftingException v p reason)
    where
      reason = "Pattern synonyms are not supported by the plugin yet"
