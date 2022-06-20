{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}

-- |
-- Module      : Plugin.Trans.Record
-- Description : Module to lift record selectors
-- Copyright   : (c) Kai-Oliver Prott (2020)
-- Maintainer  : kai.prott@hotmail.de
--
-- This module contains the function to lift the record selector function
-- that is introduced for each record label.
module Plugin.Trans.Record (liftRecordSel, mkRecSelFun) where

import Data.Generics.Aliases
import Data.Generics.Schemes
import Data.Tuple
import GHC.Data.Bag
import GHC.Hs.Binds
import GHC.Hs.Expr
import GHC.Hs.Extension
import GHC.Parser.Annotation
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Utils.Monad
import GHC.Types.TypeEnv
import GHC.Types.Fixity
import GHC.Tc.Types.Evidence
import Language.Haskell.Syntax.Extension

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
liftRecordSel ::
  TyConMap ->
  HsBindLR GhcTc GhcTc ->
  TcM (Maybe (HsBindLR GhcTc GhcTc))
liftRecordSel tcs (AbsBinds _ tvs evs ex evb bs sig)
  | [L l (FunBind wrap _ mg ticks)] <- bagToList bs,
    [ABE _ p m w s] <- ex = do
      u <- getUniqueM
      stc <- getShareClassTycon
      ftc <- getFunTycon
      us1 <- getUniqueSupplyM
      us2 <- getUniqueSupplyM

      let parent = case idDetails p of
            RecSelId parTc _ -> parTc
            _ ->
              panicBndrUnsafe
                "Expected RecSel in record selector definition"
                p

      -- Look up how the lifted record selector should look.
      mty <- mkTyConTy <$> getMonadTycon
      p' <- liftIO (getLiftedRecSel stc ftc mty us1 tcs parent p)
      -- Lift its type.
      m' <-
        setVarType
          ( setVarUnique
              ( setVarName m (setNameUnique (varName m) u)
              )
              u
          )
          <$> liftIO (liftResultTy stc ftc mty us2 tcs (varType m))
      -- Lift its implementation.
      mg' <- liftRecSelMG tcs m' mg

      -- Create the correct export entries and stuff.
      let selB = listToBag [L l (FunBind wrap (noLocA m') mg' ticks)]
      let ex' = ABE noExtField p' m' w s
      let b' = AbsBinds noExtField tvs evs [ex'] evb selB sig

      -- Update its type in the environment
      tenv_var <- tcg_type_env_var <$> getGblEnv
      tenv <- readTcRef tenv_var
      writeTcRef tenv_var (extendTypeEnvWithIds tenv [p'])

      return (Just b')
liftRecordSel _ _ = return Nothing

-- | Lift the MatchGroup of a record selector.
liftRecSelMG ::
  TyConMap ->
  Var ->
  MatchGroup GhcTc (LHsExpr GhcTc) ->
  TcM (MatchGroup GhcTc (LHsExpr GhcTc))
liftRecSelMG tcs f (MG (MatchGroupTc args res) (L _ alts) orig) =
  do
    args' <- liftIO (mapM (replaceTyconScaled tcs) args)
    -- Lift the result type of this match group accordingly.
    res' <- liftTypeTcM tcs res
    alts' <- mapM (liftRecSelAlt tcs f) alts
    return (MG (MatchGroupTc args' res') (noLocA alts') orig)

-- | Lift an alternative of a record selector.
liftRecSelAlt ::
  TyConMap ->
  Var ->
  LMatch GhcTc (LHsExpr GhcTc) ->
  TcM (LMatch GhcTc (LHsExpr GhcTc))
liftRecSelAlt tcs f (L _ (Match _ (FunRhs _ fixity strict) [pat] rhs)) = do
  -- Lift any left-side pattern.
  (pat', vs') <- liftPattern tcs pat
  let vs = map (\(a, L _ b) -> (a, b)) vs'
  let ctxt = FunRhs (noLocA (varName f)) fixity strict :: HsMatchContext GhcRn
  -- Replace any variables on the right side.
  -- Thankfully, a record selector is always just a single variable on the rhs.
  rhs' <-
    everywhere (mkT (replaceVarExpr (map swap vs)))
      <$> everywhereM (mkM (liftErrorWrapper tcs)) rhs
  return (noLocA (Match EpAnnNotUsed ctxt [pat'] rhs'))
liftRecSelAlt _ _ x = return x

-- | Substitute variables in the given expression.
replaceVarExpr :: [(Var, Var)] -> HsExpr GhcTc -> HsExpr GhcTc
replaceVarExpr vs (HsVar _ (L l v))
  | Just v' <- lookup v vs = HsVar noExtField (L l v')
replaceVarExpr _ e = e

mkRecSelFun :: TyConMap -> Var -> TcM (LHsBind GhcTc)
mkRecSelFun tcs v = do
  ftc <- getFunTycon
  stc <- getShareClassTycon
  mtc <- getMonadTycon
  let mty = mkTyConTy mtc
  us <- getUniqueSupplyM

  th <- liftQ [| \sel -> returnFLF $ \record -> record >>= sel |]

  let (pis, ty) = splitForAllTyCoVars (varType v)
  let (_, unliftedArg, unliftedRes) = splitFunTy ty
  Just (oldTc, _) <- return $ splitTyConApp_maybe unliftedArg
  v' <- liftIO (getLiftedRecSel stc ftc mty us tcs (RecSelData oldTc) v)
  arg <- liftInnerTyTcM tcs unliftedArg
  res <- liftTypeTcM tcs unliftedRes


  let monotype = mkTyConApp mtc [mkTyConApp ftc [arg, bindingType res]]
  let polytype = mkForAllTys (map (`Bndr` Inferred) pis) monotype

  let w = foldr ((<.>) . toWrap) WpHole pis
  let wrappedV = XExpr (WrapExpr (HsWrap w (HsVar noExtField (noLocA v'))))

  let thtype = (arg `mkVisFunTyMany` res) `mkVisFunTyMany` monotype
  e <- mkApp (mkNewAny th) thtype [noLocA wrappedV]

  u1 <- getUniqueM
  u2 <- getUniqueM
  let str = occNameString (occName v)
  let unliftedStr = take (length str - length "$FLsel") str
  let occ = addNameSuffix $ mkOccName (occNameSpace (occName v)) unliftedStr
  mdl <- tcg_mod <$> getGblEnv
  let name = mkExternalName (varUnique v) mdl occ noSrcSpan
  let preparedId = setIdDetails (setVarName v name) VanillaId
  let monoV = mkLocalVar VanillaId (mkClonedInternalName u1 name) Many monotype vanillaIdInfo
  let polyV = setVarType (setVarName preparedId (setNameUnique name u2)) polytype

  let bdy = GRHS EpAnnNotUsed [] e
  let rhs = GRHSs emptyComments [noLoc bdy] (EmptyLocalBinds noExtField)
  let ctxt = FunRhs (noLocA (varName monoV)) Prefix NoSrcStrict
  let clause = Match EpAnnNotUsed ctxt [] rhs
  let mg = MG (MatchGroupTc [] monotype) (noLocA [noLocA clause]) Generated
  let fb = FunBind WpHole (noLocA monoV) mg []
  let export = ABE noExtField polyV monoV WpHole (SpecPrags [])
  let absB = AbsBinds noExtField pis [] [export] [] (unitBag (noLocA fb)) False

  tenv <- getGblEnv >>= readTcRef . tcg_type_env_var
  let tenv' = plusTypeEnv tenv (typeEnvFromEntities [polyV] [] [] [])
  getGblEnv >>= \gbl -> writeTcRef (tcg_type_env_var gbl) tenv'
  return (noLocA absB)
  where
    toWrap tyvar = WpTyApp (mkTyVarTy tyvar)
