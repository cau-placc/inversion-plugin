{-# LANGUAGE TypeFamilies #-}
module Plugin.Trans.Coerce where

import GHC
import TcRnMonad
import Constraint
import GhcPlugins
import TcEvidence

import Plugin.Trans.CreateSyntax
import Plugin.Trans.Type
import Plugin.Trans.Var

-- Create function to resemble a coercion after lifting. Example:
-- newtype W = W Int
-- coerce @(Int -> Int -> Bool) @(W -> W -> Bool) ((==) @Int @Int)
-- > returnFunc $ \(f :: m (Int --> Int --> Bool)) ->
-- > returnFunc $ \(x :: m W) -> x >>= \(x' :: W) ->
-- > returnFunc $ \(y :: m W) -> y >>= \(y' :: W) ->
-- > (f `app` (coerce @W @(m Int) x') `app` (coerce @W @(m Int) y')
transCoerce :: TyConMap -> [Ct] -> Type -> Type -> TcM (LHsExpr GhcTc)
transCoerce tcs cts fromTy toTy = do
  -- classify all arguments and the result of the coercion into
  -- Phantom, Newtype or NoCoercion
  let (argsF, resF) = splitFunTys fromTy
      (argsT, resT) = splitFunTys toTy
      argClassifications = zipWith classifyCoercion argsF argsT
      resClassification = classifyCoercion resF resT
  -- lift the types for later
  fullResTy <- liftTypeTcM tcs toTy
  fullArgTy <- liftTypeTcM tcs fromTy

  -- create the variable for the function to be coerced
  v <- freshVar fullArgTy
  -- create the part for the remaining args and the function application
  e <- mkCoerceFunction fullResTy argClassifications resClassification v []

  -- create the lamda to bind the v
  let lam = mkLam (noLoc v) fullArgTy e fullResTy
  let lamty = mkVisFunTy fullArgTy fullResTy
  -- wrap everything in return . Func
  mkApp mkNewReturnFunTh lamty [lam]
  where
    -- Go through the list of arguments and collect the variables that will
    -- hold the corresponding argument
    mkCoerceFunction ty []         res v vs =
      -- no args left -> create fun application
      mkResultCoercion ty (reverse vs) v res
    mkCoerceFunction ty (arg:args) res v vs = do
      let resty = getCoercionResTy arg
      -- if newtype coercion is necessary, we will need to bind some stuff
      finalV <- (if isNewtypeClassification arg
                  then liftInnerTyTcM
                  else liftTypeTcM) tcs resty >>= freshVar
      ftc <- getFunTycon
      mtc <- getMonadTycon
      let (_, ty') = splitMyFunTy ftc mtc (bindingType ty)
      -- collect remaining args
      e <- mkCoerceFunction ty' args res v ((arg,finalV):vs)
      -- create the bind if necessary
      mkArgBindIfRequired ty' arg e finalV

    mkArgBindIfRequired resTy (NewtypeCoercion _ ty2) e v = do
      -- for a newtype coercion, create the bind and both lambdas
      ty2Lifted <- liftTypeTcM tcs ty2
      let ty2Inner = bindingType ty2Lifted
      -- the lambda after bind
      let bindLam = mkLam (noLoc v) ty2Inner e resTy
      arg1V <- freshVar ty2Lifted
      let varE = noLoc (HsVar noExtField (noLoc arg1V))
      -- actual bind
      bindE <- mkBind cts varE ty2Lifted bindLam resTy
      -- and the lambda for the arg
      mkArgLam resTy ty2Lifted arg1V bindE
    mkArgBindIfRequired fullResTy arg e v = do
      -- if not a newtype coercion, just create the lambda for the arg
      let ty2 = getCoercionResTy arg
      ty2Lifted <- liftTypeTcM tcs ty2
      mkArgLam fullResTy ty2Lifted v e


    mkArgLam resTy ty2Lifted argV e = do
      let funLam = mkLam (noLoc argV) ty2Lifted e resTy
      let funTy = mkVisFunTy ty2Lifted resTy
      mkApp mkNewReturnFunTh funTy [funLam]

    mkResultCoercion resTy args v (NewtypeCoercion ty1 ty2) = do
      -- if the result needs to be coerced via newtype, we need an additional
      -- return
      fullFunTy <- liftTypeTcM tcs fromTy
      ty1Lifted <- liftTypeTcM tcs ty1
      ty2Lifted <- liftInnerTyTcM tcs ty2
      res <- mkApplications args fullFunTy (noLoc (HsVar noExtField (noLoc v)))
      let wrap = WpCast (mkUnsafeCo Representational ty1Lifted ty2Lifted)
      let coerceRes = mkHsWrap wrap (unLoc res)
      mkApp mkNewReturnTh (bindingType resTy) [noLoc coerceRes]
    mkResultCoercion _     args v co = do
      -- if not a newtype coercion, we can just coerce the result if required
      fullFunTy <- liftTypeTcM tcs fromTy
      res <- mkApplications args fullFunTy (noLoc (HsVar noExtField (noLoc v)))
      mkCoerceIfRequired NoReverse co (unLoc res)


    mkApplications [] _ e = return e
    mkApplications ((coercion, v):rest) ty e = do
      ftc <- getFunTycon
      mtc <- getMonadTycon
      let (argty, ty') = splitMyFunTy ftc mtc (bindingType ty)
      let varE = HsVar noExtField (noLoc v)
      -- coerce the arg if required
      varECoerced <- mkCoerceIfRequired Reverse coercion varE
      -- and create the app to apply it to the function
      e' <- mkAppFL cts e ty varECoerced argty
      mkApplications rest ty' (noLoc (HsPar noExtField e'))

    mkCoerceIfRequired _         (NoCoercion _)            e =
      return (noLoc e)
    mkCoerceIfRequired Reverse   (PhantomCoercion ty1 ty2) e = do
      argty <- liftTypeTcM tcs ty1
      resty <- liftTypeTcM tcs ty2
      let coer = mkUnsafeCo Representational resty argty
      return $ noLoc $ mkHsWrap (WpCast coer) e
    mkCoerceIfRequired NoReverse (PhantomCoercion ty1 ty2) e = do
      argty <- liftTypeTcM tcs ty1
      resty <- liftTypeTcM tcs ty2
      let coer = mkUnsafeCo Representational argty resty
      return $ noLoc $ mkHsWrap (WpCast coer) e
    mkCoerceIfRequired Reverse   (NewtypeCoercion ty1 ty2) e = do
      argty <- liftTypeTcM    tcs ty1
      resty <- liftInnerTyTcM tcs ty2
      let coer = mkUnsafeCo Representational resty argty
      return $ noLoc $ mkHsWrap (WpCast coer) e
    mkCoerceIfRequired NoReverse (NewtypeCoercion ty1 ty2) e = do
      argty <- liftInnerTyTcM tcs ty1
      resty <- liftTypeTcM    tcs ty2
      let coer = mkUnsafeCo Representational argty resty
      return $ noLoc $ mkHsWrap (WpCast coer) e

-- newtype W = W Int
-- coerce @(Int -> Int -> Int) @(Int -> Int -> W)
-- > returnFunc $ \(f :: m (Int --> Int --> Int)) ->
-- > returnFunc $ \(x :: m Int) ->
-- > returnFunc $ \(y :: m Int) ->
-- > return (coerce @(m Int) @W (f `app` x' `app` y'))

data ReverseOrNot = Reverse | NoReverse
  deriving Eq

data CoercionClassification = NoCoercion Type
                            | PhantomCoercion Type Type
                            | NewtypeCoercion Type Type

isNewtypeClassification :: CoercionClassification -> Bool
isNewtypeClassification (NewtypeCoercion _ _) = True
isNewtypeClassification _                     = False

getCoercionResTy :: CoercionClassification -> Type
getCoercionResTy (NoCoercion        ty) = ty
getCoercionResTy (PhantomCoercion _ ty) = ty
getCoercionResTy (NewtypeCoercion _ ty) = ty

getCoercionArgTy :: CoercionClassification -> Type
getCoercionArgTy (NoCoercion      ty  ) = ty
getCoercionArgTy (PhantomCoercion ty _) = ty
getCoercionArgTy (NewtypeCoercion ty _) = ty

classifyCoercion :: Type -> Type -> CoercionClassification
classifyCoercion ty1 ty2 =
  case (splitTyConApp_maybe ty1, splitTyConApp_maybe ty2) of
    (Just (tc1, _), Just (tc2, _))
      | ty1 `eqType` ty2 -> NoCoercion ty1          -- equal      -> no coercion
      | tc1 == tc2       -> PhantomCoercion ty1 ty2 -- same tyCon -> a phantom
    _                    -> NewtypeCoercion ty1 ty2 -- otherwise  -> newtype
