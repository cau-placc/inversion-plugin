{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE TypeOperators   #-}
{-|
Module      : Plugin.Trans.CreateSyntax
Description : Helper functions to create parts of GHC's AST
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a lot of different helper functions to create
syntactic constructs for GHC's abstract syntax tree.
-}
module Plugin.Trans.CreateSyntax where

import Control.Monad

import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Pat
import GHC.Hs.Utils
import GHC.Hs.Expr
import TcRnMonad
import TcHsSyn
import TysWiredIn
import TyCoRep
import SrcLoc
import ConLike
import GhcPlugins
import TcEvidence
import TcSimplify
import Constraint
import Bag

import Plugin.Effect.Monad ( type (-->)(..), appFL, unFL, to, toFL, Convertible, FL )
import Plugin.Lifted --TODO: necessary?
import Plugin.Trans.Constr
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var

-- | Create the lambda functions used to lift value constructors.
-- Look at their lifting for details.
mkConLam :: Maybe HsWrapper -> DataCon -> [Type] -> [Id]
     -> TcM (LHsExpr GhcTc, Type)
-- list of types is empty -> apply the collected variables.
mkConLam mw c [] vs = do
    mtycon <- getMonadTycon
    -- Use the given wrapper for the constructor.
    let wrap = case mw of
          Just w  -> HsWrap noExtField (w <.> WpTyApp (mkTyConTy mtycon))
          Nothing -> HsWrap noExtField (WpTyApp (mkTyConTy mtycon))
    -- Apply all variables in reverse to the constructor.
    let e = foldl ((noLoc .) . HsApp noExtField)
            (noLoc (wrap (HsConLikeOut noExtField (RealDataCon c))))
            (map (noLoc . HsVar noExtField . noLoc) $ reverse vs)
    -- Get the result type of the constructor.
    ty <- snd . splitFunTys <$> getTypeOrPanic e
    -- Wrap the whole term in a 'return'.
    e' <- mkApp mkNewReturnTh ty [noLoc $ HsPar noExtField e]
    mty <- mkTyConTy <$> getMonadTycon
    return (e', mkAppTy mty ty)
-- Create lambdas for the remaining types.
mkConLam w c (ty:tys) vs = do
  mtc <- getMonadTycon
  -- Create the new variable for the lambda.
  v <- freshVar ty
  -- Create the inner part of the term with the remaining type arguments.
  (e, resty) <- mkConLam w c tys (v:vs)
  -- Make the lambda for this variable
  let e' = mkLam (noLoc v) ty e resty
  let lamty = mkVisFunTy ty resty
  ftc <- getFunTycon
  let lamty2 = mkTyConApp ftc [bindingType ty, bindingType resty]
  -- Wrap the whole term in a 'return'.
  e'' <- mkApp mkNewReturnFunTh lamty [noLoc $ HsPar noExtField e']
  let mty = mkTyConTy mtc
  return (e'', mkAppTy mty lamty2)

-- | Create a '(>>=)' for the given arguments and apply them.
mkBind :: [Ct] -> LHsExpr GhcTc -> Type -> LHsExpr GhcTc -> Type
       -> TcM (LHsExpr GhcTc)
mkBind given scr ty1 arg ty2 = do
  let ty1' = bindingType ty1
  let ty2' = bindingType ty2
  mkAppWith (mkNewBindTh ty1') given ty2' [scr, arg]

-- | Create a '(>>=)' for the given arguments and apply them.
mkAppFL :: [Ct] -> LHsExpr GhcTc -> Type -> LHsExpr GhcTc -> Type
       -> TcM (LHsExpr GhcTc)
mkAppFL given op ty1 arg ty2 = do
  let ty1' = bindingType ty1
  let ty2' = bindingType ty2
  mkAppWith (mkNewAppTh ty1') given ty2' [op, arg]

-- | Apply the given list of arguments to a term created by the first function.
mkApp :: (Type -> TcM (LHsExpr GhcTc))
      -> Type -> [LHsExpr GhcTc]
      -> TcM (LHsExpr GhcTc)
mkApp = flip mkAppWith []

-- | Apply the given list of arguments to a term created by the first function.
-- Use the given set of given constraints to solve any wanted constraints.
mkAppWith :: (Type -> TcM (LHsExpr GhcTc))
          -> [Ct] -> Type -> [LHsExpr GhcTc]
          -> TcM (LHsExpr GhcTc)
mkAppWith con cts typ args = do
  (e', WC wanted impls) <- captureConstraints (con typ)
  let constraints = WC (unionBags wanted (listToBag cts)) impls
  wrapper <- mkWpLet . EvBinds <$> simplifyTop constraints
  zonkTopLExpr (foldl mkHsApp (mkLHsWrap wrapper e') args)

-- | Create a 'return' for the given argument types.
mkNewReturnTh :: Type -> TcM (LHsExpr GhcTc)
mkNewReturnTh etype = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| return |]
  let mty = mkTyConTy mtycon
  let expType = mkVisFunTy etype $ -- 'e ->
                mkAppTy mty etype  -- m 'e
  mkNewAny th_expr expType

-- | Create a 'return . Fun' for the given argument types.
mkNewReturnFunTh :: Type -> TcM (LHsExpr GhcTc)
mkNewReturnFunTh etype = do
  ftc <- getFunTycon
  mtycon <- getMonadTycon
  th_expr <- liftQ [| return . Func |]
  let mty = mkTyConTy mtycon
  let (arg, res) = splitFunTy etype
  let eLifted = mkTyConApp ftc [mty, bindingType arg, bindingType res]
  let expType = mkVisFunTy etype $ -- 'e ->
                mkAppTy mty eLifted  -- m 'e
  mkNewAny th_expr expType

-- | Create a '(>>=)' for the given argument types.
mkNewBindTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewBindTh etype btype = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| (>>=) |]
  let mty = mkTyConTy mtycon
  let resty = mkAppTy mty btype
  let expType = mkVisFunTy (mkAppTy mty etype) $    -- m 'e ->
                mkVisFunTy (mkVisFunTy etype resty) -- (e' -> m b) ->
                  resty
  mkNewAny th_expr expType

-- | Create a 'appFL' for the given argument types.
mkNewAppTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewAppTh optype argtype = do
  mtycon <- getMonadTycon
  ftycon <- getFunTycon
  let (_, restype) = splitMyFunTy ftycon mtycon optype
  th_expr <- liftQ [| appFL |]
  let mty = mkTyConTy mtycon
  let expType = mkVisFunTy (mkAppTy mty optype) $ -- m optype ->
                mkVisFunTy (mkAppTy mty argtype)  -- m argtype ->
                restype                           -- restype
  mkNewAny th_expr expType

-- | Create a 'fmap' for the given argument types.
mkNewFmapTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewFmapTh etype btype = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| fmap |]
  let appMty = mkTyConApp mtycon . (:[])
  let expType = mkVisFunTy (mkVisFunTy etype btype) $     -- ('e -> 'b) ->
                mkVisFunTy (appMty etype) (appMty btype)  -- m 'e -> m 'b
  mkNewAny th_expr expType

-- | Create a 'liftE' for the given argument types.
mkNewLiftETh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewLiftETh ty1 ty2 = do
  mty <- (. (: [])) . mkTyConApp <$> getMonadTycon
  th_expr <- liftQ [| (\px -> FL $ fmap to <$> unFL px) :: Convertible a => FL a -> FL (Lifted a) |]
  let expType = mkVisFunTy (mty ty1) (mty ty2) -- m a -> m b
  mkNewAny th_expr expType

mkNewToFL ::  Type -> Type -> TcM (LHsExpr GhcTc)
mkNewToFL ty1 ty2 = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| toFL |]
  let expType = mkVisFunTy ty1 (mkTyConApp mtycon [ty2])
  mkNewAny th_expr expType

-- | Create a 'apply1' for the given argument types.
mkNewApply1 :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply1 ty1 ty2 = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| appFL |]
  let expType =
        mkVisFunTy (mkTyConApp mtycon                     -- Nondet
                  [mkVisFunTy (mkTyConApp mtycon [ty1])   --  ( Nondet a ->
                           (mkTyConApp mtycon [ty2])])    --    Nondet b ) ->
          (mkVisFunTy (mkTyConApp mtycon [ty1])           -- Nondet a ->
                   (mkTyConApp mtycon [ty2]))             -- Nondet b
  mkNewAny th_expr expType

-- | Create a 'apply2' for the given argument types.
mkNewApply2 :: Type -> Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply2 ty1 ty2 ty3 = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| \f a b -> f `appFL` a `appFL` b |]
  let expType =
        mkTyConApp mtycon                                    -- Nondet
                  [mkVisFunTy (mkTyConApp mtycon [ty1])      --  (Nondet a ->
                    (mkTyConApp mtycon                       --   Nondet
                       [mkVisFunTy (mkTyConApp mtycon [ty2]) --     (Nondet b ->
                         (mkTyConApp mtycon [ty3])])]        --      Nondet c )
        `mkVisFunTy`                                         --  ) ->
        mkVisFunTy (mkTyConApp mtycon [ty1])                 -- Nondet a ->
          (mkVisFunTy (mkTyConApp mtycon [ty2])              -- Nondet b ->
                   (mkTyConApp mtycon [ty3]))                -- Nondet c
  mkNewAny th_expr expType

-- | Create a 'apply2Unlifted' for the given argument types.
mkNewApply2Unlifted :: Type -> Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply2Unlifted ty1 ty2 ty3 = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| \f a b -> f `appFL` a `appFL` return b |]
  let expType =
        mkTyConApp mtycon                                    -- Nondet
                  [mkVisFunTy (mkTyConApp mtycon [ty1])      --  ( Nondet a ->
                    (mkTyConApp mtycon                       --    Nondet
                       [mkVisFunTy (mkTyConApp mtycon [ty2]) --      ( Nondet b ->
                         (mkTyConApp mtycon [ty3])])]        --        Nondet c )
        `mkVisFunTy`                                         --  ) ->
        mkVisFunTy (mkTyConApp mtycon [ty1])                 -- Nondet a ->
          (mkVisFunTy ty2                                    --        b ->
                   (mkTyConApp mtycon [ty3]))                -- Nondet c
  mkNewAny th_expr expType

-- | Create a '(>>=)' specialized to lists for list comprehensions.
mkListBind :: Type -> Type -> TcM (SyntaxExpr GhcTc)
mkListBind a b = do
  e <- mkApp mk b []
  return (SyntaxExpr (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| (>>=) |]
      let expType = mkTyConApp listTyCon [a]
                    `mkVisFunTy`
                    ((a `mkVisFunTy` mkTyConApp listTyCon [b])
                      `mkVisFunTy`
                      mkTyConApp listTyCon [b])
      mkNewAny th_expr expType

-- | Create a 'return' specialized to lists for list comprehensions.
mkListReturn :: Type -> TcM (SyntaxExpr GhcTc)
mkListReturn a = do
  e <- mkApp mk a []
  return (SyntaxExpr (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| return |]
      let expType = a `mkVisFunTy` mkTyConApp listTyCon [a]
      mkNewAny th_expr expType

-- | Create a 'fail' specialized to lists for list comprehensions.
mkListFail :: Type -> TcM (SyntaxExpr GhcTc)
mkListFail a = do
  e <- mkApp mk a []
  return (SyntaxExpr (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| fail |]
      let expType = stringTy `mkVisFunTy` mkTyConApp listTyCon [a]
      mkNewAny th_expr expType

-- | Create a 'guard' specialized to lists for list comprehensions.
mkListGuard :: TcM (SyntaxExpr GhcTc)
mkListGuard = do
  e <- mkApp mk unitTy []
  return (SyntaxExpr (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| guard |]
      let expType = boolTy `mkVisFunTy` mkTyConApp listTyCon [unitTy]
      mkNewAny th_expr expType

-- | Create a '(>>)' specialized to lists for list comprehensions.
mkListSeq :: Type -> Type -> TcM (SyntaxExpr GhcTc)
mkListSeq a b = do
  e <- mkApp mk b []
  return (SyntaxExpr (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| (>>) |]
      let expType = mkTyConApp listTyCon [a]
                    `mkVisFunTy`
                    (mkTyConApp listTyCon [b]
                      `mkVisFunTy`
                      mkTyConApp listTyCon [b])
      mkNewAny th_expr expType

-- | Create a lifted empty list constructor.
mkEmptyList :: Type -> TyConMap -> TcM (LHsExpr GhcTc)
mkEmptyList ty tcs = do
  dc <- liftIO (getLiftedCon nilDataCon tcs)
  mtycon <- getMonadTycon
  return (noLoc (HsWrap noExtField (WpTyApp ty <.> WpTyApp (mkTyConTy mtycon))
    (HsConLikeOut noExtField (RealDataCon dc))))

-- | Create a lifted cons list constructor.
mkConsList :: Type -> TyConMap -> TcM (LHsExpr GhcTc)
mkConsList ty tcs = do
  dc <- liftIO (getLiftedCon consDataCon tcs)
  mtycon <- getMonadTycon
  return (noLoc (HsWrap noExtField (WpTyApp ty <.> WpTyApp (mkTyConTy mtycon))
    (HsConLikeOut noExtField (RealDataCon dc))))

-- | Create a general lambda that binds one variable on its left side.
mkLam :: Located Id -> Type -> LHsExpr GhcTc -> Type -> LHsExpr GhcTc
mkLam v ty' bdy resty =
  let pat = VarPat noExtField v
      grhs = GRHS noExtField ([] :: [GuardLStmt GhcTc]) bdy
      rhs = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
      match = Match noExtField LambdaExpr [noLoc pat] rhs
      mgtc = MatchGroupTc [ty'] resty
      mg = MG mgtc (noLoc [noLoc match]) Generated
  in noLoc $ HsPar noExtField $ noLoc $ HsLam noExtField mg

-- | Create a simple let expression that binds the given variable to
-- the first LHsExpr, where the other LHsExpr is used for the "in" of the let.
mkSimpleLet :: RecFlag -> LHsExpr GhcTc -> LHsExpr GhcTc -> Var -> Type
            -> HsExpr GhcTc
mkSimpleLet f scr e v a =
  let grhs = GRHS noExtField [] scr
      grhss = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
      ctxt = FunRhs (noLoc (varName v)) Prefix NoSrcStrict
      alt = Match noExtField ctxt [] grhss
      mgtc = MatchGroupTc [] a
      mg = MG mgtc (noLoc [noLoc alt]) Generated
      b = FunBind emptyUniqSet (noLoc v) mg WpHole []
      nbs = NValBinds [(f, listToBag [noLoc b])] []
      bs = HsValBinds noExtField (XValBindsLR nbs)
  in HsLet noExtField (noLoc bs) e

-- | Create a simple let expression that binds the given pattern to
-- the first LHsExpr, where the other LHsExpr is used for the "in" of the let.
mkSimplePatLet :: Type -> LHsExpr GhcTc -> LPat GhcTc -> LHsExpr GhcTc
               -> HsExpr GhcTc
mkSimplePatLet ty scr p e =
  let grhs = GRHS noExtField [] scr
      grhss = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
      b = PatBind (NPatBindTc emptyNameSet ty) p grhss ([], [[]])
      nbs = NValBinds [(Recursive, listToBag [noLoc b])] []
      bs = HsValBinds noExtField (XValBindsLR nbs)
  in HsLet noExtField (noLoc bs) e

-- | Create a simple (case) alternative with the given right side and patterns.
mkSimpleAlt :: HsMatchContext Name -> LHsExpr GhcTc -> [LPat GhcTc]
            -> Match GhcTc (LHsExpr GhcTc)
mkSimpleAlt ctxt e ps =
  let grhs = GRHS noExtField [] e
      grhss = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
  in Match noExtField ctxt ps grhss

-- | Create a variable pattern with the given parameter.
mkVarPat :: Var -> LPat GhcTc
mkVarPat v = noLoc (VarPat noExtField (noLoc v))

-- | Creates a let statement for the given binding.
toLetStmt :: (RecFlag, LHsBinds GhcTc) -> ExprLStmt GhcTc
toLetStmt b = noLoc
  (LetStmt noExtField (noLoc
    (HsValBinds noExtField (XValBindsLR (NValBinds [b] [])))))

-- | Create a let with the given binding and inner expression.
toLetExpr :: (RecFlag, LHsBinds GhcTc) -> LHsExpr GhcTc -> LHsExpr GhcTc
toLetExpr b e = noLoc
  (HsLet noExtField (noLoc
    (HsValBinds noExtField (XValBindsLR (NValBinds [b] [])))) e)

splitMyFunTy :: TyCon -> TyCon -> Type -> (Type, Type)
splitMyFunTy ftc mtc (coreView -> Just ty)    = splitMyFunTy ftc mtc ty
splitMyFunTy ftc mtc (TyConApp tc [mty, ty1, ty2])
  | tc == ftc = (mkTyConApp mtc [ty1], mkTyConApp mtc [ty2])
  | otherwise = error $ showSDocUnsafe $ ppr (tc, ftc, mty, ty1, ty2)
splitMyFunTy _   _   ty@((TyConApp _ xs)) = error $ showSDocUnsafe $ ppr (ty, length xs)
splitMyFunTy _   _   ty = error $ showSDocUnsafe $ ppr ty

{- HLINT ignore "Reduce duplication "-}
