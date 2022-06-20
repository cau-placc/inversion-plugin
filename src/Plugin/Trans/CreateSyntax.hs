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

import GHC.Core.ConLike
import GHC.Core.TyCo.Rep
import GHC.Data.Bag
import GHC.Hs.Binds
import GHC.Hs.Expr
import GHC.Hs.Extension
import GHC.Hs.Pat
import GHC.Parser.Annotation
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Zonk
import GHC.Types.Fixity
import Language.Haskell.Syntax.Extension
import GHC.ThToHs
import GHC.Rename.Expr
import GHC.Tc.Gen.App
import GHC.Tc.Utils.TcType

import Plugin.Effect.Monad ( type (-->)(..), appFL, toFL, share )
import Plugin.Lifted ()
import Plugin.Trans.Constr
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var
import Plugin.BuiltIn

-- | Create the lambda functions used to lift value constructors.
-- Look at their lifting for details.
mkConLam :: Maybe HsWrapper -> DataCon
         -> [(Scaled Type, HsImplBang)] -> [Id] -> TcM (LHsExpr GhcTc, Type)
-- list of types is empty -> apply the collected variables.
mkConLam mw c [] vs = do
    mtycon <- getMonadTycon
    -- Use the given wrapper for the constructor.
    let wrap = case mw of
          Just w  -> XExpr . WrapExpr . HsWrap (w <.> WpTyApp (mkTyConTy mtycon))
          Nothing -> XExpr . WrapExpr . HsWrap (WpTyApp (mkTyConTy mtycon))
    -- Apply all variables in reverse to the constructor.
    let e = foldl ((noLocA .) . HsApp EpAnnNotUsed)
            (noLocA (wrap (HsConLikeOut noExtField (RealDataCon c))))
            (map (noLocA . HsVar noExtField . noLocA) $ reverse vs)
    -- Get the result type of the constructor.
    ty <- snd . splitFunTys <$> getTypeOrPanic e -- ok
    -- Wrap the whole term in a 'return'.
    e' <- mkApp mkNewReturnTh ty [noLocA $ HsPar EpAnnNotUsed e]
    mty <- mkTyConTy <$> getMonadTycon
    return (e', mkAppTy mty ty)
-- Create lambdas for the remaining types.
mkConLam w c ((Scaled _ ty, strictness) : tys) vs = do
  mtc <- getMonadTycon
  let vty' = Scaled Many ty
  v <- freshVar vty'
  -- Create the inner part of the term with the remaining type arguments.
  (e, resty) <- mkConLam w c tys (v:vs) -- (return \xs -> Cons x xs, SML (List a -> List a)
  ftc <- getFunTycon
  let lamty2 = mkTyConApp ftc [mkTyConTy mtc, bindingType ty, bindingType resty] -- a --> (List a --> List a)
  -- Add a seq if C is strict in this arg
  (e', v') <- case strictness of
    HsLazy -> return (e, v)
    -- | strict or unpacked
    _      -> do
      -- create the lambda-bound variable, that needs to be shared
      v' <- freshVar vty'
      -- create share
      s <- mkApp mkNewShareTh ty [noLocA (HsVar noExtField (noLocA v'))]
      mtycon <- getMonadTycon
      -- create seqValue
      seqE <- mkApp (mkNewSeqValueTh (bindingType ty)) (bindingType resty)
                [noLocA (HsVar noExtField (noLocA v)), e]
      let l = noLocA (HsPar EpAnnNotUsed (mkLam (noLocA v) vty' seqE resty))
      let sty = mkTyConApp mtycon [ty]
      shareE <- mkBind [] (noLocA (HsPar EpAnnNotUsed s)) sty l resty
      return (shareE, v')
  -- Make the lambda for this variable
  let e'' = mkLam (noLocA v') (Scaled Many ty) e' resty
  -- Wrap the whole term in a 'return'.
  e''' <- mkApp mkNewReturnFunTh (ty `mkVisFunTyMany` resty) [noLocA $ HsPar EpAnnNotUsed e'']
  let mty = mkTyConTy mtc
  return (e''', mkAppTy mty lamty2)

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

-- | Create a 'app' for the given arguments and apply them.
mkFuncApp :: [Ct] -> LHsExpr GhcTc -> Type -> LHsExpr GhcTc -> Type
          -> TcM (LHsExpr GhcTc)
mkFuncApp given op ty1 arg ty2 = do
  let ty1' = bindingType ty1
  let ty2' = bindingType ty2
  mkAppWith (mkNewAppTh ty1') given ty2' [op, arg]

-- | Apply the given list of arguments to a term created by the first function.
-- Use the given set of given constraints to solve any wanted constraints.
mkAppWith :: (Type -> TcM (LHsExpr GhcTc))
          -> [Ct] -> Type -> [LHsExpr GhcTc]
          -> TcM (LHsExpr GhcTc)
mkAppWith con _ typ args = do
  e' <- con typ
  return $ foldl mkHsApp e' args

mkLHsWrap :: HsWrapper -> LHsExpr GhcTc -> LHsExpr GhcTc
mkLHsWrap w = mapLoc (XExpr . WrapExpr . HsWrap w)

mkNewBoolConversion :: TcM (LHsExpr GhcTc)
mkNewBoolConversion = do
  mtycon <- getMonadTycon
  mboolTyCon <- getTyCon "Plugin.BuiltIn" "BoolFL"
  let mboolTy = mkTyConApp mboolTyCon [mkTyConTy mtycon]
  th_expr <- liftQ [| boolFLtoBool |]
  ps_expr <- case convertToHsExpr Generated noSrcSpan th_expr of
    Left  msg -> do
      flags <- getDynFlags
      panic ("Error while converting TemplateHaskell: " ++ showSDoc flags msg)
    Right res -> return res
  noLocA <$> (rnLExpr ps_expr >>= \(x, _) -> tcApp (unLoc x) (Check (mboolTy `mkVisFunTyMany` boolTy)))

-- | Make a seq for lifted values.
mkNewSeqValueTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewSeqValueTh atype btype = do
  mtc <- getMonadTycon
  th_expr <- liftQ [| seqValue |]
  let expType = mkVisFunTyMany (mkTyConApp mtc [atype]) $ -- m a ->
                mkVisFunTyMany (mkTyConApp mtc [btype])   -- m b ->
                (mkTyConApp mtc [btype])                  -- m b
  mkNewAny th_expr expType

-- | Create a 'return' for the given argument types.
mkNewReturnTh :: Type -> TcM (LHsExpr GhcTc)
mkNewReturnTh etype = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| return |]
  let mty = mkTyConTy mtycon
  let expType = mkVisFunTyMany etype $ -- 'e ->
                mkAppTy mty etype  -- m 'e
  mkNewAny th_expr expType

-- | Create a 'return . Fun' for the given argument types.
mkNewReturnFunTh :: Type -> TcM (LHsExpr GhcTc)
mkNewReturnFunTh etype = do
  ftc <- getFunTycon
  mtycon <- getMonadTycon
  th_expr <- liftQ [| return . Func |]
  let mty = mkTyConTy mtycon
  let (_, arg, res) = splitFunTy etype
  let eLifted = mkTyConApp ftc [mty, bindingType arg, bindingType res]
  let expType = mkVisFunTyMany etype $ -- 'e ->
                mkAppTy mty eLifted    -- m 'e
  mkNewAny th_expr expType

-- | Create a '(>>=)' for the given argument types.
mkNewBindTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewBindTh etype btype = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| (>>=) |]
  let mty = mkTyConTy mtycon
  let resty = mkAppTy mty btype
  let expType = mkVisFunTyMany (mkAppTy mty etype) $        -- m 'e ->
                mkVisFunTyMany (mkVisFunTyMany etype resty) -- (e' -> m b) ->
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
  let expType = mkVisFunTyMany (mkAppTy mty optype) $ -- m optype ->
                mkVisFunTyMany (mkAppTy mty argtype)  -- m argtype ->
                restype                               -- restype
  mkNewAny th_expr expType

-- | Create a 'fmap' for the given argument types.
mkNewFmapTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewFmapTh etype btype = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| fmap |]
  let appMty = mkTyConApp mtycon . (:[])
  let expType = mkVisFunTyMany (mkVisFunTyMany etype btype) $ -- ('e -> 'b) ->
                mkVisFunTyMany (appMty etype) (appMty btype)  -- m 'e -> m 'b
  mkNewAny th_expr expType

-- | Create a 'share' for the given argument types.
mkNewShareTh :: Type -> TcM (LHsExpr GhcTc)
mkNewShareTh ty
  | isForAllTy ty = do
    mkNewReturnTh ty
  | otherwise     = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| share |]
  let expType = mkVisFunTyMany ty $    -- a ->
                mkTyConApp mtycon [ty] -- m a
  mkNewAny th_expr expType

-- | Create a 'toFL' for the given argument types.
mkNewtoFLTh :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewtoFLTh ty1 ty2 = do
  mty <- (. (: [])) . mkTyConApp <$> getMonadTycon
  th_expr <- liftQ [| toFL |]
  let expType = mkVisFunTyMany ty1 (mty ty2) -- a -> m b
  mkNewAny th_expr expType

mkNewToFL ::  Type -> Type -> TcM (LHsExpr GhcTc)
mkNewToFL ty1 ty2 = do
  mtycon <- getMonadTycon
  th_expr <- liftQ [| toFL |]
  let expType = mkVisFunTyMany ty1 (mkTyConApp mtycon [ty2])
  mkNewAny th_expr expType

-- | Create a 'apply1' for the given argument types.
mkNewApply1 :: Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply1 ty1 ty2 = do
  ftycon <- getFunTycon
  mtycon <- getMonadTycon
  mkNewAppTh (mkTyConApp ftycon [mkTyConTy mtycon, ty1, ty2]) ty1

-- | Create a 'apply2' for the given argument types.
mkNewApply2 :: Type -> Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply2 ty1 ty2 ty3 = do
  mtycon <- getMonadTycon
  ftycon <- getFunTycon
  let mty = mkTyConTy mtycon
  th_expr <- liftQ [| \f a b -> f `appFL` a `appFL` b |]
  let expType =
        mkTyConApp mtycon                                    -- Nondet
                  [mkTyConApp ftycon [mty, ty1,              --  (a :->
                    mkTyConApp ftycon [mty, ty2,             --   b :->
                       ty3]]]                                --   c)
        `mkVisFunTyMany`                                         --  ->
        mkVisFunTyMany (mkTyConApp mtycon [ty1])             -- Nondet a ->
          (mkVisFunTyMany (mkTyConApp mtycon [ty2])          -- Nondet b ->
                   (mkTyConApp mtycon [ty3]))                -- Nondet c
  mkNewAny th_expr expType

-- | Create a 'apply2Unlifted' for the given argument types.
mkNewApply2Unlifted :: Type -> Type -> Type -> TcM (LHsExpr GhcTc)
mkNewApply2Unlifted ty1 ty2 ty3 = do
  mtycon <- getMonadTycon
  ftycon <- getFunTycon
  let mty = mkTyConTy mtycon
  th_expr <- liftQ [| \f a b -> f `appFL` a `appFL` return b |]
  let expType =
        mkTyConApp mtycon                                    -- Nondet
                  [mkTyConApp ftycon [mty, ty1,              --  (a :->
                    mkTyConApp ftycon [mty, ty2,             --   b :->
                       ty3]]]                                --   c)
        `mkVisFunTyMany`                                         --  ->
        mkVisFunTyMany (mkTyConApp mtycon [ty1])             -- Nondet a ->
          (mkVisFunTyMany ty2                                --        b ->
                   (mkTyConApp mtycon [ty3]))                -- Nondet c
  mkNewAny th_expr expType

-- | Create a '(>>=)' specialized to lists for list comprehensions.
mkListBind :: Type -> Type -> TcM (SyntaxExpr GhcTc)
mkListBind a b = do
  e <- mkApp mk b []
  return (SyntaxExprTc (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| (>>=) |]
      let expType = mkTyConApp listTyCon [a]
                    `mkVisFunTyMany`
                    ((a `mkVisFunTyMany` mkTyConApp listTyCon [b])
                      `mkVisFunTyMany`
                      mkTyConApp listTyCon [b])
      mkNewAny th_expr expType

-- | Create a 'return' specialized to lists for list comprehensions.
mkListReturn :: Type -> TcM (SyntaxExpr GhcTc)
mkListReturn a = do
  e <- mkApp mk a []
  return (SyntaxExprTc (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| return |]
      let expType = a `mkVisFunTyMany` mkTyConApp listTyCon [a]
      mkNewAny th_expr expType

-- | Create a 'fail' specialized to lists for list comprehensions.
mkListFail :: Type -> TcM (SyntaxExpr GhcTc)
mkListFail a = do
  e <- mkApp mk a []
  return (SyntaxExprTc (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| fail |]
      let expType = stringTy `mkVisFunTyMany` mkTyConApp listTyCon [a]
      mkNewAny th_expr expType

-- | Create a 'guard' specialized to lists for list comprehensions.
mkListGuard :: TcM (SyntaxExpr GhcTc)
mkListGuard = do
  e <- mkApp mk unitTy []
  return (SyntaxExprTc (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| guard |]
      let expType = boolTy `mkVisFunTyMany` mkTyConApp listTyCon [unitTy]
      mkNewAny th_expr expType

-- | Create a '(>>)' specialized to lists for list comprehensions.
mkListSeq :: Type -> Type -> TcM (SyntaxExpr GhcTc)
mkListSeq a b = do
  e <- mkApp mk b []
  return (SyntaxExprTc (unLoc e) [WpHole, WpHole] WpHole)
  where
    mk _ = do
      th_expr <- liftQ [| (>>) |]
      let expType = mkTyConApp listTyCon [a]
                    `mkVisFunTyMany`
                    (mkTyConApp listTyCon [b]
                      `mkVisFunTyMany`
                      mkTyConApp listTyCon [b])
      mkNewAny th_expr expType

-- | Create a lifted empty list constructor.
mkEmptyList :: Type -> TyConMap -> TcM (LHsExpr GhcTc)
mkEmptyList ty tcs = do
  dc <- liftIO (getLiftedCon nilDataCon tcs)
  mtycon <- getMonadTycon
  return (noLocA (XExpr $ WrapExpr $ HsWrap (WpTyApp ty <.> WpTyApp (mkTyConTy mtycon))
    (HsConLikeOut noExtField (RealDataCon dc))))

-- | Create a lifted cons list constructor.
mkConsList :: Type -> TyConMap -> TcM (LHsExpr GhcTc)
mkConsList ty tcs = do
  dc <- liftIO (getLiftedCon consDataCon tcs)
  mtycon <- getMonadTycon
  return (noLocA (XExpr $ WrapExpr $ HsWrap (WpTyApp ty <.> WpTyApp (mkTyConTy mtycon))
    (HsConLikeOut noExtField (RealDataCon dc))))

-- | Create a general lambda that binds one variable on its left side.
mkLam :: LIdP GhcTc -> Scaled Type -> LHsExpr GhcTc -> Type -> LHsExpr GhcTc
mkLam v ty' bdy resty =
  let pat = VarPat noExtField v
      grhs = GRHS EpAnnNotUsed ([] :: [GuardLStmt GhcTc]) bdy
      rhs = GRHSs emptyComments [noLoc grhs] (EmptyLocalBinds noExtField)
      match = Match EpAnnNotUsed LambdaExpr [noLocA pat] rhs
      mgtc = MatchGroupTc [ty'] resty
      mg = MG mgtc (noLocA [noLocA match]) Generated
  in noLocA $ HsPar EpAnnNotUsed $ noLocA $ HsLam noExtField mg

-- | Create a simple let expression that binds the given variable to
-- the first LHsExpr, where the other LHsExpr is used for the "in" of the let.
mkSimpleLet :: RecFlag -> LHsExpr GhcTc -> LHsExpr GhcTc -> Var -> Type
            -> HsExpr GhcTc
mkSimpleLet f scr e v a =
  let grhs = GRHS EpAnnNotUsed [] scr
      grhss = GRHSs emptyComments [noLoc grhs] (EmptyLocalBinds noExtField)
      ctxt = FunRhs (noLocA (varName v)) Prefix NoSrcStrict
      alt = Match EpAnnNotUsed ctxt [] grhss
      mgtc = MatchGroupTc [] a
      mg = MG mgtc (noLocA [noLocA alt]) Generated
      b = FunBind WpHole (noLocA v) mg []
      nbs = NValBinds [(f, listToBag [noLocA b])] []
      bs = HsValBinds EpAnnNotUsed (XValBindsLR nbs)
  in HsLet noExtField bs e

-- | Create a simple let expression that binds the given pattern to
-- the first LHsExpr, where the other LHsExpr is used for the "in" of the let.
mkSimplePatLet :: Type -> LHsExpr GhcTc -> LPat GhcTc -> LHsExpr GhcTc
               -> HsExpr GhcTc
mkSimplePatLet ty scr p e =
  let grhs = GRHS EpAnnNotUsed [] scr
      grhss = GRHSs emptyComments [noLoc grhs] (EmptyLocalBinds noExtField)
      b = PatBind ty p grhss ([], [[]])
      nbs = NValBinds [(Recursive, listToBag [noLocA b])] []
      bs = HsValBinds EpAnnNotUsed (XValBindsLR nbs)
  in HsLet noExtField bs e

-- | Create a simple (case) alternative with the given right side and patterns.
mkSimpleAlt :: HsMatchContext GhcRn -> LHsExpr GhcTc -> [LPat GhcTc]
            -> Match GhcTc (LHsExpr GhcTc)
mkSimpleAlt ctxt e ps =
  let grhs = GRHS EpAnnNotUsed [] e
      grhss = GRHSs emptyComments [noLoc grhs] (EmptyLocalBinds noExtField)
  in Match EpAnnNotUsed ctxt ps grhss

-- | Create a variable pattern with the given parameter.
mkVarPat :: Var -> LPat GhcTc
mkVarPat v = noLocA (VarPat noExtField (noLocA v))

-- | Creates a let statement for the given binding.
toLetStmt :: (RecFlag, LHsBinds GhcTc) -> ExprLStmt GhcTc
toLetStmt b = noLocA (LetStmt EpAnnNotUsed bs)
  where
    bs = HsValBinds EpAnnNotUsed (XValBindsLR (NValBinds [b] []))

-- | Create a let with the given binding and inner expression.
toLetExpr :: (RecFlag, LHsBinds GhcTc) -> LHsExpr GhcTc -> LHsExpr GhcTc
toLetExpr b e = noLocA (HsLet noExtField bs e)
  where
    bs = HsValBinds EpAnnNotUsed (XValBindsLR (NValBinds [b] []))

splitMyFunTy :: TyCon -> TyCon -> Type -> (Type, Type)
splitMyFunTy ftc mtc (coreView -> Just ty)    = splitMyFunTy ftc mtc ty
splitMyFunTy ftc mtc (TyConApp tc [mty, ty1, ty2])
  | tc == ftc = (mkTyConApp mtc [ty1], mkTyConApp mtc [ty2])
  | otherwise = error $ showSDocUnsafe $ ppr (tc, ftc, mty, ty1, ty2)
splitMyFunTy _   _   ty@((TyConApp _ xs)) = error $ showSDocUnsafe $ ppr (ty, length xs)
splitMyFunTy _   _   ty = error $ showSDocUnsafe $ ppr ty

{- HLINT ignore "Reduce duplication "-}
