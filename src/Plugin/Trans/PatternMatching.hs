{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : Plugin.Trans.PatternMatching
-- Description : Simplify pattern matching
-- Copyright   : (c) Kai-Oliver Prott (2020)
-- Maintainer  : kai.prott@hotmail.de
--
-- This module simplifies pattern matching for functions, case, let and lambda
-- expressions as well as do notation.
-- The pattern match compilation is the main preprocessing phase
-- before lifting a function.
module Plugin.Trans.PatternMatching (compileMatchGroup, matchExpr, compileLetBind) where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Generics.Aliases
import Data.Generics.Schemes
import Data.Tuple.Extra
import Data.Data (Data, Typeable)

import GHC.Builtin.Names
import GHC.Core.ConLike
import GHC.Core.PatSyn
import GHC.Core.TyCo.Rep
import GHC.Data.Bag
import GHC.Hs.Binds
import GHC.Hs.Expr
import GHC.Hs.Extension
import GHC.Hs.Lit
import GHC.Hs.Pat
import GHC.Hs.Type
import GHC.Iface.Env
import GHC.Parser.Annotation
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Zonk
import GHC.Types.Fixity
import GHC.Types.Id.Make
import GHC.Types.SourceText
import GHC.Types.TyThing
import GHC.Utils.Error
import GHC.Unit.Finder (FindResult(..), findImportedModule)
import Language.Haskell.Syntax.Extension
import Language.Haskell.TH (Extension (..))
import Plugin.Trans.CreateSyntax
import Plugin.Trans.LExprEQ
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var

{-
  Pattern matching done by the classical matrix algorithm, but instead of
  left-to-right semantics, we search for an inductive position
  and match there first.

  Please Note:

  Functions are compiled via `compileMatchGroup`.
  In the case of nullary functions, the result will be an expression instead of
  a MatchGroup. Thats why we need that Either result type.

  Cases are compiled by directly calling compileMatching.
  That function needs list of variables (a singleton list in this case),
  to which any as-patterns will be bound to. Thus, we have to create a
  let-binding for the case-scrutinee, unless it is a variable itself.

  A special case is used if the scrutinee is already a variable.
-}

-- | Simplify any pattern matching in the given expression.
-- Only looks at the top of the expression and simplifies a single
-- case, lambda, let, ... and not any deeper parts of the expression.
matchExpr :: HsExpr GhcTc -> TcM (HsExpr GhcTc)
matchExpr (HsLam x mg) =
  compileMatchGroup mg >>= \case
    Left mg' -> return (HsLam x mg')
    Right e -> return (unLoc e)
matchExpr (HsLamCase _ mg) =
  compileMatchGroup mg >>= \case
    Left mg' -> return (HsLam noExtField mg')
    Right e -> return (unLoc e)
matchExpr
  ( HsCase
      _
      (L _ (HsVar _ (L _ v)))
      (MG (MatchGroupTc _ res) (L _ alts) _)
    ) = do
    e <- errorExpr CaseAlt res >>= compileMatching [v] res alts
    return (unLoc e)
matchExpr
  ( HsCase
      _
      scr
      ( MG
          (MatchGroupTc [a@(Scaled _ ty)] res)
          (L _ alts)
          _
        )
    ) = do
    v <- freshVar a
    e <- errorExpr CaseAlt res >>= compileMatching [v] res alts
    return (mkSimpleLet NonRecursive scr e v ty)
matchExpr (HsMultiIf ty grhs) = do
  err <- errorExpr IfAlt ty
  unLoc <$> foldM compileGuard err grhs
matchExpr (HsLet _ bs e) = do
  (bs', _, strictVs) <- compileLet bs
  strict <- foldrM mkSeq e (reverse $ map unLoc $ sortBy cmpLocated strictVs)
  let eLet = foldr toLetExpr strict bs'
  return (unLoc eLet)
matchExpr (HsDo x ctxt (L l stmts)) = do
  (stmts', swapCtxt) <- compileDo x ctxt stmts
  let ctxt' = if swapCtxt then DoExpr Nothing else ctxt
  return (HsDo x ctxt' (L l stmts'))
matchExpr e = return e

-- | Translate any pattern in do-notation or comprehensions.
-- Also transforms list comprehensions into monad comprehensions and
-- fills any annotated functions that are missing because of that conversion.
compileDo ::
  Type ->
  HsStmtContext GhcRn ->
  [ExprLStmt GhcTc] ->
  TcM ([ExprLStmt GhcTc], Bool)
compileDo _ GhciStmtCtxt _ =
  failWithTc $
    text
      "Do-Notation in GHCi is not supported with the Curry-Plugin"
compileDo _ _ [] =
  panicAny "Empty do-expression or missing last statement" ()
compileDo ty ctxt [L l (LastStmt x e b r)] = do
  let ty' = snd (splitAppTy ty)
  (r', e', ctxtSwap) <- case ctxt of
    ListComp -> do
      lr <- mkListReturn ty'
      return (NoSyntaxExprTc, noLocA (applySynExpr lr (unLoc e)), True)
    _ -> return (r, e, False)
  return ([L l (LastStmt x e' b r')], ctxtSwap)
compileDo _ _ (s@(L _ LastStmt {}) : _) =
  panicAny "Unexpected last statement in do notation" s
compileDo ty ctxt ((L l (BindStmt (XBindStmtTc b' _ _ f') p (e :: LHsExpr GhcTc)) :: ExprLStmt GhcTc) : stmts) = do
  -- Compile the rest of the statements and create a do-expression.
  (stmts', swapCtxt) <- compileDo ty ctxt stmts
  let ctxt' = if swapCtxt then DoExpr Nothing else ctxt
  let rest = noLocA (HsDo ty ctxt' (noLocA stmts'))

  emty <- getTypeOrPanic e -- ok
  let ety = snd (splitAppTy emty)

  -- Create the bind and fail for ListComp.
  let ty' = snd (splitAppTy ty)
  (b, f) <- case ctxt of
    ListComp -> (,) <$> mkListBind ety ty' <*> mkListFail ty'
    _ -> return (b', fromMaybe NoSyntaxExprTc f')

  -- Create the regular and fail alternatatives
  -- (if f is not noSynExpr, the fail one never gets used).
  v <- noLocA <$> freshVar (Scaled Many ety)
  let alt = mkSimpleAlt CaseAlt rest [p]
      fe =
        mkHsWrap
          (syn_res_wrap f)
          ( HsApp
              EpAnnNotUsed
              (noLocA (syn_expr f))
              ( fmap
                  (mkHsWrap (head (syn_arg_wraps f)))
                  (errorStrStmt ctxt)
              )
          )
      altFail = mkSimpleAlt CaseAlt (noLocA fe) [noLocA (WildPat ety)]
      alts = case f of
        NoSyntaxExprTc -> [noLocA alt]
        _ -> [noLocA alt, noLocA altFail]
      mgtc = MatchGroupTc [Scaled Many ety] ty
      mg = MG mgtc (noLocA alts) Generated
  e' <- matchExpr (HsCase noExtField (noLocA (HsVar noExtField v)) mg)
  return
    ( [ L
          l
          ( BindStmt
              (XBindStmtTc b ty Many Nothing)
              (noLocA (VarPat noExtField v))
              e
          ),
        noLocA (LastStmt noExtField (noLocA e') Nothing NoSyntaxExprTc)
      ],
      -- Normally ListCompr creates a return around LastStmt.
      -- Prevent creation of duplicate return for MonadCompr
      -- due to nested LastStmt by changing the context.
      case ctxt of ListComp -> True; _ -> False
    )
compileDo ty ctxt (L _ (LetStmt _ bs) : xs) = do
  (bs', _, strictVs) <- compileLet bs
  let lets = map toLetStmt bs'
  (xs', swapCtxt) <- compileDo ty ctxt xs
  if null strictVs
    then return (lets ++ xs', swapCtxt)
    else do
      let ctxt' = if swapCtxt then DoExpr Nothing else ctxt
      let rest = noLocA (HsDo ty ctxt' (noLocA xs'))
      e <- foldrM mkSeq rest (reverse $ map unLoc $ sortBy cmpLocated strictVs)
      let lastS = noLocA (LastStmt noExtField e Nothing NoSyntaxExprTc)
      return (lets ++ [lastS], swapCtxt)
compileDo _ _ (s@(L _ ApplicativeStmt {}) : _) = do
  reportError
    ( mkMsgEnvelope
        (getLocA s)
        neverQualify
        "Applicative do-notation is not supported by the plugin"
    )
  failIfErrsM
  return ([], False)
compileDo ty ctxt (L l (BodyStmt x e@(L el ee) s g) : xs) = do
  (xs', swapCtxt) <- compileDo ty ctxt xs
  -- Add the missing sequence operator (>>) for list comprehensions.
  let ty' = snd (splitAppTy ty)
  (s', g', e') <- case ctxt of
    ListComp ->
      (,NoSyntaxExprTc,) <$> mkListSeq unitTy ty'
        <*> fmap (L el . (`applySynExpr` ee)) mkListGuard
    _ -> return (s, g, e)
  return (L l (BodyStmt x e' s' g') : xs', swapCtxt)
compileDo _ _ (s@(L _ ParStmt {}) : _) = do
  reportError
    ( mkMsgEnvelope
        (getLocA s)
        neverQualify
        "Parallel list comprehensions are not supported by the plugin"
    )
  failIfErrsM
  return ([], False)
compileDo _ _ (s@(L _ TransStmt {}) : _) = do
  reportError
    ( mkMsgEnvelope
        (getLocA s)
        neverQualify
        "Transformative list comprehensions are not supported by the plugin"
    )
  failIfErrsM
  return ([], False)
compileDo _ _ (s@(L _ RecStmt {}) : _) = do
  reportError
    ( mkMsgEnvelope
        (getLocA s)
        neverQualify
        "Recursive do-notation is not supported by the plugin"
    )
  failIfErrsM
  return ([], False)

applySynExpr :: SyntaxExpr GhcTc -> HsExpr GhcTc -> HsExpr GhcTc
applySynExpr NoSyntaxExprTc ex = ex
applySynExpr (SyntaxExprTc se _ _) ex =
  HsApp
    EpAnnNotUsed
    (noLocA (HsPar EpAnnNotUsed (noLocA se)))
    (noLocA (HsPar EpAnnNotUsed (noLocA ex)))

-- | Desugars pattern bindings in the given let-bindings.
-- This is done by introducing selector functions for each of them.
compileLet ::
  HsLocalBinds GhcTc ->
  TcM ([(RecFlag, LHsBinds GhcTc)], [Located Var], [Located Var])
compileLet (HsValBinds _ (XValBindsLR (NValBinds bs _))) = do
  (bs', vss, strictVs) <- unzip3 <$> mapM compileValBs bs
  return (bs', concat vss, concat strictVs)
  where
    compileValBs ::
      (RecFlag, LHsBinds GhcTc) ->
      TcM ((RecFlag, LHsBinds GhcTc), [Located Var], [Located Var])
    compileValBs (f, bs') = do
      (bss, vss, strictVs) <- unzip3 <$> mapM compileLetBind (bagToList bs')
      return ((f, listToBag (concat bss)), concat vss, concat strictVs)
compileLet (HsIPBinds _ _) = do
  reportError
    ( mkMsgEnvelope
        noSrcSpan
        neverQualify
        "Implicit parameters are not supported by the plugin"
    )
  failIfErrsM
  return ([], [], [])
compileLet _ = return ([], [], [])

-- | Desugars pattern bindings in the given let-binding.
-- This is done by introducing (multiple) selector functions
-- for the single binding. Also returns a lift of strict variables
compileLetBind ::
  LHsBindLR GhcTc GhcTc ->
  TcM ([LHsBindLR GhcTc GhcTc], [Located Var], [Located Var])
compileLetBind (L l (AbsBinds x tvs evs ex ev bs sig)) = do
  (bss, vss, strictVss) <- unzip3 <$> mapM compileLetBind (bagToList bs)
  let bs' = listToBag $ concat bss
  (realVs, mbex) <- unzip <$> mapM (getRealVar ex) (concat vss)
  let newExports = ex ++ catMaybes mbex
  strictVs <- map fst <$> mapM (getRealVar newExports) (concat strictVss)
  let binding = L l (AbsBinds x tvs evs newExports ev bs' sig)
  return ([binding], realVs, strictVs)
  where
    getRealVar ::
      [ABExport GhcTc] ->
      GenLocated l Var ->
      TcM (GenLocated l Var, Maybe (ABExport GhcTc))
    getRealVar [] (L l' v) = do
      u <- getUniqueM
      let p = setVarUnique v u
      -- Not currently exported, so create an export that we can seq later
      return (L l' p, Just (ABE noExtField p v WpHole (SpecPrags [])))
    getRealVar (ABE _ p m _ _ : _) (L l' v)
      | v == m = return (L l' p, Nothing)
    getRealVar (_ : ex') v = getRealVar ex' v
compileLetBind pb@(L _ (PatBind ty p grhss _)) = do
  mtc <- getMonadTycon
  ftc <- getFunTycon
  -- we do not use ConstraintSolver.removeNondet,
  -- as TyConMap is not available and not required
  let ty' = everywhere (mkT (rmNondet mtc ftc)) ty
  (b', fname) <- createOrdinaryFun ty'
  (p', vs) <- prepareSelPat p
  let pe = noLocA (HsVar noExtField (noLocA fname))
  bs <- mapM (mkSelFun ty' p' pe) vs
  flags <- getDynFlags
  let decidedStrict =
        isBangPat p
          || (Strict `xopt` flags && isNoLazyPat p)
  let export = L (getLocA pb) fname
  return (b' : bs, [export], [export | decidedStrict])
  where
    origStrictness
      | isBangPat p = SrcStrict
      | isNoLazyPat p = NoSrcStrict
      | otherwise = SrcLazy

    -- create:
    -- fname = grhss
    createOrdinaryFun ty' = do
      fname <- freshVar (Scaled Many ty')
      let ctxt = FunRhs (noLocA (varName fname)) Prefix origStrictness
          alt = Match EpAnnNotUsed ctxt [] grhss
          mgtc = MatchGroupTc [] ty'
          mg = MG mgtc (noLocA [noLocA alt]) Generated
      return (noLocA (FunBind WpHole (noLocA fname) mg []), fname)
    -- create:
    -- old = (\p' -> new) pe
    mkSelFun ty' p' pe (old, new) = do
      mtc <- getMonadTycon
      ftc <- getFunTycon
      let altLam =
            mkSimpleAlt
              LambdaExpr
              (noLocA (HsVar noExtField (noLocA new)))
              [everywhere (mkT (rmNondet mtc ftc)) (removeOtherPatterns new p')]
          mgtcLam = MatchGroupTc [Scaled Many ty'] (varType new)
          mgLam = MG mgtcLam (noLocA [noLocA altLam]) Generated
      lam <- matchExpr (HsLam noExtField mgLam)
      let bdy = HsApp EpAnnNotUsed (noLocA (HsPar EpAnnNotUsed (noLocA lam))) pe
          grhs = GRHS EpAnnNotUsed [] (noLocA bdy)
          grhssSel =
            GRHSs
              emptyComments
              [noLoc grhs]
              (EmptyLocalBinds noExtField)
          ctxt = FunRhs (noLocA (varName old)) Prefix NoSrcStrict
          alt = Match EpAnnNotUsed ctxt [] grhssSel
          mgtc = MatchGroupTc [] (varType new)
          mg = MG mgtc (noLocA [noLocA alt]) Generated
      return (noLocA (FunBind WpHole (noLocA old) mg []))

    -- rename all variables in the pattern and remove all laziness in pattern
    prepareSelPat :: LPat GhcTc -> TcM (LPat GhcTc, [(Var, Var)])
    prepareSelPat (L l1 p1) =
      first (L l1) <$> case p1 of
        VarPat x (L l2 v) -> do
          v' <- freshVar (Scaled (varMult v) (varType v))
          return (VarPat x (L l2 v'), [(v, v')])
        LazyPat _ p2 -> first unLoc <$> prepareSelPat p2
        AsPat x (L l2 v) p2 -> do
          v' <- freshVar (Scaled (varMult v) (varType v))
          (p3, vs') <- prepareSelPat p2
          return (AsPat x (L l2 v') p3, (v, v') : vs')
        ParPat _ p2 -> first unLoc <$> prepareSelPat p2
        BangPat x p2 -> first (BangPat x) <$> prepareSelPat p2
        ListPat x ps -> do
          (ps', vss) <- unzip <$> mapM prepareSelPat ps
          return (ListPat x ps', concat vss)
        TuplePat x ps b -> do
          (ps', vss) <- unzip <$> mapM prepareSelPat ps
          return (TuplePat x ps' b, concat vss)
        SumPat x p2 t b -> first (\p3 -> SumPat x p3 t b) <$> prepareSelPat p2
        p2@ConPat {pat_args = args} ->
          first (\args' -> p2 {pat_args = args'}) <$> prepareSelDetails args
        ViewPat x e p2 -> first (ViewPat x e) <$> prepareSelPat p2
        NPlusKPat x (L l2 v) lit1 lit2 se1 se2 -> do
          v' <- freshVar (Scaled (varMult v) (varType v))
          return (NPlusKPat x (L l2 v') lit1 lit2 se1 se2, [(v, v')])
        SigPat x p2 ty' -> first (flip (SigPat x) ty') <$> prepareSelPat p2
        XPat (CoPat a p2 c) -> do
          (L _ p3, vs) <- prepareSelPat (noLocA p2)
          return (XPat (CoPat a p3 c), vs)
        p2 -> return (p2, [])

    prepareSelDetails ::
      HsConPatDetails GhcTc ->
      TcM (HsConPatDetails GhcTc, [(Var, Var)])
    prepareSelDetails (PrefixCon _ ps) = do
      (ps', vss) <- unzip <$> mapM prepareSelPat ps
      return (PrefixCon [] ps', concat vss)
    prepareSelDetails (RecCon (HsRecFields flds dd)) = do
      (flds', vss) <- unzip <$> mapM prepareSelField flds
      return (RecCon (HsRecFields flds' dd), concat vss)
    prepareSelDetails (InfixCon p1 p2) = do
      (p1', vs1) <- prepareSelPat p1
      (p2', vs2) <- prepareSelPat p2
      return (InfixCon p1' p2', vs1 ++ vs2)

    prepareSelField (L _ (HsRecField x v p1 pun)) =
      first (noLocA . flip (HsRecField x v) pun) <$> prepareSelPat p1

    removeOtherPatterns :: Var -> LPat GhcTc -> LPat GhcTc
    removeOtherPatterns new p0@(L l1 p1) = L l1 $ case p1 of
      VarPat x (L l2 v)
        | v == new -> VarPat x (L l2 v)
        | otherwise -> WildPat (varType v)
      AsPat x (L l2 v) p2
        | v == new -> VarPat x (L l2 v)
        | p2 `contains` new -> unLoc (removeOtherPatterns new p2)
        | otherwise -> WildPat (varType v)
      -- always keep banged pattern for correct strictness
      BangPat x p2 -> BangPat x $ removeOtherPatterns new p2
      ListPat x ps
        | ps `contains` new -> ListPat x $ map (removeOtherPatterns new) ps
        | otherwise -> WildPat (hsLPatType p0)
      TuplePat x ps b
        | ps `contains` new ->
            flip (TuplePat x) b $
              map (removeOtherPatterns new) ps
        | otherwise -> WildPat (hsLPatType p0)
      SumPat x p2 t b
        | p2 `contains` new -> SumPat x (removeOtherPatterns new p2) t b
        | otherwise -> WildPat (hsLPatType p0)
      p2@ConPat {pat_args = args}
        | p2 `contains` new -> p2 {pat_args = removeOtherDetails new args}
        | otherwise -> WildPat (hsLPatType p0)
      ViewPat x e p2
        | p2 `contains` new -> ViewPat x e $ removeOtherPatterns new p2
      NPlusKPat x (L l2 v) lit1 lit2 se1 se2
        | v == new -> NPlusKPat x (L l2 v) lit1 lit2 se1 se2
        | otherwise -> WildPat (hsLPatType p0)
      SigPat x p2 ty' -> flip (SigPat x) ty' $ removeOtherPatterns new p2
      XPat (CoPat b p2 c) ->
        XPat
          ( CoPat
              b
              ( unLoc
                  (removeOtherPatterns new (noLocA p2))
              )
              c
          )
      _ -> WildPat (hsLPatType p0)

    removeOtherDetails new (PrefixCon _ ps) =
      PrefixCon [] (map (removeOtherPatterns new) ps)
    removeOtherDetails new (RecCon (HsRecFields flds dd)) =
      RecCon (HsRecFields (map (removeOtherField new) flds) dd)
    removeOtherDetails new (InfixCon p1 p2) =
      InfixCon (removeOtherPatterns new p1) (removeOtherPatterns new p2)

    removeOtherField new (L l1 (HsRecField x v p1 pun)) =
      L l1 (HsRecField x v (removeOtherPatterns new p1) pun)
compileLetBind
  b@( L
        _
        ( FunBind
            _
            (L _ fname)
            ( MG
                (MatchGroupTc args _)
                ( L
                    _
                    ( L
                        _
                        ( Match
                            _
                            (FunRhs _ _ strict)
                            _
                            _
                          )
                        : _
                      )
                  )
                _
              )
            _
          )
      ) = do
    flags <- getDynFlags
    -- Evaluating a function strict is never required
    -- if it is defined with at least one argument.
    let decidedStrict =
          null args
            && ( strict == SrcStrict
                   || (strict == NoSrcStrict && Strict `xopt` flags)
               )
    let export = L (getLocA b) fname
    return ([b], [export], [export | decidedStrict])
compileLetBind b = return ([b], [], [])

-- | Checks if the first term contains the second term.
contains :: (Eq a, Data r, Typeable a) => r -> a -> Bool
contains r a = not (null (listify (== a) r))

rmNondet :: TyCon -> TyCon -> Type -> Type
rmNondet mtc _ (TyConApp tc tys)
  | mtc == tc = last tys
rmNondet _ ftc (TyConApp tc [_, arg, res])
  | ftc == tc = mkVisFunTyMany arg res
rmNondet _ _ other = other

-- | Compile a group of (case) alternatives into a more simple case without
-- any nested pattern matching.
compileMatchGroup ::
  MatchGroup GhcTc (LHsExpr GhcTc) ->
  TcM
    ( Either
        (MatchGroup GhcTc (LHsExpr GhcTc))
        (LHsExpr GhcTc)
    )
compileMatchGroup
  ( MG
      mgtc@(MatchGroupTc args res)
      (L _ alts@(L _ (Match _ ctxt@FunRhs {} _ _) : _))
      _
    )
    | null args = do
        e <- errorExpr ctxt res >>= compileRhs alts
        let alt = mkSimpleAlt ctxt e []
        let mg = MG mgtc (noLocA [noLocA alt]) Generated
        return (Left mg)
compileMatchGroup
  mg@( MG
         (MatchGroupTc [_] _)
         (L _ (L _ (Match _ LambdaExpr [p] _) : _))
         _
       )
    | isVarPat p = return (Left mg)
compileMatchGroup
  mg@( MG
         (MatchGroupTc _ res)
         (L _ (L _ (Match _ ctxt _ _) : _))
         _
       ) =
    errorExpr ctxt res >>= makeUnaryBindings ctxt [] mg
compileMatchGroup mg = return (Left mg)

-- | Transform any multi-arity match group
-- into multiple lambdas and case expressions
makeUnaryBindings ::
  HsMatchContext GhcRn ->
  [Var] ->
  MatchGroup GhcTc (LHsExpr GhcTc) ->
  LHsExpr GhcTc ->
  TcM
    ( Either
        (MatchGroup GhcTc (LHsExpr GhcTc))
        (LHsExpr GhcTc)
    )
makeUnaryBindings ctxt vs (MG (MatchGroupTc args res) (L l alts) _) e =
  -- We leave the alternatives as they are, while recursing as long as
  -- args is not null.
  -- During that time, single lambda expressions and the variables they bind are
  -- generated and later collected for the pattern-match algorithm.
  case args of
    [] ->
      let vs' = reverse vs
       in Right <$> compileMatching vs' res alts e
    x : xs -> do
      v <- freshVar x
      let remaining = MG (MatchGroupTc xs res) (L l alts) Generated
      exOrMG <- makeUnaryBindings LambdaExpr (v : vs) remaining e
      let bdy1 = case exOrMG of
            Left mg -> noLocA (HsLam noExtField mg)
            Right ex -> ex

      let mgtcLam =
            MatchGroupTc
              [x]
              (foldr (\(Scaled a b) -> mkVisFunTy a b) res xs)
      let patLam = VarPat noExtField (noLocA v)
      let innerCtxt = if isFunCtxt ctxt then LambdaExpr else ctxt
      let altLam = mkSimpleAlt innerCtxt bdy1 [noLocA patLam]
      let mgLam = MG mgtcLam (noLocA [noLocA altLam]) Generated

      if isFunCtxt ctxt
        then do
          let mgtcTop =
                MatchGroupTc
                  []
                  (foldr (\(Scaled a b) -> mkVisFunTy a b) res args)
          let bdy2 = HsLam noExtField mgLam
          let altTop = mkSimpleAlt ctxt (noLocA bdy2) []
          let mgTop = MG mgtcTop (noLocA [noLocA altTop]) Generated
          return (Left mgTop)
        else return (Left mgLam)

-- | Compile all matchings of a specific match group to nested cases.
compileMatching ::
  [Var] ->
  Type ->
  [LMatch GhcTc (LHsExpr GhcTc)] ->
  LHsExpr GhcTc ->
  TcM (LHsExpr GhcTc)
compileMatching [] _ eqs err = compileRhs eqs err
compileMatching vs ty eqs err = matchOn 0 vs ty eqs err

-- | Compile local bindings and guards of a rhs.
compileRhs ::
  [LMatch GhcTc (LHsExpr GhcTc)] ->
  LHsExpr GhcTc ->
  TcM (LHsExpr GhcTc)
compileRhs (L _ (Match _ _ _ (GRHSs _ grhs lcl)) : xs) err = do
  err' <- compileRhs xs err
  mkLocalBinds lcl <$> foldM compileGuard err' (reverse grhs)
compileRhs _ err = return err

-- | Compile a single guard alternative.
compileGuard ::
  LHsExpr GhcTc ->
  LGRHS GhcTc (LHsExpr GhcTc) ->
  TcM (LHsExpr GhcTc)
compileGuard err (L _ (GRHS _ stmts e)) =
  foldM (compileGuardStmt err) e (reverse stmts)

-- | Compile a single statement from a guard.
compileGuardStmt ::
  LHsExpr GhcTc ->
  LHsExpr GhcTc ->
  GuardLStmt GhcTc ->
  TcM (LHsExpr GhcTc)
compileGuardStmt err e (L _ (BindStmt _ p (L _ (HsVar _ (L _ v))))) = do
    let alt = mkSimpleAlt CaseAlt e [p]
    resty <- getTypeOrPanic e -- ok
    compileMatching [v] resty [noLocA alt] err
compileGuardStmt err e (L _ (BindStmt _ p g)) = do
  let alt = mkSimpleAlt CaseAlt e [p]
  ty <- getTypeOrPanic g -- ok
  resty <- getTypeOrPanic e -- ok
  v <- freshVar (Scaled Many ty)
  e' <- compileMatching [v] resty [noLocA alt] err
  return (noLocA (mkSimpleLet Recursive g e' v ty))
compileGuardStmt err e (L _ (BodyStmt _ g _ _)) =
  return (noLocA (HsIf noExtField g e err))
compileGuardStmt _ e (L _ (LetStmt _ b)) =
  return (noLocA (HsLet noExtField b e))
compileGuardStmt _ _ s =
  panicAny "Unexpected statement in guard" s

mkLocalBinds :: HsLocalBinds GhcTc -> LHsExpr GhcTc -> LHsExpr GhcTc
mkLocalBinds (EmptyLocalBinds _) e = e
mkLocalBinds b e = noLocA (HsLet noExtField b e)

matchOn ::
  Int ->
  [Var] ->
  Type ->
  [LMatch GhcTc (LHsExpr GhcTc)] ->
  LHsExpr GhcTc ->
  TcM (LHsExpr GhcTc)
matchOn n vs ty eqs err = do
  let pms = map (getPatternAt n) eqs
  let pmss = groupBy (\a -> isSamePatternType (fst a) . fst) pms
  foldM (matchOnSame n vs ty) err (reverse pmss)

matchOnSame ::
  Int ->
  [Var] ->
  Type ->
  LHsExpr GhcTc ->
  [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))] ->
  TcM (LHsExpr GhcTc)
matchOnSame n vs ty err eqs
  | isVar = mkVarMatch n vs ty err eqs
  | isConstr = mkConMatch n vs ty err eqs
  | otherwise = mkOtherMatch n vs ty err eqs
  where
    isVar = isVarPat (fst (head eqs))
    isConstr = isConstrPat (fst (head eqs))

mkVarMatch ::
  Int ->
  [Var] ->
  Type ->
  LHsExpr GhcTc ->
  [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))] ->
  TcM (LHsExpr GhcTc)
mkVarMatch n vs ty err eqs = do
  let (v, vs') = getAndDrop n vs
  let noAs = map (preprocessAs v) eqs
  alts <- mapM (bindVarAlt v) noAs
  e <- compileMatching vs' ty alts err
  dflags <- getDynFlags
  -- This match is strict as soon as at most one of noAs is a bang pattern
  -- or if Strict is turned on and at least one of the pattern is not lazy.
  if any (isBangPat . fst) noAs
    || (Strict `xopt` dflags && any (isNoLazyPat . fst) noAs)
    then mkSeq v e
    else return e

-- HACK: since Int# is "invisible" to the lifting
-- and any I# constructor for Int is removed,
-- this function has to see through any I# constructor
bindVarAlt ::
  Var ->
  (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc)) ->
  TcM (LMatch GhcTc (LHsExpr GhcTc))
bindVarAlt v (L _ (VarPat _ (L _ v')), m) = return (substitute v v' m)
bindVarAlt _ (L _ (WildPat _), m) = return m
bindVarAlt v (L _ (BangPat _ p), m) = bindVarAlt v (p, m)
bindVarAlt v (L _ (LazyPat _ p), m) = bindVarAlt v (p, m)
bindVarAlt v (L _ (ParPat _ p), m) = bindVarAlt v (p, m)
bindVarAlt v (L _ (SigPat _ p _), m) = bindVarAlt v (p, m)
bindVarAlt v (L _ (XPat (CoPat _ p _)), m) = bindVarAlt v (noLocA p, m)
bindVarAlt v (L _ p@ConPat {}, m)
  | L _ (RealDataCon c) <- pat_con p,
    c == intDataCon,
    [arg] <- hsConPatArgs (pat_args p) =
      bindVarAlt v (arg, m)
bindVarAlt _ (_, m) = return m

mkSeq :: Var -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
mkSeq v e = do
  ty <- getTypeOrPanic e -- ok
  mtc <- getMonadTycon
  ftc <- getFunTycon
  -- we do not use ConstraintSolver.removeNondet,
  -- as TyConMap is not available and not required
  let vty = everywhere (mkT (rmNondet mtc ftc)) (varType v)
  return
    ( noLocA
        ( HsApp
            EpAnnNotUsed
            ( noLocA
                ( HsApp
                    EpAnnNotUsed
                    ( noLocA
                        ( mkHsWrap
                            ( WpTyApp ty
                                <.> WpTyApp vty
                                <.> WpTyApp liftedRepTy
                            )
                            (HsVar noExtField (noLocA seqId))
                        )
                    )
                    (noLocA (HsVar noExtField (noLocA (setVarType v vty))))
                )
            )
            e
        )
    )

mkOtherMatch ::
  Int ->
  [Var] ->
  Type ->
  LHsExpr GhcTc ->
  [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))] ->
  TcM (LHsExpr GhcTc)
mkOtherMatch _ _ _ _ [] =
  panicAny "Unexpected empty list of rules" ()
mkOtherMatch _ _ _ e ((p@(L _ _), _) : _) = do
  reportError
    ( mkMsgEnvelope
        (getLocA p)
        neverQualify
        "Pattern match extensions are not supported by the plugin"
    )
  failIfErrsM
  return e

mkConMatch ::
  Int ->
  [Var] ->
  Type ->
  LHsExpr GhcTc ->
  [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))] ->
  TcM (LHsExpr GhcTc)
mkConMatch n vs ty2 err eqs = do
  let (v, vs') = getAndDrop n vs
  let ty1 = varType v
  let noAs = map (preprocessAs v) eqs
  alts <- mkAlts v vs' ty1 ty2 err noAs
  case alts of
    Left as -> return (noLocA e)
      where
        mgtc = MatchGroupTc [Scaled Many ty1] ty2
        mg = MG mgtc (noLocA as) Generated
        e = HsCase noExtField (noLocA (HsVar noExtField (noLocA v))) mg
    Right e -> return e

-- This can Either return a List of matches if the top pattern is not lazy,
-- or if it is lazy, we return the expression to be used instead.
mkAlts ::
  Var ->
  [Var] ->
  Type ->
  Type ->
  LHsExpr GhcTc ->
  [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))] ->
  TcM (Either [LMatch GhcTc (LHsExpr GhcTc)] (LHsExpr GhcTc))
mkAlts v vs ty1 ty2 err eqs@((vp@(L _ (ViewPat _ e p)), _) : _) = do
  let (same, different) = partition (\(pat, _) -> sameTopCon pat vp) eqs
  alts' <- mkAlts v vs ty1 ty2 err different
  let viewExpr = HsApp EpAnnNotUsed e (noLocA (HsVar noExtField (noLocA v)))
      pty = hsLPatType p
  as <- viewAlts vs ty2 err same
  let mgtc = MatchGroupTc [Scaled Many pty] ty2
      mkMG others = MG mgtc (noLocA (as ++ others)) Generated
      mkCse others = HsCase noExtField (noLocA viewExpr) (mkMG others)
      mkGrhs = GRHS EpAnnNotUsed []
      mkGrhss ex =
        GRHSs
          emptyComments
          [noLoc (mkGrhs ex)]
          (EmptyLocalBinds noExtField)
      mkWild :: LHsExpr GhcTc -> Match GhcTc (LHsExpr GhcTc)
      mkWild ex = Match EpAnnNotUsed CaseAlt [noLocA (WildPat pty)] (mkGrhss ex)
  case alts' of
    Left remain ->
      Right . noLocA <$> matchExpr (mkCse [noLocA (mkWild (noLocA ex))])
      where
        ex = HsCase noExtField (noLocA (HsVar noExtField (noLocA v))) mgI
        mgtcI = MatchGroupTc [Scaled Many ty1] ty2
        mgI = MG mgtcI (noLocA remain) Generated
    Right ex ->
      Right . noLocA <$> matchExpr (mkCse [noLocA (mkWild ex)])
mkAlts v vs ty1 ty2 err eqs@((p, alt) : _)
  | L _ c@ConPat {} <- p,
    L _ (RealDataCon dc) <- pat_con c,
    isNewTyCon (dataConTyCon dc) = do
      (p', [v'], _) <- flattenPat p
      let patTy = Scaled Many (hsLPatType p')
      let xty = Scaled Many (varType v')
      x <- freshVar xty
      fresh <- freshVar patTy
      -- create: let x = (\a -> case a of p' -> v') v in rhs
      let grhs = GRHS EpAnnNotUsed [] (noLocA (HsVar noExtField (noLocA v')))
          rhs = GRHSs emptyComments [noLoc grhs] (EmptyLocalBinds noExtField)
          match = Match EpAnnNotUsed CaseAlt [p'] rhs
          mgtc = MatchGroupTc [patTy] (varType v')
          mg = MG mgtc (noLocA [noLocA match]) Generated
          cseVar = HsVar noExtField (noLocA fresh)
          cse = noLocA (HsCase noExtField (noLocA cseVar) mg)
          lam = mkLam (noLocA fresh) patTy cse (varType v')
          lamApp = mkHsApp lam (noLocA (HsVar noExtField (noLocA v)))

      eqs' <- mapM flattenEq [(p, alt)]
      bdy <- compileMatching (x : vs) ty2 eqs' err
      let letE = mkSimpleLet NonRecursive lamApp bdy x (varType x)
      return $ Right $ noLocA letE
  | otherwise = do
      -- Assuming the first pattern is not a lazy pattern,
      -- we need every alternative with the same constructor as the first one
      -- If that is already a lazy pattern, it is assumed to be matching.
      -- A lazy pattern gets desugared to a let-bound pattern, which then gets
      -- desugared to selector functions
      let (strict, rest) = span (isNoLazyPat . fst) eqs
      let (with, without) = partition (sameTopCon p . fst) strict
      if isNoLazyPat p
        then do
          (p', vs', _) <- flattenPat p
          alts' <- mkAlts v vs ty1 ty2 err (rest ++ without)
          eqs' <- mapM flattenEq with
          bdy <- compileMatching (vs' ++ vs) ty2 eqs' err
          return (mkNaturalOrSimpleAlt ty1 ty2 v bdy p' alts')
        else do
          -- compile any remaining patterns
          bdy <- compileMatching vs ty2 [alt] err
          -- construct new pattern binding and translate that
          let vE = noLocA (HsVar noExtField (noLocA v))
          letExpr <- matchExpr (mkSimplePatLet ty1 vE p bdy)
          -- return just this expression to be either placed
          -- in a new wildcard branch, or to completely replace the case,
          -- iff it is the first alternative.
          -- All remaining patterns would be overlapping, so we ignore them
          return (Right (noLocA letExpr))
mkAlts _ _ ty1 _ err [] =
  let grhs = GRHS EpAnnNotUsed [] err
      grhss = GRHSs emptyComments [noLoc grhs] (EmptyLocalBinds noExtField)
      alt = Match EpAnnNotUsed CaseAlt [noLocA (WildPat ty1)] grhss
   in return (Left [noLocA alt])

viewAlts ::
  [Var] ->
  Type ->
  LHsExpr GhcTc ->
  [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))] ->
  TcM [LMatch GhcTc (LHsExpr GhcTc)]
viewAlts _ _ _ [] = return []
viewAlts
  vs
  ty2
  err
  ( curr@(L _ (ViewPat _ _ p), L l _)
      : rest
    ) = do
    (p', vs', _) <- flattenPat p
    curr' <- flattenEq curr
    bdy <- compileMatching (vs' ++ vs) ty2 [curr'] err
    let grhs = GRHS EpAnnNotUsed [] bdy
    let grhss = GRHSs emptyComments [noLoc grhs] (EmptyLocalBinds noExtField)
    let a = L l (Match EpAnnNotUsed CaseAlt [p'] grhss)
    restAlts <- viewAlts vs ty2 err rest
    return (a : restAlts)
viewAlts _ _ _ alts =
  panicAny "Unexpected pattern when desugaring ViewPattern" alts

-- Desugars natural patterns (e.g. overloaded literals)
-- and string patterns into if-then-else.
-- Any other pattern is translated into a normal case-expression
mkNaturalOrSimpleAlt ::
  Type ->
  Type ->
  Var ->
  LHsExpr GhcTc ->
  LPat GhcTc ->
  Either [LMatch GhcTc (LHsExpr GhcTc)] (LHsExpr GhcTc) ->
  Either [LMatch GhcTc (LHsExpr GhcTc)] (LHsExpr GhcTc)
mkNaturalOrSimpleAlt ty1 ty2 v e1 p@(L l (LitPat _ lit)) alts
  | isStringLit lit =
      let overLit =
            OverLit
              (OverLitTc False strTy)
              (HsIsString (stringLitSourceText lit) (stringLitFastString lit))
              (HsLit EpAnnNotUsed lit)
          eqSynExpr =
            SyntaxExprTc
              ( HsVar
                  noExtField
                  ( noLocA
                      ( mkGlobalVar
                          VanillaId
                          eqStringName
                          (mkVisFunTyMany strTy (mkVisFunTyMany strTy boolTy))
                          vanillaIdInfo
                      )
                  )
              )
              [WpHole, WpHole]
              WpHole
          nPat = NPat strTy (L (getLocA p) overLit) Nothing eqSynExpr
       in mkNaturalOrSimpleAlt ty1 ty2 v e1 (L l nPat) alts
  where
    strTy = mkTyConApp listTyCon [mkTyConTy charTyCon]
mkNaturalOrSimpleAlt
  ty1
  ty2
  v
  e1
  ( L
      _
      ( NPat
          _
          (L _ (OverLit _ _ l))
          neg
          (SyntaxExprTc eq [argWQ1, argWQ2] resWQ)
        )
    )
  alts =
    let ve = HsVar noExtField (noLocA v)
        l' = case neg of
          Just (SyntaxExprTc en [argWN] resWN) ->
            mkHsWrap
              resWN
              ( HsApp
                  EpAnnNotUsed
                  (noLocA en)
                  (noLocA (mkHsWrap argWN l))
              )
          _ -> l
        if1 =
          noLocA
            ( mkHsWrap
                resWQ
                ( HsApp
                    EpAnnNotUsed
                    ( noLocA
                        ( HsApp
                            EpAnnNotUsed
                            (noLocA eq)
                            (noLocA (mkHsWrap argWQ1 l'))
                        )
                    )
                    (noLocA (mkHsWrap argWQ2 ve))
                )
            )
        if2 = e1
        if3 = case alts of
          Left as ->
            let mgtc = MatchGroupTc [Scaled Many ty1] ty2
                mg = MG mgtc (noLocA as) Generated
             in noLocA (HsCase noExtField (noLocA ve) mg)
          Right e2 -> e2
     in Right (noLocA (HsIf noExtField if1 if2 if3))
mkNaturalOrSimpleAlt _ _ _ e1 p (Left as) =
  Left (noLocA (mkSimpleAlt CaseAlt e1 [p]) : as)
mkNaturalOrSimpleAlt ty1 _ _ e1 p (Right e2) =
  Left
    [ noLocA (mkSimpleAlt CaseAlt e1 [p]),
      noLocA (mkSimpleAlt CaseAlt e2 [noLocA (WildPat ty1)])
    ]

preprocessAs ::
  Var ->
  (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc)) ->
  (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))
preprocessAs v (L _ (AsPat _ (L _ v') p), m) =
  let m' = substitute v v' m
   in preprocessAs v (p, m')
preprocessAs v (L l (LazyPat x p), m) =
  first (L l . LazyPat x) (preprocessAs v (p, m))
preprocessAs v (L l (BangPat x p), m) =
  first (L l . BangPat x) (preprocessAs v (p, m))
preprocessAs v (L l (SigPat x p ty), m) =
  first (L l . flip (SigPat x) ty) (preprocessAs v (p, m))
preprocessAs v (L _ (ParPat _ p), m) =
  preprocessAs v (p, m)
preprocessAs _ (p, m) = (p, m)

flattenEq ::
  (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc)) ->
  TcM (LMatch GhcTc (LHsExpr GhcTc))
flattenEq (p, L l (Match a b ps c)) = do
  (_, _, ps') <- flattenPat p
  return (L l (Match a b (ps' ++ ps) c))

-- Flatten a pattern into the top constructor pattern
-- and the sub-patterns with their new variables
flattenPat :: LPat GhcTc -> TcM (LPat GhcTc, [Var], [LPat GhcTc])
flattenPat p@(L _ (WildPat _)) = return (p, [], [])
flattenPat p@(L _ (VarPat _ _)) = return (p, [], [])
flattenPat (L l (LazyPat x p)) =
  (\(a, b, c) -> (L l (LazyPat x a), b, c)) <$> flattenPat p
flattenPat (L l (AsPat x v p)) =
  (\(a, b, c) -> (L l (AsPat x v a), b, c)) <$> flattenPat p
flattenPat (L l (ParPat x p)) =
  (\(a, b, c) -> (L l (ParPat x a), b, c)) <$> flattenPat p
flattenPat (L l (BangPat x p)) =
  (\(a, b, c) -> (L l (BangPat x a), b, c)) <$> flattenPat p
flattenPat p@(L _ (ListPat (ListPatTc _ (Just _)) _)) = do
  reportError
    ( mkMsgEnvelope
        (getLocA p)
        neverQualify
        "Overloaded lists are not supported by the plugin"
    )
  failIfErrsM
  return (p, [], [])
flattenPat (L l (ListPat (ListPatTc ty Nothing) [])) = do
  let dc = noLocA (RealDataCon nilDataCon)
  let res =
        L
          l
          ( ConPat
              (ConPatTc [ty] [] [] (EvBinds emptyBag) WpHole)
              dc
              (PrefixCon [] [])
          )
  return (res, [], [])
flattenPat (L l (ListPat tc@(ListPatTc ty Nothing) (x : xs))) = do
  v1 <- mkVar ty
  v2 <- mkVar (mkTyConApp listTyCon [ty])
  let dc = noLocA (RealDataCon consDataCon)
  let c =
        PrefixCon
          []
          [ noLocA (VarPat noExtField (noLocA v1)),
            noLocA (VarPat noExtField (noLocA v2))
          ]
  let res = L l (ConPat (ConPatTc [ty] [] [] (EvBinds emptyBag) WpHole) dc c)
  return (res, [v1, v2], [x, noLocA (ListPat tc xs)])
flattenPat (L l (TuplePat tys ps b)) =
  (\vs -> (L l (TuplePat tys (map mkVarPat vs) b), vs, ps))
    <$> mapM mkVar tys
flattenPat (L l (SumPat tys p t a)) =
  ( \v ->
      ( L l (SumPat tys (noLocA (VarPat noExtField (noLocA v))) t a),
        [v],
        [p]
      )
  )
    <$> mkVar (tys !! t)
flattenPat (L l cn@ConPat {}) =
  let argtys = cpt_arg_tys (pat_con_ext cn)
      cty = conLikeInstOrigArgTys (unLoc (pat_con cn)) argtys
   in (\(args', vs, c) -> (L l (cn {pat_args = args'}), vs, c))
        <$> flattenConPatDetails (pat_args cn) cty argtys
flattenPat (L _ (ViewPat _ _ p')) = flattenPat p'
-- seems weird, cut the matching on the view is handled somewhere else.
-- We are only interested in what is left to match on the inner patttern
flattenPat p@(L _ (SplicePat _ _)) = do
  reportError
    ( mkMsgEnvelope
        (getLocA p)
        neverQualify
        "Template Haskell is not supported by the plugin"
    )
  failIfErrsM
  return (p, [], [])
flattenPat p@(L _ (LitPat _ _)) = return (p, [], [])
flattenPat p@(L _ NPat {}) = return (p, [], [])
flattenPat p@(L _ NPlusKPat {}) = return (p, [], [])
flattenPat (L l (SigPat x p ty)) =
  (\(a, b, c) -> (L l (SigPat x a ty), b, c)) <$> flattenPat p
flattenPat (L l (XPat (CoPat co p w))) =
  (\(a, b, c) -> (L l (XPat (CoPat co (unLoc a) w)), b, c))
    <$> flattenPat (noLocA p)

flattenConPatDetails ::
  HsConPatDetails GhcTc ->
  [Scaled Type] ->
  [Type] ->
  TcM (HsConPatDetails GhcTc, [Var], [LPat GhcTc])
flattenConPatDetails (PrefixCon _ args) tys _ = do
  vs <- mapM (\(Scaled _ ty) -> mkVar ty) tys
  let vsp = map (noLocA . VarPat noExtField . noLocA) vs
  return (PrefixCon [] vsp, vs, args)
flattenConPatDetails (RecCon (HsRecFields flds d)) _ tys = do
  (flds', vs, args) <- unzip3 <$> mapM (flattenRecField tys) flds
  return (RecCon (HsRecFields flds' d), concat vs, concat args)
flattenConPatDetails (InfixCon a1 a2) tys _ = do
  [v1, v2] <- mapM (\(Scaled _ ty) -> mkVar ty) tys
  let p1 = mkVarPat v1
      p2 = mkVarPat v2
  return (InfixCon p1 p2, [v1, v2], [a1, a2])

flattenRecField ::
  [Type] ->
  LHsRecField GhcTc (LPat GhcTc) ->
  TcM (LHsRecField GhcTc (LPat GhcTc), [Var], [LPat GhcTc])
flattenRecField tys (L l (HsRecField x idt p pn)) = do
  let ty = funResultTy (instantiateWith tys (varType (extFieldOcc (unLoc idt))))
  v <- mkVar ty
  let p' = noLocA (VarPat noExtField (noLocA v))
  return (L l (HsRecField x idt p' pn), [v], [p])

mkVar :: Type -> TcM Var
mkVar ty = do
  u <- getUniqueM
  return $
    mkLocalVar VanillaId (mkSystemName u (mkVarOcc "p")) Many ty vanillaIdInfo

substitute :: Data a => Var -> Var -> a -> a
substitute new old = everywhere (mkT substVar)
  where
    u = varName old
    substVar v = if varName v == u then new else v

getPatternAt ::
  Int ->
  LMatch GhcTc (LHsExpr GhcTc) ->
  (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))
getPatternAt n (L l (Match x c ps lcl)) =
  let (p, rs) = getAndDrop n ps
   in (p, L l (Match x c rs lcl))

getAndDrop :: Int -> [a] -> (a, [a])
getAndDrop _ [] = panicAnyUnsafe "No pattern at the specified index" ()
getAndDrop 0 (x : xs) = (x, xs)
getAndDrop n (x : xs) =
  let (y, ys) = getAndDrop (n - 1) xs
   in (y, x : ys)

isSamePatternType :: LPat GhcTc -> LPat GhcTc -> Bool
isSamePatternType p1 p2 =
  (isConstrPat p1 && isConstrPat p2)
    || (isVarPat p1 && isVarPat p2)

isConstrPat :: LPat GhcTc -> Bool
isConstrPat (L _ (WildPat _)) = False
isConstrPat (L _ (VarPat _ _)) = False
isConstrPat (L _ (LazyPat _ p)) = isConstrPat p
isConstrPat (L _ (AsPat _ _ p)) = isConstrPat p
isConstrPat (L _ (ParPat _ p)) = isConstrPat p
isConstrPat (L _ (BangPat _ p)) = isConstrPat p
isConstrPat (L _ (ListPat _ _)) = True
isConstrPat (L _ TuplePat {}) = True
isConstrPat (L _ SumPat {}) = True
isConstrPat (L _ ConPat {}) = True
isConstrPat (L _ ViewPat {}) = True -- <- Surprisingly, this works.
isConstrPat (L _ (SplicePat _ _)) = False
isConstrPat (L _ (LitPat _ _)) = True
isConstrPat (L _ NPat {}) = True
isConstrPat (L _ NPlusKPat {}) = False
isConstrPat (L _ (SigPat _ p _)) = isConstrPat p
isConstrPat (L _ (XPat (CoPat _ p _))) = isConstrPat (noLocA p)

-- HACK: since Int# is "invisible" to the lifting and any I# constructor for Int is removed,
-- this function has to see through any I# constructor
isVarPat :: LPat GhcTc -> Bool
isVarPat (L _ (WildPat _)) = True
isVarPat (L _ (VarPat _ _)) = True
isVarPat (L _ (LazyPat _ p)) = isVarPat p
isVarPat (L _ (AsPat _ _ p)) = isVarPat p
isVarPat (L _ (ParPat _ p)) = isVarPat p
isVarPat (L _ (BangPat _ p)) = isVarPat p
isVarPat (L _ (ListPat _ _)) = False
isVarPat (L _ TuplePat {}) = False
isVarPat (L _ SumPat {}) = False
isVarPat (L _ p@ConPat {})
  | L _ (RealDataCon c) <- pat_con p,
    c == intDataCon,
    [arg] <- hsConPatArgs (pat_args p) =
      isVarPat arg
  | otherwise = False
isVarPat (L _ ViewPat {}) = False
isVarPat (L _ (SplicePat _ _)) = False
isVarPat (L _ (LitPat _ _)) = False
isVarPat (L _ NPat {}) = False
isVarPat (L _ NPlusKPat {}) = False
isVarPat (L _ (SigPat _ p _)) = isVarPat p
isVarPat (L _ (XPat (CoPat _ p _))) = isVarPat (noLocA p)

isBangPat :: LPat GhcTc -> Bool
isBangPat (L _ (WildPat _)) = False
isBangPat (L _ (VarPat _ _)) = False
isBangPat (L _ (LazyPat _ _)) = False
isBangPat (L _ (AsPat _ _ p)) = isBangPat p
isBangPat (L _ (ParPat _ p)) = isBangPat p
isBangPat (L _ (BangPat _ _)) = True
isBangPat (L _ (ListPat _ _)) = False
isBangPat (L _ TuplePat {}) = False
isBangPat (L _ SumPat {}) = False
isBangPat (L _ ConPat {}) = False
isBangPat (L _ ViewPat {}) = False
isBangPat (L _ (SplicePat _ _)) = False
isBangPat (L _ (LitPat _ _)) = False
isBangPat (L _ NPat {}) = False
isBangPat (L _ NPlusKPat {}) = False
isBangPat (L _ (SigPat _ p _)) = isBangPat p
isBangPat (L _ (XPat (CoPat _ p _))) = isBangPat (noLocA p)

isNoLazyPat :: LPat GhcTc -> Bool
isNoLazyPat (L _ (WildPat _)) = True
isNoLazyPat (L _ (VarPat _ _)) = True
isNoLazyPat (L _ (LazyPat _ _)) = False
isNoLazyPat (L _ (AsPat _ _ p)) = isNoLazyPat p
isNoLazyPat (L _ (ParPat _ p)) = isNoLazyPat p
isNoLazyPat (L _ (BangPat _ p)) = isNoLazyPat p
isNoLazyPat (L _ (ListPat _ _)) = True
isNoLazyPat (L _ TuplePat {}) = True
isNoLazyPat (L _ SumPat {}) = True
isNoLazyPat (L _ ConPat {}) = True
isNoLazyPat (L _ ViewPat {}) = True
isNoLazyPat (L _ (SplicePat _ _)) = True
isNoLazyPat (L _ (LitPat _ _)) = True
isNoLazyPat (L _ NPat {}) = True
isNoLazyPat (L _ NPlusKPat {}) = True
isNoLazyPat (L _ (SigPat _ p _)) = isNoLazyPat p
isNoLazyPat (L _ (XPat (CoPat _ p _))) = isNoLazyPat (noLocA p)

-- this is more delicate than it seems,
-- as we have to make sure that ListPat and TuplePat are "the same" as their
-- explicit constructors
sameTopCon :: LPat GhcTc -> LPat GhcTc -> Bool
sameTopCon (L _ (WildPat _)) (L _ (WildPat _)) = True
sameTopCon (L _ (VarPat _ _)) (L _ (VarPat _ _)) = True
sameTopCon (L _ (LazyPat _ _)) (L _ (LazyPat _ _)) = True
sameTopCon (L _ AsPat {}) (L _ AsPat {}) = True
sameTopCon (L _ (ParPat _ p1)) p2 = sameTopCon p1 p2
sameTopCon p1 (L _ (ParPat _ p2)) = sameTopCon p1 p2
sameTopCon (L _ (BangPat _ _)) (L _ (BangPat _ _)) = True
sameTopCon (L _ (ListPat _ ps1)) (L _ (ListPat _ ps2)) = null ps1 == null ps2
sameTopCon
  (L _ (ListPat _ ps1))
  (L _ ConPat {pat_con = L _ (RealDataCon c)}) =
    null ps1
      == (c == nilDataCon)
sameTopCon
  (L _ ConPat {pat_con = L _ (RealDataCon c)})
  (L _ (ListPat _ ps1)) =
    null ps1
      == (c == nilDataCon)
sameTopCon (L _ TuplePat {}) (L _ TuplePat {}) = True
sameTopCon
  (L _ (TuplePat _ ps b))
  (L _ ConPat {pat_con = L _ (RealDataCon c)}) = c == tc
    where
      tc = tupleDataCon b (length ps)
sameTopCon
  (L _ ConPat {pat_con = L _ (RealDataCon c)})
  (L _ (TuplePat _ ps b)) = c == tc
    where
      tc = tupleDataCon b (length ps)
sameTopCon
  (L _ (SumPat _ _ t1 _))
  (L _ (SumPat _ _ t2 _)) = t1 == t2
sameTopCon
  (L _ (ConPat _ (L _ c1) _))
  (L _ (ConPat _ (L _ c2) _)) = sameConLike c1 c2
sameTopCon (L _ (ViewPat t1 e1 _)) (L _ (ViewPat t2 e2 _)) = viewLExprEq x1 x2
  where
    (x1, x2) = ((e1, t1), (e2, t2))
sameTopCon (L _ (SplicePat _ _)) (L _ (SplicePat _ _)) = False
sameTopCon (L _ (LitPat _ l1)) (L _ (LitPat _ l2)) = l1 == l2
sameTopCon
  (L _ (NPat _ (L _ l1) _ _))
  (L _ (NPat _ (L _ l2) _ _)) = l1 == l2
sameTopCon
  (L _ (NPlusKPat _ _ (L _ l1) _ _ _))
  (L _ (NPlusKPat _ _ (L _ l2) _ _ _)) = l1 == l2
sameTopCon (L _ (SigPat _ p1 _)) p2 = sameTopCon p1 p2
sameTopCon p1 (L _ (SigPat _ p2 _)) = sameTopCon p1 p2
sameTopCon p1 (L _ (XPat (CoPat _ p2 _))) = sameTopCon p1 p2'
  where
    p2' = noLocA p2
sameTopCon (L _ (XPat (CoPat _ p1 _))) p2 = sameTopCon p1' p2
  where
    p1' = noLocA p1
sameTopCon _ _ = False

sameConLike :: ConLike -> ConLike -> Bool
sameConLike (RealDataCon c1) (RealDataCon c2) = dataConName c1 == dataConName c2
sameConLike (PatSynCon c1) (PatSynCon c2) = patSynName c1 == patSynName c2
sameConLike _ _ = False

isFunCtxt :: HsMatchContext a -> Bool
isFunCtxt FunRhs {} = True
isFunCtxt _ = False

errorExpr :: HsMatchContext GhcRn -> Type -> TcM (LHsExpr GhcTc)
errorExpr (FunRhs (L _ idt) _ _) ty =
  mkErrorWith ty $
    "Non-exhaustive patterns in function: "
      ++ occNameString (occName idt)
errorExpr LambdaExpr ty =
  mkErrorWith ty "Non-exhaustive patterns in lambda abstraction"
errorExpr CaseAlt ty =
  mkErrorWith ty "Non-exhaustive patterns in case expression"
errorExpr IfAlt ty =
  mkErrorWith ty "Non-exhaustive guard alternatives in multi-way if"
errorExpr (ArrowMatchCtxt _) ty =
  mkErrorWith ty "Non-exhaustive patterns in an arrow expression"
errorExpr PatBindRhs ty =
  mkErrorWith ty "Non-exhaustive patterns in a pattern binding"
errorExpr PatBindGuards ty =
  mkErrorWith ty "Non-exhaustive guard alternatives in a pattern binding"
errorExpr (StmtCtxt _) ty =
  mkErrorWith ty "Non-exhaustive patterns in a list comprehension or do-notation"
errorExpr ThPatSplice ty =
  mkErrorWith ty "Non-exhaustive patterns in a TemplateHaskell pattern splice "
errorExpr ThPatQuote ty =
  mkErrorWith ty "Non-exhaustive patterns in a TemplateHaskell pattern quotation"
errorExpr PatSyn ty =
  mkErrorWith ty "Non-exhaustive patterns in a pattern synonym declaration"
errorExpr RecUpd _ =
  panicAny "Unexpected RecUpd context of a pattern matching" ()

-- Introduced in dsExpr only

errorStrStmt :: HsStmtContext GhcRn -> LHsExpr GhcTc
errorStrStmt ListComp =
  mkErrorLit "Non-exhaustive patterns in a List comprehension"
errorStrStmt MonadComp =
  mkErrorLit "Non-exhaustive patterns in a Monad comprehension"
errorStrStmt (DoExpr Nothing) =
  mkErrorLit "Non-exhaustive patterns in a do expression"
errorStrStmt (DoExpr (Just _)) =
  mkErrorLit "Non-exhaustive patterns in a qualified do expression"
errorStrStmt (MDoExpr Nothing) =
  mkErrorLit "Non-exhaustive patterns in a recursive do expression"
errorStrStmt (MDoExpr (Just _)) =
  mkErrorLit "Non-exhaustive patterns in a qualified, recursive do expression"
errorStrStmt ArrowExpr =
  mkErrorLit "Non-exhaustive patterns in an arrow expression"
errorStrStmt GhciStmtCtxt =
  mkErrorLit "Non-exhaustive patterns in a GHCi statement"
errorStrStmt (PatGuard _) =
  panicAnyUnsafe "Unexpected pattern guard context in do-notation" ()
errorStrStmt (ParStmtCtxt _) =
  mkErrorLit "Non-exhaustive patterns in a branch of a parallel do statement"
errorStrStmt (TransStmtCtxt _) =
  mkErrorLit "Non-exhaustive patterns in a branch of a transform statement"

mkErrorLit :: String -> LHsExpr GhcTc
mkErrorLit = noLocA . HsLit EpAnnNotUsed . HsString NoSourceText . mkFastString

mkErrorWith :: Type -> String -> TcM (LHsExpr GhcTc)
mkErrorWith ty s = do
  hscEnv <- getTopEnv
  Found _ mdl <- liftIO $
    findImportedModule hscEnv (mkModuleName "Plugin.BuiltIn") Nothing
  errId <- lookupId =<< lookupOrig mdl ( mkVarOcc "failFLStr" )
  errId' <- setVarName errId <$> externaliseName mdl (varName errId)
  return (noLocA (HsApp noAnn
    (noLocA (XExpr (WrapExpr (HsWrap (WpTyApp ty) (HsVar noExtField (noLocA errId'))))))
    (mkErrorLit s)))
