-- |
-- Module      : Plugin.Trans.LExprEQ
-- Description : Weak comparison of expressions for views
-- Copyright   :
--   (c) The University of Glasgow 2006
--   (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
--
-- This module provides a conservative function to compare expressions
-- from view pattern for their compatibility to be used together.
-- The function is copied from module GHC.HsToCore.Match from the GHC project.
module Plugin.Trans.LExprEQ where

import GHC.Core.TyCo.Rep
import GHC.Hs.Expr
import GHC.Hs.Extension
import GHC.Hs.Lit
import GHC.Plugins
import GHC.Tc.Types.Evidence
import Prelude (Bool (..), and, (&&), (==))

viewLExprEq :: (LHsExpr GhcTc, Type) -> (LHsExpr GhcTc, Type) -> Bool
viewLExprEq (e1Orig, _) (e2Orig, _) = lexp e1Orig e2Orig
  where
    lexp :: LHsExpr GhcTc -> LHsExpr GhcTc -> Bool
    lexp e e' = exp (unLoc e) (unLoc e')

    ---------
    exp :: HsExpr GhcTc -> HsExpr GhcTc -> Bool
    -- real comparison is on HsExpr's
    -- strip parens
    exp (HsPar _ (L _ e)) e' = exp e e'
    exp e (HsPar _ (L _ e')) = exp e e'
    -- because the expressions do not necessarily have the same type,
    -- we have to compare the wrappers
    exp (XExpr (WrapExpr (HsWrap h e))) (XExpr (WrapExpr (HsWrap h' e'))) =
      wrap h h' && exp e e'
    exp (XExpr (ExpansionExpr (HsExpanded _ b))) (XExpr (ExpansionExpr (HsExpanded _ b'))) =
      exp b b'
    exp (HsVar _ i) (HsVar _ i') = i == i'
    exp (HsConLikeOut _ c) (HsConLikeOut _ c') = c == c'
    -- the instance for IPName derives using the id, so this works if the
    -- above does
    exp (HsIPVar _ i) (HsIPVar _ i') = i == i'
    exp (HsOverLabel l x) (HsOverLabel l' x') = l == l' && x == x'
    exp (HsOverLit _ l) (HsOverLit _ l') =
      -- Overloaded lits are equal if they have the same type
      -- and the data is the same.
      -- this is coarser than comparing the SyntaxExpr's in l and l',
      -- which resolve the overloading (e.g., fromInteger 1),
      -- because these expressions get written as a bunch of different variables
      -- (presumably to improve sharing)
      eqType (overLitType l) (overLitType l') && l == l'
    exp (HsApp _ e1 e2) (HsApp _ e1' e2') = lexp e1 e1' && lexp e2 e2'
    -- the fixities have been straightened out by now, so it's safe
    -- to ignore them?
    exp (OpApp _ l o ri) (OpApp _ l' o' ri') =
      lexp l l' && lexp o o' && lexp ri ri'
    exp (NegApp _ e n) (NegApp _ e' n') = lexp e e' && syn_exp n n'
    exp (SectionL _ e1 e2) (SectionL _ e1' e2') =
      lexp e1 e1' && lexp e2 e2'
    exp (SectionR _ e1 e2) (SectionR _ e1' e2') =
      lexp e1 e1' && lexp e2 e2'
    exp (ExplicitTuple _ es1 _) (ExplicitTuple _ es2 _) =
      eq_list tup_arg es1 es2
    exp (ExplicitSum _ _ _ e) (ExplicitSum _ _ _ e') = lexp e e'
    exp (HsIf _ e e1 e2) (HsIf _ e' e1' e2') =
      lexp e e' && lexp e1 e1' && lexp e2 e2'
    -- Enhancement: could implement equality for more expressions
    --   if it seems useful
    -- But no need for HsLit, ExplicitList, ExplicitTuple,
    -- because they cannot be functions
    exp _ _ = False

    ---------
    syn_exp :: SyntaxExpr GhcTc -> SyntaxExpr GhcTc -> Bool
    syn_exp
      ( SyntaxExprTc
          { syn_expr = expr1,
            syn_arg_wraps = arg_wraps1,
            syn_res_wrap = res_wrap1
          }
        )
      ( SyntaxExprTc
          { syn_expr = expr2,
            syn_arg_wraps = arg_wraps2,
            syn_res_wrap = res_wrap2
          }
        ) =
        exp expr1 expr2
          && and (zipWithEqual "viewLExprEq" wrap arg_wraps1 arg_wraps2)
          && wrap res_wrap1 res_wrap2
    syn_exp NoSyntaxExprTc NoSyntaxExprTc = True
    syn_exp _ _ = False

    ---------
    tup_arg (Present _ e1) (Present _ e2) = lexp e1 e2
    tup_arg (Missing (Scaled _ t1)) (Missing (Scaled _ t2)) = eqType t1 t2
    tup_arg _ _ = False

    ---------
    wrap :: HsWrapper -> HsWrapper -> Bool
    -- Conservative, in that it demands that wrappers be
    -- syntactically identical and doesn't look under binders
    --
    -- Coarser notions of equality are possible
    -- (e.g., reassociating compositions,
    --        equating different ways of writing a coercion)
    wrap WpHole WpHole = True
    wrap (WpCompose w1 w2) (WpCompose w1' w2') = wrap w1 w1' && wrap w2 w2'
    wrap (WpFun w1 w2 _ _) (WpFun w1' w2' _ _) = wrap w1 w1' && wrap w2 w2'
    wrap (WpCast co) (WpCast co') = co `eqCoercion` co'
    wrap (WpEvApp et1) (WpEvApp et2) = et1 `ev_term` et2
    wrap (WpTyApp t) (WpTyApp t') = eqType t t'
    -- Enhancement: could implement equality for more wrappers
    --   if it seems useful (lams and lets)
    wrap _ _ = False

    ---------
    ev_term :: EvTerm -> EvTerm -> Bool
    ev_term (EvExpr (Var a)) (EvExpr (Var b)) = a == b
    ev_term (EvExpr (Coercion a)) (EvExpr (Coercion b)) = a `eqCoercion` b
    ev_term _ _ = False

    ---------
    eq_list :: (a -> a -> Bool) -> [a] -> [a] -> Bool
    eq_list _ [] [] = True
    eq_list _ [] (_ : _) = False
    eq_list _ (_ : _) [] = False
    eq_list eq (x : xs) (y : ys) = eq x y && eq_list eq xs ys
