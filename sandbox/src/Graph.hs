{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

-- Example from "Principles of Inverse Computation and the Universal Resolving Algorithm"

module Graph where

data Node = A | B | C | D
  deriving (Show)

--TODO: Remove quick fix
instance Eq Node where
  A == A = True
  B == B = True
  C == C = True
  D == D = True
  _ == _ = False

type Graph = [(Node, [Node])]

type Path = [Node]

isWalk :: Graph -> Path -> Bool
isWalk g p = isWalk' p []
  where isInGraph x = x `elem` map fst g
        isReachableFrom x y = case lookup y g of
          Just ys -> x `elem` ys
        isWalk' []     _      = True
        isWalk' (x:xs) []     | isInGraph x = isWalk' xs [x]
        isWalk' (x:xs) (y:ys) | isInGraph x = x `notElem` (y:ys) && isReachableFrom x y && isWalk' xs (x:y:ys)

graph :: Graph
graph = [ (A, [B,C])
        , (B, [D])
        , (C, [])
        , (D, [A,C])]

-- Test with:
-- $(partialInv 'isWalk True [0]) graph True (should result in 17 cycle-free walks)
-- $(partialInv 'isWalk True [0]) graph False (should result in an infinite number of cyclic walks)
-- $(partialInv 'isWalk False [0]) graph False (should result in 52/54 representants of cyclic walks)


{-
[Solo "",Solo "a",Solo "b",Solo "c",Solo "d",Solo "ab",Solo "ac",Solo "bd",Solo "da",Solo "dc",Solo "abd",Solo "dab",Solo "bda",Solo "dac",Solo "bdc",Solo "abdc",Solo "bdac"]

[Solo [],Solo [A],Solo [B],Solo [C],Solo [D],Solo [A,B],Solo [A,C],Solo [B,D],Solo [D,C],Solo [A,B,D],Solo [B,D,C],Solo [A,B,D,C]]

Missing: DA, DAB, BDA, DAC, BDAC
Common: subpath: DA

:set -fplugin-opt Plugin.InversionPlugin:dump-pattern-matched
-}

{-
DumpPatternMatched
------------------
[$tcNodeFL
   = TyCon
       11284165957374241463## 16645910325213545416## $trModuleFL
       (TrNameS "Node"#) 0 krep$*,
 $tc'AFL
   = TyCon
       4537433208837587864## 7791496361309316072## $trModuleFL
       (TrNameS "'A"#) 0 $krepFL,
 $tc'BFL
   = TyCon
       11474119812166019021## 11551656710148742089## $trModuleFL
       (TrNameS "'B"#) 0 $krepFL,
 $tc'CFL
   = TyCon
       9405346803224519353## 7848011944899274365## $trModuleFL
       (TrNameS "'C"#) 0 $krepFL,
 $tc'DFL
   = TyCon
       3393095094534396843## 18361491967046977222## $trModuleFL
       (TrNameS "'D"#) 0 $krepFL,
 $tcNodeFLa1LXnFL
   = TyCon
       4698922546702019123## 118117829461169382## $trModuleFL
       (TrNameS "NodeFL"#) 0 $krepFL,
 $tcNodeFLa1LXnFLa1LXxFL
   = TyCon
       18096025772512244609## 11833976767588616938## $trModuleFL
       (TrNameS "'AFL"#) 1 $krepFL,
 $tcNodeFLa1LXnFLa1LXzFL
   = TyCon
       2469589479773490787## 7528601211732051057## $trModuleFL
       (TrNameS "'BFL"#) 1 $krepFL,
 $tcNodeFLa1LXnFLa1LXBFL
   = TyCon
       7263668390575027496## 212809856699563290## $trModuleFL
       (TrNameS "'CFL"#) 1 $krepFL,
 $tcNodeFLa1LXnFLa1LXDFL
   = TyCon
       8039759412058430565## 4604893809857707418## $trModuleFL
       (TrNameS "'DFL"#) 1 $krepFL,
 $krepFL [InlPrag=[~]] = KindRepVar 0,
 $krepFL [InlPrag=[~]] = KindRepFun krep$*Arr* krep$*,
 $krepFL [InlPrag=[~]]
   = KindRepTyConApp $tcNodeFLa1LXnFL ((:) $krepFL []),
 $krepFL [InlPrag=[~]] = KindRepTyConApp $tcNodeFL [],
 $trModuleFL = Module (TrNameS "main"#) (TrNameS "Graph"#),
 graphFL = [(A, [B, C]), (B, [D]), (C, []), (D, [A, C])],
 isWalkFL
   = \ fFL
       -> \ fFL
            -> let
                 isReachableFromFL
                   = \ fFL
                       -> \ fFL
                            -> let fFL = lookupFL fFL fFL
                               in
                                 case fFL of
                                   Just pFL -> elemFL fFL pFL
                                   _ -> failFLStrFL "Non-exhaustive patterns in case expression" in
               let isInGraphFL = \ fFL -> elemFL fFL mapFL fstFL fFL in
               let
                 isWalk'FL
                   = \ fFL
                       -> \ fFL
                            -> case fFL of
                                 [] -> True
                                 pFL : pFL
                                   -> case fFL of
                                        []
                                          -> if isInGraphFL pFL then
                                                 isWalk'FL pFL [pFL]
                                             else
                                                 failFLStrFL
                                                   "Non-exhaustive patterns in function: isWalk'"
                                        pFL : pFL
                                          -> if isInGraphFL pFL then
                                                 (&&#)
                                                   notElemFL pFL ((:) pFL pFL)
                                                   (&&#)
                                                     isReachableFromFL pFL pFL
                                                     isWalk'FL pFL ((:) pFL (:) pFL pFL)
                                             else
                                                 failFLStrFL
                                                   "Non-exhaustive patterns in function: isWalk'"
                                        _ -> failFLStrFL
                                               "Non-exhaustive patterns in function: isWalk'"
                                 _ -> failFLStrFL "Non-exhaustive patterns in function: isWalk'"
               in isWalk'FL fFL [],
 $dEq_a1LWt = C:Eq $c==FL $c/=FL,
 (==#)
   = \ fFL
       -> \ fFL
            -> let fFL = (dataToTag# fFL) in
               let fFL = (dataToTag# fFL) in (tagToEnum# ((==##) fFL fFL)),
 (/=#) = $dm/=,
 $dShow_a1LWL = C:Show $cshowsPrecFL $cshowFL $cshowListFL,
 showsPrecFL
   = \ fFL
       -> \ fFL
            -> case fFL of
                 A -> showStringFL "A"
                 B -> showStringFL "B"
                 C -> showStringFL "C"
                 D -> showStringFL "D"
                 _ -> failFLStrFL "Non-exhaustive patterns in function: showsPrec",
 showFL = $dmshow, showListFL = $dmshowList]
-}


{-
Graph.$tcNode
  = ghc-prim:GHC.Types.TyCon
      11284165957374241463## 16645910325213545416## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "Node"#) 0 ghc-prim:GHC.Types.krep$*
Graph.$tc'A
  = ghc-prim:GHC.Types.TyCon
      4537433208837587864## 7791496361309316072## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "'A"#) 0 $krep_a1Nn2
Graph.$tc'B
  = ghc-prim:GHC.Types.TyCon
      11474119812166019021## 11551656710148742089## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "'B"#) 0 $krep_a1Nn2
Graph.$tc'C
  = ghc-prim:GHC.Types.TyCon
      9405346803224519353## 7848011944899274365## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "'C"#) 0 $krep_a1Nn2
Graph.$tc'D
  = ghc-prim:GHC.Types.TyCon
      3393095094534396843## 18361491967046977222## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "'D"#) 0 $krep_a1Nn2
Graph.$tcNodeFLa1NmL
  = ghc-prim:GHC.Types.TyCon
      4698922546702019123## 118117829461169382## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "NodeFL"#) 0 $krep_a1Nn3
Graph.$tcNodeFLa1NmLFLa1NmV
  = ghc-prim:GHC.Types.TyCon
      18096025772512244609## 11833976767588616938## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "'AFL"#) 1 $krep_a1Nn4
Graph.$tcNodeFLa1NmLFLa1NmX
  = ghc-prim:GHC.Types.TyCon
      2469589479773490787## 7528601211732051057## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "'BFL"#) 1 $krep_a1Nn4
Graph.$tcNodeFLa1NmLFLa1NmZ
  = ghc-prim:GHC.Types.TyCon
      7263668390575027496## 212809856699563290## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "'CFL"#) 1 $krep_a1Nn4
Graph.$tcNodeFLa1NmLFLa1Nn1
  = ghc-prim:GHC.Types.TyCon
      8039759412058430565## 4604893809857707418## Graph.$trModule
      (ghc-prim:GHC.Types.TrNameS "'DFL"#) 1 $krep_a1Nn4
$krep_a1Nn5 [InlPrag=[~]] = ghc-prim:GHC.Types.KindRepVar 0
$krep_a1Nn3 [InlPrag=[~]]
  = ghc-prim:GHC.Types.KindRepFun
      ghc-prim:GHC.Types.krep$*Arr* ghc-prim:GHC.Types.krep$*
$krep_a1Nn4 [InlPrag=[~]]
  = ghc-prim:GHC.Types.KindRepTyConApp
      Graph.$tcNodeFLa1NmL ((:) $krep_a1Nn5 [])
$krep_a1Nn2 [InlPrag=[~]]
  = ghc-prim:GHC.Types.KindRepTyConApp Graph.$tcNode []
Graph.$trModule
  = ghc-prim:GHC.Types.Module
      (ghc-prim:GHC.Types.TrNameS "main"#)
      (ghc-prim:GHC.Types.TrNameS "Graph"#)
graph_a1Nkb = [(A, [B, C]), (B, [D]), (C, []), (D, [A, C])]
isWalk_a1Nkd g_a1Nj4 p_a1Nj5
  = isWalk'_a1Nj8 p_a1Nj5 []
  where
      isInGraph_a1Nj6 x_a1Nj9 = x_a1Nj9 `elem` map fst g_a1Nj4
      isReachableFrom_a1Nj7 x_a1Nja y_a1Njb
        = case lookup y_a1Njb g_a1Nj4 of
            Just ys_a1Njc -> x_a1Nja `elem` ys_a1Njc
      isWalk'_a1NkV [] _ = True
      isWalk'_a1NkV (x_a1Njd : xs_a1Nje) []
        | isInGraph_a1Nj6 x_a1Njd = isWalk'_a1NkV xs_a1Nje [x_a1Njd]
      isWalk'_a1NkV (x_a1Njf : xs_a1Njg) (y_a1Njh : ys_a1Nji)
        | isInGraph_a1Nj6 x_a1Njf
        = x_a1Njf `notElem` (y_a1Njh : ys_a1Nji)
            &&
              isReachableFrom_a1Nj7 x_a1Njf y_a1Njh
                && isWalk'_a1Nj8 xs_a1Njg (x_a1Njf : y_a1Njh : ys_a1Nji)
$dEq_a1NlR = ghc-prim:GHC.Classes.C:Eq $c==_a1NlA $c/=_a1NlL
(==_a1NlC) a_a1NjR b_a1NjS
  = case (ghc-prim:GHC.Prim.dataToTag# a_a1NjR) of
      a#_a1NjT
        -> case (ghc-prim:GHC.Prim.dataToTag# b_a1NjS) of
             b#_a1NjU
               -> (ghc-prim:GHC.Prim.tagToEnum#
                     (a#_a1NjT ghc-prim:GHC.Prim.==# b#_a1NjU))
(/=_a1NlN) = ghc-prim:GHC.Classes.$dm/= @(Node)
$dShow_a1Nm9
  = GHC.Show.C:Show $cshowsPrec_a1NlT $cshow_a1NlX $cshowList_a1Nm3
showsPrec_a1NlV _ A = showString "A"
showsPrec_a1NlV _ B = showString "B"
showsPrec_a1NlV _ C = showString "C"
showsPrec_a1NlV _ D = showString "D"
show_a1NlZ = GHC.Show.$dmshow @(Node)
showList_a1Nm5 = GHC.Show.$dmshowList @(Node)
$dHasPrimitiveInfo_a1No1
  = Plugin.Effect.Monad.C:HasPrimitiveInfo $cprimitiveInfo_a1NnV
primitiveInfo_a1NnX = Plugin.Effect.Monad.NoPrimitive
$dNarrowable_a1Non
  = Plugin.Effect.Monad.C:Narrowable $cnarrow_a1No3
narrow_a1No5
  = [do return Graph.AFL, do return Graph.BFL, do return Graph.CFL,
     do return Graph.DFL]
$dTo_a1NoD = Plugin.Effect.Monad.C:To $ctoWith_a1Nop
toWith_a1Nor tf_cH arg_cI
  = case arg_cI of
      A -> Graph.AFL
      B -> Graph.BFL
      C -> Graph.CFL
      D -> Graph.DFL
$dFrom_a1NoT = Plugin.Effect.Monad.C:From $cfrom_a1NoF
from_a1NoH arg_cJ
  = case arg_cJ of
      Graph.AFL -> A
      Graph.BFL -> B
      Graph.CFL -> C
      Graph.DFL -> D
$dMatchable_a1Npm = Plugin.Effect.Monad.C:Matchable $cmatch_a1NoV
match_a1NoX Graph.AFL A = return ()
match_a1NoX Graph.BFL B = return ()
match_a1NoX Graph.CFL C = return ()
match_a1NoX Graph.DFL D = return ()
match_a1NoX _ _ = GHC.Base.empty
$dUnifiable_a1NpX
  = Plugin.Effect.Monad.C:Unifiable $clazyUnify_a1Npo
lazyUnify_a1Npq Graph.AFL Graph.AFL = return ()
lazyUnify_a1Npq Graph.BFL Graph.BFL = return ()
lazyUnify_a1Npq Graph.CFL Graph.CFL = return ()
lazyUnify_a1Npq Graph.DFL Graph.DFL = return ()
lazyUnify_a1Npq _ _ = GHC.Base.empty
$dNormalForm_a1NqH
  = Plugin.Effect.Monad.C:NormalForm $cnormalFormWith_a1NpZ
normalFormWith_a1Nq1 nf_cK
  = \case
      Graph.AFL
        -> Plugin.Effect.Monad.FL
             (Plugin.Effect.Monad.unFL (return Graph.AFL))
      Graph.BFL
        -> Plugin.Effect.Monad.FL
             (Plugin.Effect.Monad.unFL (return Graph.BFL))
      Graph.CFL
        -> Plugin.Effect.Monad.FL
             (Plugin.Effect.Monad.unFL (return Graph.CFL))
      Graph.DFL
        -> Plugin.Effect.Monad.FL
             (Plugin.Effect.Monad.unFL (return Graph.DFL))
$dShowFree_a1Nr9
  = Plugin.Effect.Monad.C:ShowFree
      $cshowFree'_a1NqJ $cshowsFreePrec'_a1NqP
showFree'_a1NqL = Plugin.Effect.Monad.$dmshowFree' @(Node)
showsFreePrec'_a1NqR d_cL A
  = (showParen (False && (d_cL > 10)))
      ((showParen False) (showString "A"))
showsFreePrec'_a1NqR d_cM B
  = (showParen (False && (d_cM > 10)))
      ((showParen False) (showString "B"))
showsFreePrec'_a1NqR d_cN C
  = (showParen (False && (d_cN > 10)))
      ((showParen False) (showString "C"))
showsFreePrec'_a1NqR d_cO D
  = (showParen (False && (d_cO > 10)))
      ((showParen False) (showString "D"))
$dInvertible_a1NrK
  = Plugin.Effect.Monad.C:Invertible
      $cp1Invertible_a1Nrk $cp2Invertible_a1Nro $cp3Invertible_a1Nrs
      $cp4Invertible_a1Nrw $cp5Invertible_a1NrA $cp6Invertible_a1NrE
      $cp7Invertible_a1NrI
graphFL_a1NsX
  = return
      Plugin.BuiltIn.ConsFL
        return
          Plugin.BuiltIn.Tuple2FL
            (return (Graph.AFL))
            return
              Plugin.BuiltIn.ConsFL
                (return (Graph.BFL))
                return
                  Plugin.BuiltIn.ConsFL
                    (return (Graph.CFL)) return Plugin.BuiltIn.NilFL
        return
          Plugin.BuiltIn.ConsFL
            return
              Plugin.BuiltIn.Tuple2FL
                (return (Graph.BFL))
                return
                  Plugin.BuiltIn.ConsFL
                    (return (Graph.DFL)) return Plugin.BuiltIn.NilFL
            return
              Plugin.BuiltIn.ConsFL
                return
                  Plugin.BuiltIn.Tuple2FL
                    (return (Graph.CFL)) (return (Plugin.BuiltIn.NilFL))
                return
                  Plugin.BuiltIn.ConsFL
                    return
                      Plugin.BuiltIn.Tuple2FL
                        (return (Graph.DFL))
                        return
                          Plugin.BuiltIn.ConsFL
                            (return (Graph.AFL))
                            return
                              Plugin.BuiltIn.ConsFL
                                (return (Graph.CFL)) return Plugin.BuiltIn.NilFL
                    return Plugin.BuiltIn.NilFL
isWalkFL_a1Nt6
  = (return . Plugin.Effect.Monad.Func)
      (\ fFL_a1Nta
         -> (return . Plugin.Effect.Monad.Func)
              (\ fFL_a1NtC
                 -> let
                      isReachableFromFL_a1Nt7
                        = (return . Plugin.Effect.Monad.Func)
                            (\ fFL_a1Ntb
                               -> (return . Plugin.Effect.Monad.Func)
                                    (\ fFL_a1Nt9
                                       -> let
                                            fFL_a1Nt8
                                              = (Plugin.Effect.Monad.appFL
                                                   (Plugin.Effect.Monad.appFL
                                                      Plugin.BuiltIn.lookupFL fFL_a1Nt9)
                                                   fFL_a1Nta)
                                          in
                                            (>>=)
                                              fFL_a1Nt8
                                              (\case
                                                 Plugin.BuiltIn.JustFL pFL_a1Ntc
                                                   -> (Plugin.Effect.Monad.appFL
                                                         (Plugin.Effect.Monad.appFL
                                                            Plugin.BuiltIn.elemFL fFL_a1Ntb)
                                                         pFL_a1Ntc)
                                                 _ -> (Plugin.Effect.Monad.appFL
                                                         Plugin.BuiltIn.failFLStrFL
                                                         (Plugin.Effect.Monad.toFL
                                                            "Non-exhaustive patterns in case expression"))))) in
                    let
                      isInGraphFL_a1Ntf
                        = (return . Plugin.Effect.Monad.Func)
                            (\ fFL_a1Ntg
                               -> (Plugin.Effect.Monad.appFL
                                     (Plugin.Effect.Monad.appFL Plugin.BuiltIn.elemFL fFL_a1Ntg)
                                     (Plugin.Effect.Monad.appFL
                                        (Plugin.Effect.Monad.appFL
                                           Plugin.BuiltIn.mapFL Plugin.BuiltIn.fstFL)
                                        fFL_a1Nta))) in
                    let
                      isWalk'FL_a1Ntu
                        = (return . Plugin.Effect.Monad.Func)
                            (\ fFL_a1NtA
                               -> (return . Plugin.Effect.Monad.Func)
                                    (\ fFL_a1Ntz
                                       -> (>>=)
                                            fFL_a1NtA
                                            (\case
                                               Plugin.BuiltIn.NilFL
                                                 -> (return (Plugin.BuiltIn.TrueFL))
                                               pFL_a1Ntv `Plugin.BuiltIn.ConsFL` pFL_a1Ntw
                                                 -> (>>=)
                                                      fFL_a1Ntz
                                                      (\case
                                                         Plugin.BuiltIn.NilFL
                                                           -> (>>=)
                                                                (Plugin.Effect.Monad.appFL
                                                                   isInGraphFL_a1Ntf pFL_a1Ntv)
                                                                (\ f_a1Nxp
                                                                   -> if Plugin.BuiltIn.boolFLtoBool
                                                                           f_a1Nxp then
                                                                          (Plugin.Effect.Monad.appFL
                                                                             (Plugin.Effect.Monad.appFL
                                                                                isWalk'FL_a1Ntu
                                                                                pFL_a1Ntw)
                                                                             return
                                                                               Plugin.BuiltIn.ConsFL
                                                                                 pFL_a1Ntv
                                                                                 return
                                                                                   Plugin.BuiltIn.NilFL)
                                                                      else
                                                                          (Plugin.Effect.Monad.appFL
                                                                             Plugin.BuiltIn.failFLStrFL
                                                                             (Plugin.Effect.Monad.toFL
                                                                                "Non-exhaustive patterns in function: isWalk'")))
                                                         pFL_a1Ntx `Plugin.BuiltIn.ConsFL` pFL_a1Nty
                                                           -> (>>=)
                                                                (Plugin.Effect.Monad.appFL
                                                                   isInGraphFL_a1Ntf pFL_a1Ntv)
                                                                (\ f_a1NAn
                                                                   -> if Plugin.BuiltIn.boolFLtoBool
                                                                           f_a1NAn then
                                                                          (Plugin.Effect.Monad.appFL
                                                                             (Plugin.Effect.Monad.appFL
                                                                                (Plugin.BuiltIn.&&#)
                                                                                (Plugin.Effect.Monad.appFL
                                                                                   (Plugin.Effect.Monad.appFL
                                                                                      Plugin.BuiltIn.notElemFL
                                                                                      pFL_a1Ntv)
                                                                                   ((Plugin.Effect.Monad.appFL
                                                                                       (Plugin.Effect.Monad.appFL
                                                                                          ((return
                                                                                              . Plugin.Effect.Monad.Func)
                                                                                             ((\ f_a1NxF
                                                                                                 -> (return
                                                                                                       . Plugin.Effect.Monad.Func)
                                                                                                      ((\ f_a1NxG
                                                                                                          -> return
                                                                                                               (Plugin.BuiltIn.ConsFL
                                                                                                                  f_a1NxF
                                                                                                                  f_a1NxG))))))
                                                                                          pFL_a1Ntx)
                                                                                       pFL_a1Nty))))
                                                                             (Plugin.Effect.Monad.appFL
                                                                                (Plugin.Effect.Monad.appFL
                                                                                   (Plugin.BuiltIn.&&#)
                                                                                   (Plugin.Effect.Monad.appFL
                                                                                      (Plugin.Effect.Monad.appFL
                                                                                         isReachableFromFL_a1Nt7
                                                                                         pFL_a1Ntv)
                                                                                      pFL_a1Ntx))
                                                                                (Plugin.Effect.Monad.appFL
                                                                                   (Plugin.Effect.Monad.appFL
                                                                                      isWalk'FL_a1Ntu
                                                                                      pFL_a1Ntw)
                                                                                   ((Plugin.Effect.Monad.appFL
                                                                                       (Plugin.Effect.Monad.appFL
                                                                                          ((return
                                                                                              . Plugin.Effect.Monad.Func)
                                                                                             ((\ f_a1NyG
                                                                                                 -> (return
                                                                                                       . Plugin.Effect.Monad.Func)
                                                                                                      ((\ f_a1NyH
                                                                                                          -> return
                                                                                                               (Plugin.BuiltIn.ConsFL
                                                                                                                  f_a1NyG
                                                                                                                  f_a1NyH))))))
                                                                                          pFL_a1Ntv)
                                                                                       (Plugin.Effect.Monad.appFL
                                                                                          (Plugin.Effect.Monad.appFL
                                                                                             ((return
                                                                                                 . Plugin.Effect.Monad.Func)
                                                                                                ((\ f_a1Nzd
                                                                                                    -> (return
                                                                                                          . Plugin.Effect.Monad.Func)
                                                                                                         ((\ f_a1Nze
                                                                                                             -> return
                                                                                                                  (Plugin.BuiltIn.ConsFL
                                                                                                                     f_a1Nzd
                                                                                                                     f_a1Nze))))))
                                                                                             pFL_a1Ntx)
                                                                                          pFL_a1Nty))))))
                                                                      else
                                                                          (Plugin.Effect.Monad.appFL
                                                                             Plugin.BuiltIn.failFLStrFL
                                                                             (Plugin.Effect.Monad.toFL
                                                                                "Non-exhaustive patterns in function: isWalk'")))
                                                         _ -> (Plugin.Effect.Monad.appFL
                                                                 Plugin.BuiltIn.failFLStrFL
                                                                 (Plugin.Effect.Monad.toFL
                                                                    "Non-exhaustive patterns in function: isWalk'")))
                                               _ -> (Plugin.Effect.Monad.appFL
                                                       Plugin.BuiltIn.failFLStrFL
                                                       (Plugin.Effect.Monad.toFL
                                                          "Non-exhaustive patterns in function: isWalk'")))))
                    in
                      (Plugin.Effect.Monad.appFL
                         (Plugin.Effect.Monad.appFL isWalk'FL_a1NtB fFL_a1NtC)
                         (return (Plugin.BuiltIn.NilFL)))))
$dEq_a1NlR = Plugin.BuiltIn.C:EqFL $c==FL_a1NtE $c/=FL_a1NtJ
(==#_a1NtK)
  = (return . Plugin.Effect.Monad.Func)
      (\ fFL_a1NtM
         -> (return . Plugin.Effect.Monad.Func)
              (\ fFL_a1NtO
                 -> let
                      fFL_a1NtL
                        = ((Plugin.Effect.Monad.appFL
                              (return . Plugin.Effect.Monad.Func)
                                (\ dtt_cP x_cQ
                                   -> (x_cQ
                                         >>=
                                           (\ x'_cR
                                              -> return (ghc-prim:GHC.Types.I# (dtt_cP x'_cR))))
                                   ghc-prim:GHC.Prim.dataToTag#)
                              fFL_a1NtM)) in
                    let
                      fFL_a1NtN
                        = ((Plugin.Effect.Monad.appFL
                              (return . Plugin.Effect.Monad.Func)
                                (\ dtt_cS x_cT
                                   -> (x_cT
                                         >>=
                                           (\ x'_cU
                                              -> return (ghc-prim:GHC.Types.I# (dtt_cS x'_cU))))
                                   ghc-prim:GHC.Prim.dataToTag#)
                              fFL_a1NtO))
                    in
                      ((Plugin.Effect.Monad.appFL
                          (return . Plugin.Effect.Monad.Func)
                            (\ ttenum_cV ndint_cW
                               -> (ndint_cW
                                     >>=
                                       (\ (ghc-prim:GHC.Types.I# i_cX)
                                          -> Plugin.Effect.Monad.toFL (ttenum_cV i_cX)))
                               ghc-prim:GHC.Prim.tagToEnum#)
                          ((Plugin.Effect.Monad.appFL
                              (Plugin.Effect.Monad.appFL (Plugin.BuiltIn.==##) fFL_a1NtL)
                              fFL_a1NtN))))))
(/=#_a1NtQ) = Plugin.BuiltIn.$dm/=#
$dShow_a1Nm9
  = Plugin.BuiltIn.C:ShowFL
      $cshowsPrecFL_a1NtS $cshowFL_a1NtT $cshowListFL_a1NtW
showsPrecFL_a1NtX
  = (return . Plugin.Effect.Monad.Func)
      (\ fFL_a1NtZ
         -> (return . Plugin.Effect.Monad.Func)
              (\ fFL_a1NtY
                 -> (>>=)
                      fFL_a1NtY
                      (\case
                         Graph.AFL
                           -> (Plugin.Effect.Monad.appFL
                                 Plugin.BuiltIn.showStringFL (Plugin.Effect.Monad.toFL "A"))
                         Graph.BFL
                           -> (Plugin.Effect.Monad.appFL
                                 Plugin.BuiltIn.showStringFL (Plugin.Effect.Monad.toFL "B"))
                         Graph.CFL
                           -> (Plugin.Effect.Monad.appFL
                                 Plugin.BuiltIn.showStringFL (Plugin.Effect.Monad.toFL "C"))
                         Graph.DFL
                           -> (Plugin.Effect.Monad.appFL
                                 Plugin.BuiltIn.showStringFL (Plugin.Effect.Monad.toFL "D"))
                         _ -> (Plugin.Effect.Monad.appFL
                                 Plugin.BuiltIn.failFLStrFL
                                 (Plugin.Effect.Monad.toFL
                                    "Non-exhaustive patterns in function: showsPrec")))))
showFL_a1Nu1 = Plugin.BuiltIn.$dmshowFL
showListFL_a1Nu3 = Plugin.BuiltIn.$dmshowListFL
-}
