{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
module Plugin.Primitives
  ( Transform, Argument, Result, inv, To, partialInv, semiInv, weakInv
  , Class, inOutClassInv, inClassInv, var
  , invFree, partialInvFree, semiInvFree, weakInvFree, inClassInvFree, inOutClassInvFree, showFree
  , funPat, funPatLegacy
  , module Plugin.BuiltIn.Primitive
  ) where

import Control.Monad.State

import Data.Bifunctor
import Data.List
import Data.Maybe

import Generics.SYB

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Plugin.BuiltIn.Primitive
import Plugin.Effect.Monad
import Plugin.Effect.TH

{-# ANN module "HLint: ignore Redundant bracket" #-}

inv, invFree :: Name -> ExpQ
inv = genInv True
invFree = genInv False

partialInv, partialInvFree :: Name -> [Int] -> ExpQ
partialInv = genPartialInv True
partialInvFree = genPartialInv False

--TODO: Free in nonGround umbenennen
semiInv, semiInvFree :: Name -> [Int] -> [Int] -> ExpQ
semiInv = genSemiInv True
semiInvFree = genSemiInv False

weakInv, weakInvFree :: Name -> ExpQ
weakInv = genWeakInv True
weakInvFree = genWeakInv False

inClassInv, inClassInvFree :: Name -> [ExpQ] -> ExpQ
inClassInv = genInClassInv True
inClassInvFree = genInClassInv False

inOutClassInv, inOutClassInvFree :: Name -> [ExpQ] -> ExpQ -> ExpQ
inOutClassInv = genInOutClassInv True
inOutClassInvFree = genInOutClassInv False

genInv :: Bool -> Name -> ExpQ
genInv gnf = flip (genPartialInv gnf) []

-- CAUTION! This primitive has to generate a let expression (instead of a lambda expression).
-- See also remark at `inClassInv`.
-- TODO: Check if indices beginning with 0 or 1 are better.
genPartialInv :: Bool -> Name -> [Int] -> ExpQ
genPartialInv gnf name fixedArgIndices = do
  originalArity <- getFunArity name
  --when (originalArity == 0) $ fail "Cannot create inverse for a nullary function"
  let validFixedArgIndices = [1 .. originalArity]
  when (any (`notElem` validFixedArgIndices) fixedArgIndices) $ fail $
    "Invalid argument index sequence for partial inverse provided (has to be a subsequence of " ++ show validFixedArgIndices ++ ")"
  let nubbedFixedArgIndices = nub fixedArgIndices
      nonFixedArgIndices = filter (`notElem` fixedArgIndices) validFixedArgIndices
  fixedArgNames <- replicateM (length nubbedFixedArgIndices) (newName "fixedArg")
  nonFixedArgNames <- replicateM (length nonFixedArgIndices) (newName "freeArg")
  resArgName <- newName "resArg"
  let fixedArgExps = zip nubbedFixedArgIndices $ map (AppE (VarE 'toFL) . VarE) fixedArgNames
      nonFixedArgExps = zip nonFixedArgIndices $ map VarE nonFixedArgNames
      argExps = map snd $ sortOn fst $ fixedArgExps ++ nonFixedArgExps
  g <- newName "g"

  liftedName <- liftTHNameQ name
  funPatExp <- genLiftedApply (VarE liftedName) argExps
  let resExp = AppE (VarE 'toFL) (VarE resArgName)
      nonStrictUnifyExp = applyExp (VarE 'nonStrictUnifyFL) [funPatExp, resExp]
      shareFrees = map (\nm -> BindS (VarP nm) (AppE (VarE 'share) (VarE 'free))) nonFixedArgNames
      doExp = DoE Nothing $ shareFrees ++ [NoBindS nonStrictUnifyExp, NoBindS (AppE (VarE (if gnf then 'groundNormalFormFL else 'normalFormFL)) returnExp)]
      returnExp = mkLiftedTupleE $ map snd nonFixedArgExps
      bodyExp = AppE (VarE 'fromFL) doExp
  bNm <- newName "b"
  typ <- getFunType name
  ctxt <- getFunContext name

  let (argTys, resTy) = arrowUnapply typ
      indexedArgTys = zip [1 ..] argTys
      fixedArgTys = filter (\(i, _) -> i `elem` nubbedFixedArgIndices) indexedArgTys
      unfixedArgTys = filter (\(i, _) -> i `notElem` nubbedFixedArgIndices) indexedArgTys
      invContext = context ++ map (AppT (ConT ''Transform)) ctxt
      context = nub $ map (AppT (ConT ''Argument) . snd) unfixedArgTys ++
                return (AppT (ConT ''Result) resTy) ++
                map (AppT (ConT ''To) . snd) fixedArgTys
      bTy = ForallT [] invContext $ foldr mkArrowT (AppT ListT $ mkTupleT $ map snd unfixedArgTys) $ map (AppT (ConT ''FL) . AppT (ConT ''Transform) . snd) unfixedArgTys

  let freeExps = take (length nonFixedArgExps) $ map (AppE (ConE 'FL) . AppE (VarE 'return) . AppE (ConE 'Var) . mkIntExp) [0 ..]
  let letDecs = zipWith (\nm e -> FunD nm [Clause [] (NormalB e) []]) nonFixedArgNames freeExps ++
                zipWith (\nm ty -> SigD nm (ForallT
                                             (map (\n -> PlainTV n SpecifiedSpec) (allTyVars ty))
                                             [((AppT (ConT ''HasPrimitiveInfo) . AppT (ConT ''Transform)) ty)]
                                             ((AppT (ConT ''FL) . AppT (ConT ''Transform)) ty)))
                          nonFixedArgNames (map snd unfixedArgTys)
  let invExp = bodyExp

  let invTyNoForall = foldr mkArrowT (AppT ListT $ mkTupleT $ map snd unfixedArgTys) $ map snd fixedArgTys ++ [resTy]
      invTy = ForallT (map (\n -> PlainTV n SpecifiedSpec) (allTyVars invTyNoForall)) invContext invTyNoForall

  -- return $ (LamE (map VarP $ fixedArgNames ++ [resArgName]) invExp)
  return $ LetE [
    SigD g invTy,
    FunD g [Clause (map VarP $ fixedArgNames ++ [resArgName]) (NormalB invExp) []]] ((VarE g) )
  {-params <- replicateM (length fixedArgNames + 1) (newName "param")
  return $ LamE (map VarP params) $ LetE [
    SigD g invTy,
    FunD g [Clause (map VarP $ fixedArgNames ++ [resArgName]) (NormalB invExp) []]] $ applyExp (VarE g) $ map VarE params-}

{-
-- CAUTION! This primitive has to generate a let expression (instead of a lambda expression).
-- See also remark at `inClassInv`.
genPartialInv :: Bool -> Name -> [Int] -> ExpQ
genPartialInv gnf name fixedArgIndices = do
  originalArity <- getFunArity name
  --when (originalArity == 0) $ fail "Cannot create inverse for a nullary function"
  let validFixedArgIndices = [1 .. originalArity]
  when (any (`notElem` validFixedArgIndices) fixedArgIndices) $ fail $
    "Invalid argument index sequence for partial inverse provided (has to be a subsequence of " ++ show validFixedArgIndices ++ ")"
  --when (length (nub fixedArgIndices) == originalArity) $ fail $
  --  "Invalid argument index sequence for partial inverse provided (must not contain all indices)"
  let nubbedFixedArgIndices = nub fixedArgIndices
      nonFixedArgIndices = filter (`notElem` fixedArgIndices) validFixedArgIndices
  fixedArgNames <- replicateM (length nubbedFixedArgIndices) (newName "fixedArg")
  let fixedArgExps = zip nubbedFixedArgIndices $ map VarE fixedArgNames
      nonFixedArgExps = zip nonFixedArgIndices $ map (AppE (VarE 'var) . mkIntExp) [0 ..]
      inClassExps = map snd $ sortOn fst $ fixedArgExps ++ nonFixedArgExps
  g <- newName "g"
  invE <- genInClassInv gnf name (map return inClassExps)
  typ <- getFunType name
  let (argTys, resTy) = arrowUnapply typ
      indexedArgTys = zip [1 ..] argTys
      fixedArgTys = filter (\(i, _) -> i `elem` nubbedFixedArgIndices) indexedArgTys
      unfixedArgTys = filter (\(i, _) -> i `notElem` nubbedFixedArgIndices) indexedArgTys
      context = nub $ map (AppT (ConT ''Argument) . snd) unfixedArgTys ++
                return (AppT (ConT ''Result) resTy) ++
                map (AppT (ConT ''To) . snd) fixedArgTys
      invTy = ForallT [] context $ foldr mkArrowT (AppT ListT $ mkTupleT $ map snd unfixedArgTys) $ map snd fixedArgTys ++ [resTy]
  return $ LetE [SigD g invTy, FunD g [Clause (map VarP fixedArgNames) (NormalB invE) []]] (VarE g)
-}

genSemiInv :: Bool -> Name -> [Int] -> [Int] -> ExpQ
genSemiInv gnf name fixedArgIndices fixedResIndices = do
  originalArity <- getFunArity name
  -- when (originalArity == 0) $ fail "Cannot create inverse for a nullary function"
  let validFixedArgIndices = [1 .. originalArity]
  when (any (`notElem` validFixedArgIndices) fixedArgIndices) $ fail $
    "Invalid argument index sequence for semi inverse provided (has to be a subsequence of " ++ show validFixedArgIndices ++ ")"
  --when (length (nub fixedArgIndices) == originalArity) $ fail $
  --  "Invalid argument index sequence for partial inverse provided (must not contain all indices)"
  let nubbedFixedArgIndices = nub fixedArgIndices
      nonFixedArgIndices = filter (`notElem` fixedArgIndices) validFixedArgIndices
  fixedArgNames <- replicateM (length nubbedFixedArgIndices) (newName "fixedArg")
  nonFixedArgNames <- replicateM (length nonFixedArgIndices) (newName "freeArg")
  typ <- getFunType name
  let resultArity = fromMaybe 1 $ case fst (unapplyType (snd (arrowUnapply typ))) of
          ConT (Name (OccName resultOccConName) _) -> tupleConArity resultOccConName
          TupleT n           -> Just n
          _                  -> Nothing
  let validFixedResIndices = [1 .. resultArity]
  when (any (`notElem` validFixedResIndices) fixedResIndices) $ fail $
    "Invalid result index sequence for semi inverse provided (has to be a subsequence of " ++ show validFixedResIndices ++ ")"
  let nubbedFixedResIndices = nub fixedResIndices
      nonFixedResIndices = filter (`notElem` fixedResIndices) validFixedResIndices
  fixedResNames <- replicateM (length nubbedFixedResIndices) (newName "fixedResult")
  nonFixedResNames <- replicateM (length nonFixedResIndices) (newName "freeRes")

  let fixedArgExps = zip nubbedFixedArgIndices $ map (AppE (VarE 'toFL) . VarE) fixedArgNames
      nonFixedArgExps = zip nonFixedArgIndices $ map VarE nonFixedArgNames
      argExps = map snd $ sortOn fst $ fixedArgExps ++ nonFixedArgExps
  let fixedResExps = zip nubbedFixedResIndices $ map (AppE (VarE 'toFL) . VarE) fixedResNames
      nonFixedResExps = zip nonFixedResIndices $ map VarE nonFixedResNames
      resExps = map snd $ sortOn fst $ fixedResExps ++ nonFixedResExps

  g <- newName "g"

  liftedName <- liftTHNameQ name
  funPatExp <- genLiftedApply (VarE liftedName) argExps
  let resExp = mkTupleE' resExps
      mkTupleE' [e] = e
      mkTupleE' es = mkLiftedTupleE es
      nonStrictUnifyExp = applyExp (VarE 'nonStrictUnifyFL) [funPatExp, resExp]
      doExp = DoE Nothing [NoBindS nonStrictUnifyExp, NoBindS (AppE (VarE (if gnf then 'groundNormalFormFL else 'normalFormFL)) returnExp)]
      returnExp = mkLiftedTupleE $ map snd $ nonFixedArgExps ++ nonFixedResExps
      bodyExp = AppE (VarE 'fromFL) doExp
  bNm <- newName "b"
  let letDecs = [FunD bNm [Clause (map VarP $ nonFixedArgNames ++ nonFixedResNames) (NormalB bodyExp) []]]
  let freeExps = take (length $ nonFixedArgExps ++ nonFixedResExps) $ map (AppE (ConE 'FL) . AppE (VarE 'return) . AppE (ConE 'Var) . mkIntExp) [0 ..]
  let invExp = LetE letDecs (applyExp (VarE bNm) freeExps)

  let (argTys, resTy) = arrowUnapply typ
      resTys = case unapplyType resTy of
          (ConT (Name (OccName resultOccConName) _), tys) | Just _ <- tupleConArity resultOccConName -> tys
          (TupleT _, tys) -> tys
          _ -> [resTy]
      indexedArgTys = zip [1 ..] argTys
      fixedArgTys = filter (\(i, _) -> i `elem` nubbedFixedArgIndices) indexedArgTys
      unfixedArgTys = filter (\(i, _) -> i `notElem` nubbedFixedArgIndices) indexedArgTys

      indexedResTys = zip [1 ..] resTys
      fixedResTys = filter (\(i, _) -> i `elem` nubbedFixedResIndices) indexedResTys
      fixedResTupleTy = if length fixedResTys > 1 then [mkTupleT (map snd fixedResTys)] else take 1 (map snd fixedResTys)
      unfixedResTys = filter (\(i, _) -> i `notElem` nubbedFixedResIndices) indexedResTys


  ctxt <- getFunContext name
  let invContext = context ++ map (AppT (ConT ''Transform)) ctxt
      context = nub $ map (AppT (ConT ''Argument) . snd) (unfixedArgTys ++ unfixedResTys) ++
                return (AppT (ConT ''Unifiable) (AppT (ConT ''Transform) resTy)) ++
                {-map (AppT (ConT ''NormalForm) . AppT (ConT ''Transform) . snd) unfixedResTys ++
                map (AppT (ConT ''From) . snd) unfixedResTys ++
                map (AppT (ConT ''HasPrimitiveInfo) . AppT (ConT ''Transform) . snd) unfixedResTys ++-}
                map (AppT (ConT ''To) . snd) (fixedArgTys ++ fixedResTys)
      invTyNoForall = foldr mkArrowT (AppT ListT $ mkTupleT $ map snd $ unfixedArgTys ++ unfixedResTys) $ map snd fixedArgTys ++ fixedResTupleTy
      invTy = ForallT [] invContext invTyNoForall

  let resPs | length fixedResExps > 1 = [mkTupleP (map VarP fixedResNames)]
            | length fixedResExps == 1 = [VarP (head fixedResNames)]
            | otherwise = []
  return $ LetE [
    SigD g invTy,
    FunD g [Clause (map VarP fixedArgNames ++ resPs) (NormalB invExp) []]] (VarE g)

{-
-- CAUTION! This primitive has to generate a let expression (instead of a lambda expression).
-- See also remark at `inClassInv`.
-- TODO: Check if indices beginning with 0 or 1 are better.
genSemiInv :: Bool -> Name -> [Int] -> [Int] -> ExpQ
genSemiInv gnf name fixedArgIndices fixedResultIndices = do
  originalArity <- getFunArity name
  -- when (originalArity == 0) $ fail "Cannot create inverse for a nullary function"
  let validFixedArgIndices = [1 .. originalArity]
  when (any (`notElem` validFixedArgIndices) fixedArgIndices) $ fail $
    "Invalid argument index sequence for semi inverse provided (has to be a subsequence of " ++ show validFixedArgIndices ++ ")"
  --when (length (nub fixedArgIndices) == originalArity) $ fail $
  --  "Invalid argument index sequence for partial inverse provided (must not contain all indices)"
  let nubbedFixedArgIndices = nub fixedArgIndices
      nonFixedArgIndices = filter (`notElem` fixedArgIndices) validFixedArgIndices
  fixedArgNames <- replicateM (length nubbedFixedArgIndices) (newName "fixedArg")
  let fixedArgExps = zip nubbedFixedArgIndices $ map VarE fixedArgNames
      nonFixedArgExps = zip nonFixedArgIndices $ map (AppE (VarE 'var) . mkIntExp) [0 ..]
      inClassExps = map snd $ sortOn fst $ fixedArgExps ++ nonFixedArgExps
  typ <- getFunType name
  let resultArity = fromMaybe 1 $ case fst (unapplyType (snd (arrowUnapply typ))) of
          ConT (Name (OccName resultOccConName) _) -> tupleConArity resultOccConName
          TupleT n           -> Just n
          _                  -> Nothing
  let validFixedResultIndices = [1 .. resultArity]
  when (any (`notElem` validFixedResultIndices) fixedResultIndices) $ fail $
    "Invalid result index sequence for semi inverse provided (has to be a subsequence of " ++ show validFixedResultIndices ++ ")"
  let nubbedFixedResultIndices = nub fixedResultIndices
      nonFixedResultIndices = filter (`notElem` fixedResultIndices) validFixedResultIndices
  fixedResultNames <- replicateM (length nubbedFixedResultIndices) (newName "fixedResult")
  let fixedResultExps = zip nubbedFixedResultIndices $ map VarE fixedResultNames
      nonFixedResultExps = zip nonFixedResultIndices $ map (AppE (VarE 'var) . mkIntExp) [originalArity ..]
      outClassExps = map snd $ sortOn fst $ fixedResultExps ++ nonFixedResultExps
      outClassExp = if resultArity > 1 then mkTupleE outClassExps else head outClassExps
      fixedResultPats = if length fixedResultExps > 1 then [mkTupleP (map VarP fixedResultNames)] else take 1 (map VarP fixedResultNames)
  g <- newName "g"
  invE <- genInOutClassInv gnf name (map return inClassExps) (return outClassExp)
  let (argTys, resTy) = arrowUnapply typ
      resTys = case unapplyType resTy of
          (ConT (Name (OccName resultOccConName) _), tys) | Just _ <- tupleConArity resultOccConName -> tys
          (TupleT _, tys) -> tys
          _ -> [resTy]
      indexedResTys = zip [1 ..] resTys
      indexedArgTys = zip [1 ..] argTys
      fixedResTys = filter (\(i, _) -> i `elem` nubbedFixedResultIndices) indexedResTys
      fixedResTupleTy = if length fixedResTys > 1 then [mkTupleT (map snd fixedResTys)] else take 1 (map snd fixedResTys)
      fixedArgTys = filter (\(i, _) -> i `elem` nubbedFixedArgIndices) indexedArgTys
      unfixedArgTys = filter (\(i, _) -> i `notElem` nubbedFixedArgIndices) indexedArgTys
      unfixedResTys = filter (\(i, _) -> i `notElem` nubbedFixedResultIndices) indexedResTys
      context = nub $ map (AppT (ConT ''Argument) . snd) unfixedArgTys ++
                return (AppT (ConT ''Result) resTy) ++
                map (AppT (ConT ''To) . snd) fixedArgTys
      invTy = ForallT [] context $ foldr mkArrowT (AppT ListT $ mkTupleT $ map snd $ unfixedArgTys ++ unfixedResTys) $ map snd fixedArgTys ++ fixedResTupleTy
  return $ LetE [SigD g invTy, FunD g [Clause (map VarP fixedArgNames ++ fixedResultPats) (NormalB invE) []]] (VarE g)-}

genWeakInv :: Bool -> Name -> ExpQ
genWeakInv gnf name = [| foldr const (error "no weak inverse") . $(genInv gnf name) |]

allTyVars :: Type -> [Name]
allTyVars = map (\(VarT n) -> n) . nub . listify (\case
  VarT n -> True
  _      -> False)

type Class = ExpQ

--TODO: appFL verwenden
genInOutClassInv :: Bool -> Name -> [Class] -> Class -> ExpQ
genInOutClassInv gnf name inClassExpQs outClassExpQ = do
  originalArity <- getFunArity name
  let numInClasses = length inClassExpQs
  when (originalArity /= numInClasses) $ fail $ "Wrong number of input classes provided (expected " ++ show originalArity ++ ", but got " ++ show numInClasses ++ ")"
  inClassExps <- sequence inClassExpQs
  outClassExp <- outClassExpQ
  -- We add the output class at the end of the input classes, so that the free variables of the output class appear at the end of the result tuples of inverses.
  let exps = inClassExps ++ [outClassExp]
  mapping <- createFreeMap exps
  liftedName <- liftTHNameQ name
  resExp : argExps <- mapM (convertExp (map (second fst) mapping)) (outClassExp:inClassExps)
  funPatExp <- genLiftedApply (VarE liftedName) argExps
  let nonStrictUnifyExp = applyExp (VarE 'nonStrictUnifyFL) [funPatExp, resExp]
      freeNames = map (fst . snd) mapping
      doExp = DoE Nothing [NoBindS nonStrictUnifyExp, NoBindS (AppE (VarE (if gnf then 'groundNormalFormFL else 'normalFormFL)) returnExp)]
      returnExp = mkLiftedTupleE (map VarE freeNames)
      bodyExp = AppE (VarE 'fromFL) doExp
  bNm <- newName "b"
  let letDecs = [FunD bNm [Clause (map VarP freeNames) (NormalB bodyExp) []]]
  return $ LetE letDecs (applyExp (VarE bNm) (map (snd . snd) mapping))
  --TODO: explain why monomorph types, let generalisation does not take place, because the type of free1/2 leaks to the outside (as every free variable is part of the return value of an inverse)


-- $(partialInv 'map [| replicate 2 True |] [| free 1 |])
--TODO: inferenzsystem für erlaubte ausdrücke in input classes.
--TODO: TTH damit man falsche applications von free oder konstruktoren finden kann. pattern wären nicht ausreichend, da wir so keine freien variablen nicht-linear spezifizieren könnten, da syntaktisch verboten.
--TODO: mapping zu negativen zahlen


--TODO: mapping sorum gut, weil es sonst durch neu nummerierung sein kann, dass variablen, die vom nutzer angegeben wurden, mit neuen typen identifiziert werden (da diese ja neu vergeben werden).
convertExp :: [(Integer, Name)] -> Exp -> Q Exp
convertExp freeMap = \case
  VarE na -> return $ AppE (VarE 'toFL) (VarE na)
  ConE na -> do
    argsNum <- getConArity na
    nms <- replicateM argsNum (newName "arg")
    return $ LamE (map VarP nms) (AppE (VarE 'return) (foldl AppE (ConE (liftTHName na)) (map VarE nms)))
  LitE lit -> return $ AppE (VarE 'toFL) (LitE lit)
  AppE exp' exp2 -> case exp' of
    VarE na
      | na == 'var -> case exp2 of
        LitE (IntegerL i) | i >= 0 -> case lookup i freeMap of
          Nothing -> error $ "Internal error: var " ++ show i ++ " not found"
          Just n  -> return $ VarE n
        _ -> fail "var has to be applied to non-negative integers"
      | otherwise  -> fail "Wrong form of class (forbidden function application)"
    _ -> AppE <$> convertExp freeMap exp' <*> convertExp freeMap exp2
  ParensE exp' -> ParensE <$> convertExp freeMap exp'
  InfixE m_exp exp' ma | isJust m_exp && isJust ma -> convertExp freeMap (applyExp exp' (map fromJust [m_exp, ma]))
  TupE m_exps | all isJust m_exps -> mkLiftedTupleE <$> mapM (convertExp freeMap . fromJust) m_exps
  ListE exps -> convertExp freeMap (foldr (\x xs -> applyExp (ConE '(:)) [x, xs]) (ConE '[]) exps)
  --TODO: handle wildcard/hole
  UnboundVarE na -> fail $ "Variable not in scope: " ++ show na
  _ -> fail "Wrong form of class (unsupported syntax)"

createFreeMap :: [Exp] -> Q [(Integer, (Name, Exp))]
createFreeMap = mapM (\case
    AppE _ (LitE (IntegerL i)) -> do
      nm <- newName $ "free" ++ (if i < 0 then "m" else "") ++ show (abs i)
      return (i, (nm, AppE (ConE 'FL) (AppE (VarE 'return) (AppE (ConE 'Var) (LitE (IntegerL i))))))
    _ -> error "Internal error: createFreeMap") .
  nub .
  listify (\case
    AppE (VarE nm) (LitE (IntegerL _)) | nm == 'var -> True
    _ -> False)

-- CAUTION! This primitive has to generate a let expression (instead of the following lambda expression `[| \x = $(inOutClassInv f gnf ins [| x |]) |]`), because otherwise examples like `$(inv 'id True) [True]` would fail to type.
-- This is weird behavior by the GHC and probably a bug.
-- Remark by Kai-Oliver Prott: Could be a confluence error.
genInClassInv :: Bool -> Name -> [Class] -> ExpQ
genInClassInv gnf f ins = [| let g x = $(genInOutClassInv gnf f ins [| x |]) in g |]

--TODO: Comment generation scheme
funPat :: Name -> [PatQ] -> PatQ
funPat name qps = do
  ps <- sequence qps
  vs <- getAllPatVars ps
  res <- evalStateT (mapM patToExp ps) 0
  ViewP <$> inClassInvFree name (map return res) <*> [p| $(return $ mkTupleP vs):_ |]

getAllPatVars :: [Pat] -> Q [Pat]
getAllPatVars = flip evalStateT [] .
  mapM (\case
    VarP nm -> do
      occNms <- get
      let occNm = occName nm
      if occNm `elem` occNms
        then fail $ "Conflicting definitions for ‘" ++ occString occNm ++ "’"
        else do
          modify (occNm :)
          return (VarP nm)
    p -> return p
  ) .
  listify (\case
    VarP _ -> True
    WildP  -> True
    _ -> False)
  where
    occName (Name o _) = o

createFreshVarCall :: MonadState Int m => m Exp
createFreshVarCall = do
  i <- get
  put (i + 1)
  return $ AppE (VarE 'var) (LitE (IntegerL (toInteger i)))

patToExp :: (MonadFail m, MonadState Int m) => Pat -> m Exp
patToExp (LitP lit) = return $ LitE lit
patToExp (VarP _) = createFreshVarCall
patToExp WildP = createFreshVarCall
patToExp (ConP nm _ ps) = applyExp (ConE nm) <$> mapM patToExp ps
patToExp (ParensP pat) = patToExp pat
patToExp (InfixP p1 n p2) = do
  e1 <- patToExp p1
  let op = ConE n
  e2 <- patToExp p2
  return $ InfixE (Just e1) op (Just e2)
patToExp (TupP ps) = TupE <$> mapM (fmap Just . patToExp) ps
patToExp (ListP ps) = ListE <$> mapM patToExp ps
patToExp _ = fail "Unsupported syntax in functional pattern"

funPatLegacy :: Name -> [PatQ] -> PatQ
funPatLegacy name qps = do
  tP <- mkTupleP <$> sequence qps
  vE <- [| (\a -> [b | b@($(return (anonymizePat tP))) <- $(invFree name) a]) |]
  _ <- evalStateT (patToExp tP) 0 -- Check for unsupported syntax
  _ <- getAllPatVars [tP]         -- Check for conflicting variable definitions
  ViewP vE <$> [p| $(return tP):_ |]

anonymizePat :: Pat -> Pat
anonymizePat (LitP l)              = LitP l
anonymizePat (VarP _)              = WildP
anonymizePat (TupP ps)             = TupP $ map anonymizePat ps
anonymizePat (UnboxedTupP ps)      = UnboxedTupP $ map anonymizePat ps
anonymizePat (UnboxedSumP p a1 a2) = UnboxedSumP (anonymizePat p) a1 a2
anonymizePat (ConP n tys ps)       = ConP n tys $ map anonymizePat ps
anonymizePat (InfixP p1 n p2)      = InfixP (anonymizePat p1) n (anonymizePat p2)
anonymizePat (UInfixP p1 n p2)     = UInfixP (anonymizePat p1) n (anonymizePat p2)
anonymizePat (ParensP p)           = ParensP $ anonymizePat p
anonymizePat (TildeP p)            = TildeP $ anonymizePat p
anonymizePat (BangP p)             = BangP $ anonymizePat p
anonymizePat (AsP _ p)             = anonymizePat p
anonymizePat WildP                 = WildP
anonymizePat (RecP n fps)          = RecP n $ map (fmap anonymizePat) fps
anonymizePat (ListP ps)            = ListP $ map anonymizePat ps
anonymizePat (SigP p ty)           = SigP (anonymizePat p) ty
anonymizePat (ViewP e p)           = ViewP e (anonymizePat p)
