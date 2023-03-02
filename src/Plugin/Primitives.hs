{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}

module Plugin.Primitives
  ( Input, Output, inv, To, partialInv, weakInv
  , Class, inOutClassInv, inClassInv, var
  , showFree
  , funPat, funPatLegacy
  ) where

import Control.Monad.State

import Data.Bifunctor
import Data.List
import Data.Maybe

import Generics.SYB

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Plugin.Effect.Monad
import Plugin.Effect.TH

{-# ANN module "HLint: ignore Redundant bracket" #-}

inv :: Name -> Bool -> ExpQ
inv f = flip (partialInv f) []

-- CAUTION! This primitive has to generate a let expression (instead of a lambda expression).
-- See also remark at `inClassInv`.
partialInv :: Name -> Bool -> [Int] -> ExpQ
partialInv name gnf fixedArgIndices = do
  originalArity <- getFunArity name
  let validFixedArgIndices = [0 .. originalArity - 1]
      hint = "has to be a subsequence of " ++ show validFixedArgIndices
  when (any (`notElem` validFixedArgIndices) fixedArgIndices) $ fail $
    "Invalid argument index sequence for partial inverse provided (" ++ hint ++ ")"
  let nubbedFixedArgIndices = nub fixedArgIndices
      nonFixedArgIndices = filter (`notElem` fixedArgIndices) validFixedArgIndices
  fixedArgNames <- replicateM (length nubbedFixedArgIndices) (newName "fixedArg")
  let fixedArgExps = zip nubbedFixedArgIndices $ map VarE fixedArgNames
      nonFixedArgExps = zip nonFixedArgIndices $ map (AppE (VarE 'var) . mkIntExp) [0 ..]
      inClassExps = map snd $ sortOn fst $ fixedArgExps ++ nonFixedArgExps
  g <- newName "g"
  invE <- inClassInv name gnf (map return inClassExps)
  return $ LetE [FunD g [Clause (map VarP fixedArgNames) (NormalB invE) []]] (VarE g)

weakInv :: Name -> Bool -> ExpQ
weakInv name gnf = [| foldr const (error "no weak inverse") . $(inv name gnf) |]

type Class = ExpQ

inOutClassInv :: Name -> Bool -> [Class] -> ExpQ -> ExpQ
inOutClassInv name gnf inClassExpQs outClassExpQ = do
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
  let lazyUnifyExp = applyExp (VarE 'lazyUnifyFL) [funPatExp, resExp]
      freeNames = map (fst . snd) mapping
      letExp = DoE Nothing [NoBindS lazyUnifyExp, NoBindS returnExp]
      returnExp = mkLiftedTupleE (map VarE freeNames)
      bodyExp = applyExp (VarE 'map) [VarE 'fromFLVal, AppE (VarE 'evalFL) (AppE (VarE (if gnf then 'groundNormalFormFL else 'normalFormFL)) letExp)]
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
inClassInv :: Name -> Bool -> [Class] -> ExpQ
inClassInv f gnf ins = [| let g x = $(inOutClassInv f gnf ins [| x |]) in g |]

funPat :: Name -> [PatQ] -> PatQ
funPat name qps = do
  ps <- sequence qps
  vs <- getAllPatVars ps
  res <- evalStateT (mapM patToExp ps) 0
  ViewP <$> inClassInv name False (map return res) <*> [p| $(return $ mkTupleP vs):_ |]

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
  vE <- [| (\a -> [b | b@($(return (anonymizePat tP))) <- $(inv name False) a]) |]
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
