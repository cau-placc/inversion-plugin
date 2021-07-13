{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase      #-}
module Tests.QuickCheckInverse where

import Control.Monad
import Language.Haskell.TH
import Data.Foldable

import Plugin.InversionPlugin
import Plugin.Effect.TH (mkTupleP)

genInverseQuickCheck :: Name -> Int -> [Int] -> Q Exp
genInverseQuickCheck funName maxNumRes fixed = do
  invFun <- partialInv funName fixed
  ar <- reify funName >>= \case
    VarI     _ ty _ -> return (arity ty)
    ClassOpI _ ty _ -> return (arity ty)
    _ -> fail "genInverseQuickCheck: partialInv should have failed already"
  tk <- [| take maxNumRes |]
  equal <- [| \x xs -> all (==x) xs |]
  arg <- newName "arg"
  let numPartials = length fixed
  partials <- replicateM numPartials (newName "fixed")
  let allArgs = partials ++ [arg]
  let invRes = foldl' AppE invFun $ map VarE allArgs
  invResName <- newName "invResult"
  let invResDecl = ValD (VarP invResName) (NormalB invRes) []
  toOrig <- AppE (VarE 'map) <$> mkUncurry funName ar (zip fixed partials)

  let testExp = foldl' AppE equal [ VarE arg
                                  , AppE tk (AppE toOrig (VarE invResName)) ]
  return (LamE (map VarP allArgs) (LetE [invResDecl] testExp))

arity :: Type -> Int
arity (AppT (AppT ArrowT _) ty2) = 1 + arity ty2
arity (ForallT _ _ ty) = arity ty
arity (ParensT     ty) = arity ty
arity _                = 0

mkUncurry :: Name -> Int -> [(Int, Name)] -> Q Exp
mkUncurry funName num fixed = do
  args <- replicateM (num - length fixed) (newName "x")
  let applied = foldl' AppE (VarE funName) $ create fixed args 1
  return (LamE [mkTupleP $ map VarP args] applied)
  where
    create []             others      _       = map VarE others
    create rest           []          _       = map (VarE . snd) rest
    create ((n, v1):rest) (v2:others) current
      | n == current = VarE v1 : create rest           (v2:others) (current + 1)
      | otherwise    = VarE v2 : create ((n, v1):rest) others      (current + 1)
