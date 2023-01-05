{-|
Module      : Plugin.Trans.Var
Description : Various helper to create variables
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains various functions to generate fresh variables and other
stuff to deal with variables.
-}
module Plugin.Trans.Var where

import Data.Data (Data)
import Data.List
import Data.Generics.Schemes

import GHC.Core.TyCo.Rep
import GHC.Plugins
import GHC.Tc.Types


-- | Create a fresh type variable of kind 'Type'.
freshSimpleTVar :: TcM TyVar
freshSimpleTVar = do
  u <- getUniqueM
  let k = liftedTypeKind
  return $ mkTyVar (mkSystemName u (mkTyVarOcc "a")) k

-- | Create a fresh type variable of the given kind.
freshTVar :: Kind -> TcM TyVar
freshTVar k = do
  u <- getUniqueM
  return $ mkTyVar (mkSystemName u (mkTyVarOcc "a")) k

-- | Create a fresh type variable of kind 'Type -> Type'.
freshMonadTVar :: TcM TyVar
freshMonadTVar = do
  u <- getUniqueM
  let k = liftedTypeKind
  return $ mkTyVar (mkSystemName u (mkTyVarOcc "m")) (mkVisFunTyMany k k)

-- | Create a fresh variable of the given type.
freshVar :: Scaled Type -> TcM Var
freshVar (Scaled mult ty) = do
  u <- getUniqueM
  let name = mkSystemName u (mkVarOcc "f")
  return $ mkLocalVar VanillaId name mult ty vanillaIdInfo

-- | Create a fresh dictionary variable of the given type.
freshDictId :: Type -> TcM Var
freshDictId ty = do
  u <- getUniqueM
  let name = mkSystemName u (mkVarOcc "d")
  return $ mkLocalVar (DFunId True) name Many ty vanillaIdInfo

-- | Count the number of occurrences of the variable in the given term.
countVarOcc :: Data a => Var -> a -> Int
countVarOcc v e = length (listify (\v' -> varUnique v' == u) e)
  where u = varUnique v

-- | Change the unique of the given name and add a suffix.
liftName :: Name -> Unique -> Name
liftName n u = tidyNameOcc (setNameUnique n u) (addNameSuffix (occName n))

addNameSuffix :: OccName -> OccName
addNameSuffix o
  | isSymOcc o = mkOccName (occNameSpace o) (occNameString o ++ "#")
  | otherwise  = mkOccName (occNameSpace o) (occNameString o ++ "FL")

removeNameSuffix :: OccName -> OccName
removeNameSuffix o
  | isSymOcc o = case occNameString o of
      s | last s == '#'       -> mkOccName (occNameSpace o) (init s)
      _                       -> o
  | otherwise  = case occNameString o of
      s | "FL" `isSuffixOf` s -> mkOccName (occNameSpace o) (init (init s))
      _                       -> o

isLiftedDefaultName :: OccName -> OccName -> Bool
isLiftedDefaultName o1 o2 =
  o2 ==
  mkOccName (occNameSpace o1) ("$dm" ++ occNameString
  (addNameSuffix (mkOccName (occNameSpace o1) (drop 3 (occNameString o1)))))

-- | Change the unique of the given name and add a suffix.
liftVarName :: Var -> Unique -> Var
liftVarName n u = setVarName (setVarUnique n u) (liftName (varName n) u)
