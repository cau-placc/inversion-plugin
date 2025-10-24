{-# LANGUAGE TemplateHaskell, ViewPatterns, FlexibleContexts, UndecidableInstances #-}
{-# OPTIONS_GHC -ddump-splices #-}

module Test2 where

import Test

import Plugin.InversionPlugin

idInv :: (Argument a, Result a) => a -> [a]
idInv x = $(inv 'id2) x

lookupInv :: (Argument a, Argument [(a, b)], Result (Maybe b), Argument b, Unifiable (Transform (b), To b), Transform (Eq a)) => Maybe b -> [(a, [(a, b)])]
--lookupInv :: (Argument a, Argument b, Result b, Transform (Eq a)) => Maybe b -> [(a, [(a, b)])]
lookupInv x = $(inv 'lookup) x

--lookupInv2 :: (Argument a, To [(a, b)], Result (Maybe b), Transform (Eq a)) => [(a, b)] -> Maybe b -> [a]
lookupInv2 :: (Argument a, To a, To b, Result b, Transform (Eq a)) => [(a, b)] -> Maybe b -> [a]
lookupInv2 map x = $(partialInv 'lookup [1]) map x

{-
let
      g_aaqs
        = let
            g_aaqt x_aaqu
              = let
                  b_aaqE free0_aaqv
                    = Plugin.Effect.Monad.fromFL
                        (do (Plugin.Effect.Monad.nonStrictUnifyFL
                               (((>>=) Plugin.BuiltIn.idFL)
                                  (\ (Plugin.Effect.Monad.Func v_aaqD) -> v_aaqD free0_aaqv)))
                              (Plugin.Effect.Monad.toFL x_aaqu)
                            Plugin.Effect.Monad.groundNormalFormFL free0_aaqv)
                in
                  b_aaqE
                    (Plugin.Effect.Monad.FL (return (Plugin.Effect.Monad.Var 0)))
          in g_aaqt
    in g_aaqs
-}
