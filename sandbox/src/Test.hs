{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
{-# OPTIONS_GHC -ddump-tc #-}

module Test where

($$$) :: (a -> b) -> a -> b
f $$$ x = f x
