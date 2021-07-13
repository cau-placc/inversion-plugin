{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module Export where

-- We can import these definitions in Import.hs.

data Result a b = Err a
                | Ok b

result :: (a -> c) -> (b -> c) -> Result a b -> c
result f _ (Err  a) = f a
result _ g (Ok b) = g b

value :: Result Bool Bool
value = Err True
