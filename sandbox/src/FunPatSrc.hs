{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module FunPatSrc where

g x y = (x, y)

pat y = g (id y) y

test f g x = f g x

id2 :: a -> b
id2 _ = undefined
{-
$(inv 'id2 True)
  :: (Plugin.Effect.Monad.NormalForm a1,
      Plugin.Effect.Monad.HasPrimitiveInfo
        (Lifted Plugin.Effect.Monad.FL a1),
      Plugin.Effect.Monad.Unifiable a2,
      Plugin.Effect.Monad.Convertible a1,
      Plugin.Effect.Monad.Convertible a2) =>
     a2 -> [Solo a1]
     ausgaben von inversen müssen convertible sein, normalform haben und primitiveinfo haben,
     eingaben selbiger müssen conviertible sein und unifizerbar
-}

f2 :: (a -> b) -> c -> d
f2 _ _ = error "bla"

h :: Bool -> Bool
h x = True
