{-# LANGUAGE TypeOperators #-}
module Plugin.BuiltIn.Char where

import Plugin.Effect.Monad
--import Plugin.BuiltIn
import Plugin.BuiltIn.Primitive

chrFL :: FL (IntFL FL :--> CharFL FL)
chrFL = undefined --toEnumFL

ordFL :: FL (CharFL FL :--> IntFL FL)
ordFL = undefined --fromEnumFL
