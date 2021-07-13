{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Example0 where

import Example

testImp :: Bool
testImp = not (id2 True)

append :: [a] -> [a] -> [a]
append = (+++)
