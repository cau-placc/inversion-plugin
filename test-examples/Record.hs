{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module Record where

-- Record syntax is fully supported:

-- Record datatypes
data Rec = Rec { fromRec :: Int }
         | NoRec

-- Record patterns
test1 :: Rec -> Int
test1 Rec { fromRec = x } = x
test1 NoRec               = 0

-- Record constructors
test2 :: Rec
test2 = Rec { fromRec = 1 }

-- Record updates
test3 :: Rec
test3 = test2 { fromRec = 2 }
