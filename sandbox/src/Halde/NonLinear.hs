{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module NonLinear where

{-


$(matchAll [e| ... |] [p|  |])

-}

-- f1 (_ ++ [x] ++ _) -- O(1), zählt aber nicht

-- f2 (_ ++ [x] ++ _ ++ [x+1] ++ _) -- O(n^2)

-- f3 (_ ++ [x] ++ _ ++ [x+1] ++ _ ++ [x+2] ++ _) -- O(n^3)

-- f2Helper x a b c = a ++ [x] ++ b ++ [x+1] ++ c

-- f2Helperr x y a b c = a ++ [x] ++ b ++ [y] ++ c

-- f3Helper x a b c d = a ++ [x] ++ b ++ [x+1] ++ c ++ [x+2] ++ d

-- f3Helperr x y z a b c d = a ++ [x] ++ b ++ [y] ++ c ++ [z] ++ d

-- f4Helper x a b c d e = a ++ [x] ++ b ++ [x+1] ++ c ++ [x+2] ++ d ++ [x+3] ++ e