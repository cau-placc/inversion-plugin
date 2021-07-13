{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE GADTs           #-}

module App where

import Control.Egison

app2 l =
  match l (List Integer)
  [[mc| _ ++ [$x] ++ _ ++ [#(x+1)] ++ _ -> "Matched" |]
  , [mc| _ -> "Not matched" |]]

app3 l =
  match l (List Integer)
  [[mc| _ ++ [$x] ++ _ ++ [#(x+1)] ++ _ ++ [#(x+2)] ++ _ -> "Matched" |]
  , [mc| _ -> "Not matched" |]]

app4 l =
  match l (List Integer)
  [[mc| _ ++ [$x] ++ _ ++ [#(x+1)] ++ _ ++ [#(x+2)] ++ _ ++ [#(x+3)] ++ _ -> "Matched" |]
  , [mc| _ -> "Not matched" |]]

test2 n = concatMap (\m -> m : take n (repeat 42)) [0..10]
