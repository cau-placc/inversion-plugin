{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module InstanceImport where

import InstanceExport

data Foo = Foo
  deriving Show

odd :: Id Int
odd = Id 2

test1 :: Id Int
test1 = return 3

test2 :: Id Int
test2 = const (return 42) False

test3 :: Id Foo
test3 = Id Foo

test4 :: String
test4 = show test3

test5 :: String
test5 = show (Id Foo)
