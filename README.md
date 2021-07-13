# Inversion plugin for GHC

This package offers a plugin for the Glasgow Haskell Compiler (GHC) that automatically generates (partial) inverse functions for each definition in every module where the plugin is activated.
It also enables the use of functional patterns in Haskell.

The idea behind this plugin is described in the paper ["Haskell⁻¹: Automatic Function Inversion in Haskell"](https://doi.org/10.1145/3471874.3472982).

## Table of Contents

- [Inversion plugin for GHC](#inversion-plugin-for-ghc)
  * [Table of Contents](#table-of-contents)
  * [Compatibility](#compatibility)
  * [Using the plugin](#using-the-plugin)
    + [(Partial) inverses](#-partial--inverses)
    + [Functional patterns](#functional-patterns)
  * [Using the plugin in a sandbox](#using-the-plugin-in-a-sandbox)
  * [Known issues](#known-issues)
  * [Debugging](#debugging)

## Compatibility

This plugin only works with GHC 8.10.4 and cannot be used with other versions.
It uses the tool [Stack](https://www.haskellstack.org) to automatically install the required version and Haskell dependencies.

## Using the plugin

The plugin can be enabled it via a GHC pragma `{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}` at the top of a module.
If the plugin is enabled, it automatically generates (partial) inverses for each definition in the module.
```haskell
{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module Inverses where

import Prelude hiding ((++), lookup, Maybe(..))

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

data Maybe a = Nothing
             | Just a
  deriving Show

lookup :: Eq k => k -> [(k, v)] -> Maybe v
lookup k []          = Nothing
lookup k ((k',v):xs)
  | k == k'          = Just v
  | otherwise        = lookup k xs
```

These inverses cannot be used in the same module, but are automatically available whenever the module is imported in a different module.
There, one can use the (partial) inverses and functional pattens via Template Haskell meta functions as seen in the following examples (more examples can be found in the `sandbox/src` directory, see section [Using the plugin in a sandbox](#using-the-plugin-in-a-sandbox)).

### (Partial) inverses

```haskell
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module UsingInverses where

import Prelude hiding ((++), lookup)

import Plugin.InversionPlugin

import Inverses

-- Applying the inverse of (+++) to [1,2,3].
-- ghci> $(inv '(++)) [1,2,3]
-- [([],[1,2,3]),([1],[2,3]),([1,2],[3]),([1,2,3],[])]
-- One can also use inverses to define new functions.
splits :: Invertible a => [a] -> [([a],[a])]
splits = $(inv '(++))
-- ghci> splits [True,False]
-- [([],[True,False]),([True],[False]),([True,False],[])]

-- Implementing a reverse lookup via a partial inverse of lookup.
-- The list argument `[2]` to `partialInv` denotes
-- that the second argument (key-value list) is fixed.
reverseLookup :: (Invertible a, Invertible b, Eq a, Lifted (Eq a))
              => v -> [(k,v)] -> [k]
reverseLookup v xs = $(partialInv 'lookup [2]) (Just v) xs
-- ghci> reverseLookup True [(1,True),(2,False),(3,True)]
-- [1,3]
```
As shown in the example above, the fixed arguments are specified by providing the indices of the corresponding arguments (starting at 1).
Note that one can fix more than one argument of a partial inverse by giving more than one index in the first argument of `partialInv`.
However, the order and duplicates in the index list do not matter.
Consequently, `$(partialInv 'lookup [1,2])` and `$(partialInv 'lookup [2,1,1])` refer to the same partial inverse.

### Functional patterns

```haskell
{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module UsingFunctionalPatterns where

import Prelude hiding ((++), lookup)

import Plugin.InversionPlugin

import Inverses

-- Get the last element of a list.
-- The first argument of `funPat` is the quoted name of the function to be
-- used in the functional pattern.
-- All subsequent arguments have to be quasi-quoted patterns,
-- whose number has to match the arity of the function
-- in the functional pattern.
last :: Invertible a => [a] -> a
last ($funPat '(++) [p| _ |] [p| x |]) = x
last _                                  = error "last: empty list"
-- ghci> last [1,2,3]
-- 3
```

## Using the plugin in a sandbox

A sandbox project is available to play around with in `sandbox/`.
It can be loaded by executing `stack repl sandbox:lib` from the root of the project.

## Known issues

* Compile time for the first module is slow (~3s).
However, this is not the case for any subsequent module that uses the plugin.
* Most of the definitions from the Prelude are not supported at the moment.
For now, the best idea is to not use any imported definitions from the Prelude or other modules.
We will lift this restriction in the future.
* At the moment, it not possible to enable the plugin in a module that uses (partial) inverses or functional patterns.
* Using `:r` in GHCi often does not work.
Reload the whole module with `:l <module>` instead.
* HIE and HaskellLanguageServer do not work.
* ~~Stack outputs some decoding failures while compiling the project.
This can be ignored safely.~~
Fixed with stack version 2.3.3 and later.
* Almost all language extensions are unsupported.
We only focused on Haskell2010.

## Debugging

In order to see whether the plugin generates valid code, use the GHC option `-dcore-lint`.
This type checks the generated Core code and emits an error message when something went wrong.
We are very interested in finding those errors.
This option can also be turned on via the GHC pragma `{-# OPTIONS_GHC -dcore-lint #-}` at the top of modules that use the plugin.
