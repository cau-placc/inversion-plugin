# Inversion plugin for GHC

This package offers a plugin for the Glasgow Haskell Compiler (GHC) that automatically generates inverted functions for each function definition in every module where the plugin is activated.
It also enables the use of functional patterns in Haskell.

The idea behind this plugin is originally described in the paper ["Haskell⁻¹: Automatic Function Inversion in Haskell"](https://doi.org/10.1145/3471874.3472982).

## Table of Contents

- [Inversion plugin for GHC](#inversion-plugin-for-ghc)
  - [Table of Contents](#table-of-contents)
  - [Compatibility](#compatibility)
  - [Building the plugin](#building-the-plugin)
  - [Configuring the plugin](#configuring-the-plugin)
  - [Using the plugin](#using-the-plugin)
    - [Inverted functions](#inverted-functions)
    - [Functional patterns](#functional-patterns)
  - [Using the plugin in a sandbox](#using-the-plugin-in-a-sandbox)
  - [Known issues](#known-issues)
  - [Debugging](#debugging)

## Compatibility

This plugin only works with GHC 9.2.4 and cannot be used with other versions.
It uses the tool [Stack](https://www.haskellstack.org) to automatically install the required GHC version and Haskell dependencies.

## Building the plugin

```
stack build inversion-plugin
```

## Configuring the plugin

The plugin can be configured using the following flags:

  - `--flag inversion-plugin:type-safe`: Enables type-safe inversion.

  - `--flag inversion-plugin:gen-solo`: Generate `Solo` tuples (default: off)
  - `--flag inversion-plugin:use-sbv`: Use SBV (default: on)
  - `--flag inversion-plugin:use-what4`: Use What4 (default: off)
  - `--flag inversion-plugin:use-cvc`: Use CVC4/5 (default: off)
  - `--flag inversion-plugin:use-z3`: Use Z3 (default: on)
  - `--flag inversion-plugin:use-dfs`: Perform depth-first search (default: off)
  - `--flag inversion-plugin:use-iddfs`: Perform iterative-deepening depth-first search (default: off)
  - `--flag inversion-plugin:use-bfs`: Perform breadth-first search (default: on)
  - `--flag inversion-plugin:use-cs`: Perform concurrent search (default: off)
  - `--flag inversion-plugin:use-ps`: Perform parallel search (default: off)

## Using the plugin

The plugin can be enabled it via a GHC pragma `{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}` at the top of a module.
If the plugin is enabled, it automatically generates inverted functions for each definition in the module.

```haskell
{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module ToBeInverted where

myAppend :: [a] -> [a] -> [a]
myAppend []     ys = ys
myAppend (x:xs) ys = x : myAppend xs ys

myLookup :: Eq k => k -> [(k, v)] -> Maybe v
myLookup k []          = Nothing
myLookup k ((k',v):xs)
  | k == k'          = Just v
  | otherwise        = myLookup k xs
```

These inverted functions cannot be used in the same module, but are automatically available whenever the module is imported in a different module.
There, one can use the inverted functions and functional patterns via Template Haskell meta functions as seen in the following examples (more examples can be found in the `sandbox/src` directory, see section [Using the plugin in a sandbox](#using-the-plugin-in-a-sandbox)).

### Inverted functions

```haskell
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module InvertedFunctions where

import Plugin.InversionPlugin

import ToBeInverted

-- Applying the inverted function of myAppend to [1,2,3].
-- ghci> $(inv 'myAppend) [1,2,3]
-- [([],[1,2,3]),([1],[2,3]),([1,2],[3]),([1,2,3],[])]
-- One can also use inverted functions to define new functions.
splits :: Invertible a => [a] -> [([a],[a])]
splits = $(inv 'myAppend)
-- ghci> splits [True,False]
-- [([],[True,False]),([True],[False]),([True,False],[])]
```

### Partially inverted functions

```haskell
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module PartiallyInvertedFunctions where

import Plugin.InversionPlugin

import ToBeInverted

-- Implementing a reverse lookup via a partially inverted function of myLookup.
-- The list argument `[2]` to `partialInv` denotes
-- that the second argument (the key-value list) is fixed.
reverseLookup :: (Invertible a, Invertible b, Eq a, Lifted (Eq a))
              => v -> [(k,v)] -> [k]
reverseLookup v xs = $(partialInv 'myLookup [2]) (Just v) xs
-- ghci> reverseLookup True [(1,True),(2,False),(3,True)]
-- [1,3]
```

As shown in the example above, the fixed arguments are specified by providing the indices of the corresponding arguments (starting at 1).
Note that one can fix more than one argument of a partially inverted function by giving more than one index in the first argument of `partialInv`.
However, the order and duplicates in the index list do not matter.
Consequently, `$(partialInv 'myLookup [1,2])` and `$(partialInv 'myLookup [2,1,1])` refer to the same partially inverted function.

### Semi-inverted functions

```haskell
{-# LANGUAGE TemplateHaskell, FlexibleContexts #-}
module SemiInvertedFunctions where

import Plugin.InversionPlugin

import ToBeInverted

TODO
```

### Functional patterns

```haskell
{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module FunctionalPatterns where

import Plugin.InversionPlugin

import ToBeInverted

-- Get the last element of a list.
-- The first argument of `funPat` is the quoted name of the function to be
-- used in the functional pattern.
-- All subsequent arguments have to be quasi-quoted patterns,
-- whose number has to match the arity of the function
-- in the functional pattern.
last :: Invertible a => [a] -> a
last ($funPat 'myAppend [p| _ |] [p| x |]) = x
last _                                     = error "last: empty list"
-- ghci> last [1,2,3]
-- 3
```

## Using the plugin in a sandbox

A sandbox project is available to play around with in `sandbox/`.
It can be loaded by executing `stack repl sandbox` from the root of the project.

## Known issues

* Compile time for the first module might be slow.
However, this is not the case for any subsequent modules that use the plugin.
* While some of the most common definitions from the Prelude are supported, some remain unsupported at the moment.
To support all definitions from the Prelude is part of future work.
* It not possible to enable the plugin in a module that uses inverted functions or functional patterns.
* Using `:r` in GHCi often does not work properly the first time.
Either, repeat `:r` a second time or reload the whole module with `:l <module>` instead.
* HIE and HaskellLanguageServer do not work with the plugin.
* Almost all language extensions are unsupported.
We only focused on supporting the Haskell2010 standard.

## Debugging

In order to see whether the plugin generates valid code, use the GHC option `-dcore-lint`.
This type checks the generated Core code and emits an error message when something went wrong.
We are very interested in finding those errors.
This option can also be turned on via the GHC pragma `{-# OPTIONS_GHC -dcore-lint #-}` at the top of modules that use the plugin.
