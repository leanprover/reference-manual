/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.BasicTypes.Nat
import Manual.BasicTypes.String
import Manual.BasicTypes.Array

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


#doc (Manual) "Basic Types" =>
%%%
tag := "basic-types"
%%%


Lean includes a number of built-in types that are specially supported by the compiler.
Some, such as {lean}`Nat`, additionally have special support in the kernel.
Other types don't have special compiler support _per se_, but rely in important ways on the internal representation of types for performance reasons.

{include 0 Manual.BasicTypes.Nat}

# Integers
%%%
tag := "Int"
%%%

::: planned 104
 * Compile-time and run-time characteristics, and how they're inherited from {lean}`Nat`
 * API reference
:::

# Fixed-Precision Integer Types
%%%
tag := "fixed-ints"
%%%


::: planned 105
 * Compile-time and run-time characteristics for {lean}`UInt8`, {lean}`UInt16`, {lean}`UInt32`, {lean}`UInt64`
 * API reference
:::

# Bitvectors
%%%
tag := "BitVec"
%%%


:::planned 106
 * Run-time and kernel representations of {name}`BitVec`
 * API reference
 * Cross-reference to TBW chapter on `bv_decide`
:::

# Floating-Point Numbers
%%%
tag := "Float"
%%%


:::planned 107
 * Run-time and kernel representations
 * Precision, and whether it's platform-dependent
 * Relationship between IEEE floats and decidable equality
:::

# Characters
%%%
tag := "Char"
%%%


{docstring Char}

## Syntax
%%%
tag := "char-syntax"
%%%


## Logical Model
%%%
tag := "char-model"
%%%

## Run-Time Representation
%%%
tag := "char-runtime"
%%%


In monomorphic contexts, characters are represented as 32-bit immediate values. In other words, a field of a constructor or structure of type `Char` does not require indirection to access. In polymorphic contexts, characters are boxed.


## API Reference
%%%
tag := "char-api"
%%%


### Character Classes
%%%
tag := "char-api-classes"
%%%


{docstring Char.isAlpha}

{docstring Char.isAlphanum}

{docstring Char.isDigit}

{docstring Char.isLower}

{docstring Char.isUpper}

{docstring Char.isWhitespace}

{include 0 Manual.BasicTypes.String}

# The Unit Type

{docstring Unit}

{docstring PUnit}

:::planned 161
 * Definitional equality
 * {lean}`Unit` vs {lean}`PUnit`
:::

# Booleans

{docstring Bool}

:::planned 162
 * Relationship to {lean}`Prop`
 * Laziness of `&&` etc
:::

# Linked Lists
%%%
tag := "List"
%%%


::: planned 108
 * Representation at compile time and run time
 * API reference
 * Literal syntax
 * Constructor/pattern syntax
:::


{include 0 Manual.BasicTypes.Array}


# Lazy Computations
%%%
tag := "Thunk"
%%%


::: planned 92
Description and API reference for {name}`Thunk`:
 * Logical model as wrapper around a function from {lean}`Unit`
 * Run-time realization as a lazy computation
 * API reference
:::

# Tasks and Threads
%%%
tag := "concurrency"
%%%


::: planned 90
Description and API reference for {name}`Task` and runtime threads, including {lean}`IO.Promise`

 * Scheduling model
 * Things to be careful of

This section may be moved to the section on {name}`IO` in particular.
:::
