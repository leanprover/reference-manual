/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.BasicTypes.Nat
import Manual.BasicTypes.String

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


#doc (Manual) "Basic Types" =>

Lean includes a number of built-in datatypes that are specially supported by the compiler.
Some, such as {lean}`Nat`, additionally have special support in the kernel.
Other types don't have special compiler support _per se_, but rely in important ways on the internal representation of types for performance reasons.

{include 0 Manual.BasicTypes.Nat}

# Integers

# Fixed-Precision Integer Types

# Floating-Point Numbers

# Characters

{docstring Char}

## Syntax

## Logical Model



## Run-Time Representation

In monomorphic contexts, characters are represented as 32-bit immediate values. In other words, a field of a datatype or structure of type `Char` does not require indirection to access. In polymorphic contexts, characters are boxed.


## API Reference

### Character Classes

{docstring Char.isAlpha}

{docstring Char.isAlphanum}

{docstring Char.isDigit}

{docstring Char.isLower}

{docstring Char.isUpper}

{docstring Char.isWhitespace}


{include 0 Manual.BasicTypes.String}

# Linked Lists

# Arrays

::: planned 91
Description and API reference for {name}`Thunk`:
 * Logical model as wrapper around a function from {lean}`Unit`
 * Run-time realization as a lazy computation
 * API reference
:::


# Lazy Computations

::: planned 92
Description and API reference for {name}`Thunk`:
 * Logical model as wrapper around a function from {lean}`Unit`
 * Run-time realization as a lazy computation
 * API reference
:::

# Tasks and Threads

::: planned 90
Description and API reference for {name}`Task` and runtime threads, including {lean}`IO.Promise`

 * Scheduling model
 * Things to be careful of

This section may be moved to the section on {name}`IO` in particular.
:::
