/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.BuiltInTypes.Nat
import Manual.BuiltInTypes.String

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


#doc (Manual) "Built-In Types" =>

Lean includes a number of built-in datatypes that are specially supported by the compiler.
Some additionally have special support in the kernel.

{include 0 Manual.BuiltInTypes.Nat}

# Fixed-Precision Integer Types



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

{include 0 Manual.BuiltInTypes.String}

# Arrays
