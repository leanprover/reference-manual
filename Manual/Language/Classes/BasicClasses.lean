/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Basic Classes" =>
%%%
tag := "basic-classes"
%%%

Many Lean type classes exist in order to allow built-in notations such as addition or array indexing to be overloaded.

# Boolean Equality Tests

{docstring BEq}

{docstring Hashable}

{docstring LawfulBEq}

# Ordering

{docstring Ord}

{docstring LT}

{docstring LE}

# Decidability

{docstring Decidable}

{docstring DecidableRel}

{docstring DecidableEq}

# Inhabited Types

{docstring Inhabited}

{docstring Nonempty}

# Visible Representations

:::planned 135

 * How to write a correct {name}`Repr` instance
 * {name}`ReprAtom`
 * Useful helpers, like {name}`Repr.addAppParen` and {name}`reprArg`
 * When to use {name}`Repr` vs {name}`ToString`
:::

{docstring Repr}

{docstring ToString}

# Arithmetic and Bitwise Operators

{docstring Zero}

{docstring NeZero}

{docstring HAdd}

{docstring Add}

{docstring HSub}

{docstring Sub}

{docstring HMul}

{docstring Mul}

{docstring HDiv}

{docstring Div}

{docstring Dvd}

{docstring HMod}

{docstring Mod}

{docstring HPow}

{docstring Pow}

{docstring NatPow}

{docstring HomogeneousPow}

{docstring HShiftLeft}

{docstring ShiftLeft}

{docstring HShiftRight}

{docstring ShiftRight}

{docstring Neg}

{docstring HAnd}

{docstring HOr}

{docstring HXor}

# Append

{docstring HAppend}

{docstring Append}

# Data Lookups

{docstring GetElem}

{docstring GetElem?}

{docstring LawfulGetElem}
