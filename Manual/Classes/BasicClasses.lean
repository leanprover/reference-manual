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

{docstring Ordering}

{docstring LT}

{docstring LE}

# Decidability
%%%
tag := "decidable-propositions"
%%%

A proposition is {deftech}_decidable_ if it can be checked algorithmically.{index}[decidable]{index subterm:="decidable"}[proposition]
The Law of the Excluded Middle means that every proposition is true or false, but it provides no way to check which of the two cases holds, which can often be useful.
By default, only algorithmic {lean}`Decidable` instances for which code can be generated are in scope; opening the `Classical` namespace makes every proposition decidable.

{docstring Decidable}

{docstring DecidableRel}

{docstring DecidableEq}

{docstring Decidable.decide}

{docstring Decidable.byCases}

::::keepEnv
:::example "Excluded Middle and {lean}`Decidable`"
The equality of functions from {lean}`Nat` to {lean}`Nat` is not decidable:
```lean (error:=true) (name := NatFunNotDecEq)
example (f g : Nat → Nat) : Decidable (f = g) := inferInstance
```
```leanOutput NatFunNotDecEq
failed to synthesize
  Decidable (f = g)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

Opening `Classical` makes every proposition decidable; however, declarations and examples that use this fact must be marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` to indicate that code should not be generated for them.
```lean
open Classical
noncomputable example (f g : Nat → Nat) : Decidable (f = g) := inferInstance
```

:::
::::


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
