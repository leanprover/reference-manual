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
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Basic Classes" =>
%%%
tag := "basic-classes"
%%%

Many Lean type classes exist in order to allow built-in notations such as addition or array indexing to be overloaded.

# Boolean Equality Tests

The Boolean equality operator `==` is overloaded by defining instances of `BEq`.
The companion class `Hashable` specifies a hashing procedure for a type.
When a type has both `BEq` and `Hashable` instances, then the hashes computed should respect the `BEq` instance: two values equated by `BEq.bEq` should always have the same hash.

{docstring BEq}

{docstring Hashable}

{docstring mixHash}

{docstring LawfulBEq}

{docstring EquivBEq}

{docstring LawfulHashable}

{docstring hash_eq}

# Ordering

There are two primary ways to order the values of a type:
 * The {name}`Ord` type class provides a three-way comparison operator, {name}`compare`, which can indicate that one value is less than, equal to, or greater than another. It returns an {name}`Ordering`.
 * The {name}`LT` and {name}`LE` classes provide canonical {lean}`Prop`-valued ordering relations for a type that do not need to be decidable. These relations are used to overload the `<` and `≤` operators.

{docstring Ord}

The {name}`compare` method is exported, so no explicit `Ord` namespace is required to use it.

{docstring compareOn}

{docstring Ord.opposite}

{docstring Ordering}

{docstring Ordering.swap}

{docstring Ordering.then}

{docstring Ordering.isLT}

{docstring Ordering.isLE}

{docstring Ordering.isEq}

{docstring Ordering.isNe}

{docstring Ordering.isGE}

{docstring Ordering.isGT}

{docstring compareOfLessAndEq}

{docstring compareOfLessAndBEq}

{docstring compareLex}

:::syntax term (title := "Ordering Operators")

The less-than operator is overloaded in the {name}`LT` class:

```grammar
$_ < $_
```

The less-than-or-equal-to operator is overloaded in the {name}`LE` class:

```grammar
$_ ≤ $_
```

The greater-than and greater-than-or-equal-to operators are the reverse of the less-than and less-than-or-equal-to operators, and cannot be independently overloaded:

```grammar
$_ > $_
```

```grammar
$_ ≥ $_
```

:::

{docstring LT}

{docstring LE}

An {name}`Ord` can be used to construct {name}`BEq`, {name}`LT`, and {name}`LE` instances with the following helpers.
They are not automatically instances because many types are better served by custom relations.

{docstring ltOfOrd}

{docstring leOfOrd}

{docstring Ord.toBEq}

{docstring Ord.toLE}

{docstring Ord.toLT}

:::example "Using `Ord` Instances for `LT` and `LE` Instances"

Lean can automatically derive an {name}`Ord` instance.
In this case, the {inst}`Ord Vegetable` instance compares vegetables lexicographically:
```lean
structure Vegetable where
  color : String
  size : Fin 5
deriving Ord
```

```lean
def broccoli : Vegetable where
  color := "green"
  size := 2

def sweetPotato : Vegetable where
  color := "orange"
  size := 3
```


Using the helpers {name}`ltOfOrd` and {name}`leOfOrd`, {inst}`LT Vegetable` and {inst}`LE Vegetable` instances can be defined.
These instances compare the vegetables using {name}`compare` and logically assert that the result is as expected.
```lean
instance : LT Vegetable := ltOfOrd
instance : LE Vegetable := leOfOrd
```

The resulting relations are decidable because equality is decidable for {lean}`Ordering`:

```lean (name := brLtSw)
#eval broccoli < sweetPotato
```
```leanOutput brLtSw
true
```
```lean (name := brLeSw)
#eval broccoli ≤ sweetPotato
```
```leanOutput brLeSw
true
```
```lean (name := brLtBr)
#eval broccoli < broccoli
```
```leanOutput brLtBr
false
```
```lean (name := brLeBr)
#eval broccoli ≤ broccoli
```
```leanOutput brLeBr
true
```
:::

## Instance Construction

{docstring Ord.lex}

{docstring Ord.lex'}

{docstring Ord.on}

# Minimum and Maximum Values

The classes `Max` and `Min` provide overloaded operators for choosing the greater or lesser of two values.
These should be in agreement with `Ord`, `LT`, and `LE` instances, if they exist, but there is no mechanism to enforce this.

{docstring Min}

{docstring Max}

:::leanSection

```lean (show := false)
variable {α : Type u} [LE α]
```

Given an {inst}`LE α` instance for which {name}`LE.le` is decidable, the helpers {name}`minOfLe` and {name}`maxOfLe` can be used to create suitable {lean}`Min α` and {lean}`Max α` instances.
They can be used as the right-hand side of an {keywordOf Lean.Parser.Command.declaration}`instance` declaration.

{docstring minOfLe}

{docstring maxOfLe}

:::

# Decidability
%%%
tag := "decidable-propositions"
%%%

A proposition is {deftech}_decidable_ if it can be checked algorithmically.{index}[decidable]{index subterm:="decidable"}[proposition]
The Law of the Excluded Middle means that every proposition is true or false, but it provides no way to check which of the two cases holds, which can often be useful.
By default, only algorithmic {lean}`Decidable` instances for which code can be generated are in scope; opening the `Classical` namespace makes every proposition decidable.

{docstring Decidable}

{docstring DecidablePred}

{docstring DecidableRel}

{docstring DecidableEq}

{docstring DecidableLT}

{docstring DecidableLE}

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

# Subsingleton Types

{docstring Subsingleton}

{docstring Subsingleton.elim}

{docstring Subsingleton.helim}

# Visible Representations
%%%
draft := true
%%%

:::planned 135
 * ToString
 * xref to Repr section
 * When to use {name}`Repr` vs {name}`ToString`
:::


{docstring ToString (allowMissing := true)}

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
