/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.BasicTypes.Nat
import Manual.BasicTypes.Int
import Manual.BasicTypes.String
import Manual.BasicTypes.Array
import Manual.BasicTypes.Fin
import Manual.BasicTypes.UInt
import Manual.BasicTypes.BitVec
import Manual.BasicTypes.Float
import Manual.BasicTypes.Char
import Manual.BasicTypes.Option
import Manual.BasicTypes.Empty
import Manual.BasicTypes.Products
import Manual.BasicTypes.Sum
import Manual.BasicTypes.List
import Manual.BasicTypes.Maps
import Manual.BasicTypes.Subtype
import Manual.BasicTypes.Thunk

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Basic Types" =>
%%%
tag := "basic-types"
%%%


Lean includes a number of built-in types that are specially supported by the compiler.
Some, such as {lean}`Nat`, additionally have special support in the kernel.
Other types don't have special compiler support _per se_, but rely in important ways on the internal representation of types for performance reasons.

{include 0 Manual.BasicTypes.Nat}

{include 0 Manual.BasicTypes.Int}

{include 0 Manual.BasicTypes.Fin}

{include 0 Manual.BasicTypes.UInt}

{include 0 Manual.BasicTypes.BitVec}

{include 0 Manual.BasicTypes.Float}

{include 0 Manual.BasicTypes.Char}


{include 0 Manual.BasicTypes.String}

# The Unit Type

The unit type is the canonical type with exactly one element, named {name Unit.unit}`unit` and represented by the empty tuple {lean}`()`.
It describes only a single value, which consists of said constructor applied to no arguments whatsoever.

{lean}`Unit` is analogous to `void` in languages derived from C: even though `void` has no elements that can be named, it represents the return of control flow from a function with no additional information.
In functional programming, {lean}`Unit` is the return type of things that "return nothing".
Mathematically, this is represented by a single completely uninformative value, as opposed to an empty type such as {lean}`Empty`, which represents unreachable code.

:::leanSection
```lean (show := false)
variable {m : Type → Type} [Monad m] {α : Type}
```

When programming with {ref "monads-and-do"}[monads], {lean}`Unit` is especially useful.
For any type {lean}`α`, {lean}`m α` represents an action that has side effects and returns a value of type {lean}`α`.
The type {lean}`m Unit` represents an action that has some side effects but does not return a value.

:::



There are two variants of the unit type:

 * {lean}`Unit` is a {lean}`Type` that exists in the smallest non-propositional {tech}[universe].

 * {lean}`PUnit` is {tech key:="universe polymorphism"}[universe polymorphic] and can be used in any non-propositional {tech}[universe].

Behind the scenes, {lean}`Unit` is actually defined as {lean}`PUnit.{1}`.
{lean}`Unit` should be preferred over {name}`PUnit` when possible to avoid unnecessary universe parameters.
If in doubt, use {lean}`Unit` until universe errors occur.

{docstring Unit}

{docstring Unit.unit}

{docstring PUnit}

## Definitional Equality

{deftech}_Unit-like types_ are inductive types that have a single constructor which takes no non-proof parameters.
{lean}`PUnit` is one such type.
All elements of unit-like types are {tech key:="definitional equality"}[definitionally equal] to all other elements.

:::example "Definitional Equality of {lean}`Unit`"
Every term with type {lean}`Unit` is definitionally equal to every other term with type {lean}`Unit`:

```lean
example (e1 e2 : Unit) : e1 = e2 := rfl
```
:::

::::keepEnv
:::example "Definitional Equality of Unit-Like Types"

Both {lean}`CustomUnit` and {lean}`AlsoUnit` are unit-like types, with a single constructor that takes no parameters.
Every pair of terms with either type is definitionally equal.

```lean
inductive CustomUnit where
  | customUnit

example (e1 e2 : CustomUnit) : e1 = e2 := rfl

structure AlsoUnit where

example (e1 e2 : AlsoUnit) : e1 = e2 := rfl
```

Types with parameters, such as {lean}`WithParam`, are also unit-like if they have a single constructor that does not take parameters.

```lean
inductive WithParam (n : Nat) where
  | mk

example (x y : WithParam 3) : x = y := rfl
```

Constructors with non-proof parameters are not unit-like, even if the parameters are all unit-like types.
```lean
inductive NotUnitLike where
  | mk (u : Unit)
```

```lean (error:=true) (name := NotUnitLike)
example (e1 e2 : NotUnitLike) : e1 = e2 := rfl
```
```leanOutput NotUnitLike
type mismatch
  rfl
has type
  ?m.13 = ?m.13 : Prop
but is expected to have type
  e1 = e2 : Prop
```

Constructors of unit-like types may take parameters that are proofs.
```lean
inductive ProofUnitLike where
  | mk : 2 = 2 → ProofUnitLike

example (e1 e2 : ProofUnitLike) : e1 = e2 := rfl
```
:::
::::

{include 0 Manual.BasicTypes.Empty}


# Booleans

{docstring Bool}

The constructors {lean}`Bool.true` and {lean}`Bool.false` are exported from the {lean}`Bool` namespace, so they can be written {lean}`true` and {lean}`false`.

## Run-Time Representation

Because {lean}`Bool` is an {tech}[enum inductive] type, it is represented by a single byte in compiled code.

## Booleans and Propositions

Both {lean}`Bool` and {lean}`Prop` represent notions of truth.
From a purely logical perspective, they are equivalent: {tech}[propositional extensionality] means that there are fundamentally only two propositions, namely {lean}`True` and {lean}`False`.
However, there is an important pragmatic difference: {lean}`Bool` classifies _values_ that can be computed by programs, while {lean}`Prop` classifies statements for which code generation doesn't make sense.
In other words, {lean}`Bool` is the notion of truth and falsehood that's appropriate for programs, while {lean}`Prop` is the notion that's appropriate for mathematics.
Because proofs are erased from compiled programs, keeping {lean}`Bool` and {lean}`Prop` distinct makes it clear which parts of a Lean file are intended for computation.

```lean (show := false)
section BoolProp

axiom b : Bool

/-- info: b = true : Prop -/
#check_msgs in
#check (b : Prop)

example : (true = true) = True := by simp

#check decide
```

A {lean}`Bool` can be used wherever a {lean}`Prop` is expected.
There is a {tech}[coercion] from every {lean}`Bool` {lean}`b` to the proposition {lean}`b = true`.
By {lean}`propext`, {lean}`true = true` is equal to {lean}`True`, and {lean}`false = true` is equal to {lean}`False`.

Not every proposition can be used by programs to make run-time decisions.
Otherwise, a program could branch on whether the Collatz conjecture is true or false!
Many propositions, however, can be checked algorithmically.
These propositions are called {tech}_decidable_ propositions, and have instances of the {lean}`Decidable` type class.
The function {name}`Decidable.decide` converts a proof-carrying {lean}`Decidable` result into a {lean}`Bool`.
This function is also a coercion from decidable propositions to {lean}`Bool`, so {lean}`(2 = 2 : Bool)` evaluates to {lean}`true`.

```lean (show := false)
/-- info: true -/
#check_msgs in
#eval (2 = 2 : Bool)
end BoolProp
```

## Syntax

:::syntax term (title := "Boolean Infix Operators")
The infix operators `&&`, `||`, and `^^` are notations for {lean}`Bool.and`, {lean}`Bool.or`, and {lean}`Bool.xor`, respectively.

```grammar
$_:term && $_:term
```
```grammar
$_:term || $_:term
```
```grammar
$_:term ^^ $_:term
```
:::

:::syntax term (title := "Boolean Negation")
The prefix operator `!` is notation for {lean}`Bool.not`.
```grammar
!$_:term
```
:::


## API Reference

### Logical Operations

```lean (show := false)
section ShortCircuit

axiom BIG_EXPENSIVE_COMPUTATION : Bool
```

The functions {name}`cond`, {name Bool.and}`and`, and {name Bool.or}`or` are short-circuiting.
In other words, {lean}`false && BIG_EXPENSIVE_COMPUTATION` does not need to execute {lean}`BIG_EXPENSIVE_COMPUTATION` before returning `false`.
These functions are defined using the {attr}`macro_inline` attribute, which causes the compiler to replace calls to them with their definitions while generating code, and the definitions use nested pattern matching to achieve the short-circuiting behavior.

```lean (show := false)
end ShortCircuit
```


{docstring cond}

{docstring Bool.dcond}

{docstring Bool.not}

{docstring Bool.and}

{docstring Bool.or}

{docstring Bool.xor}

### Comparisons

Most comparisons on Booleans should be performed using the {inst}`DecidableEq Bool`, {inst}`LT Bool`, {inst}`LE Bool` instances.

{docstring Bool.decEq}

### Conversions

{docstring Bool.toISize}

{docstring Bool.toUInt8}

{docstring Bool.toUInt16}

{docstring Bool.toUInt32}

{docstring Bool.toUInt64}

{docstring Bool.toUSize}

{docstring Bool.toInt8}

{docstring Bool.toInt16}

{docstring Bool.toInt32}

{docstring Bool.toInt64}

{docstring Bool.toNat}

{docstring Bool.toInt}


{include 0 Manual.BasicTypes.Option}

{include 0 Manual.BasicTypes.Products}

{include 0 Manual.BasicTypes.Sum}

{include 0 Manual.BasicTypes.List}

{include 0 Manual.BasicTypes.Array}

{include 0 Manual.BasicTypes.Maps}

{include 0 Manual.BasicTypes.Subtype}

{include 0 Manual.BasicTypes.Thunk}
