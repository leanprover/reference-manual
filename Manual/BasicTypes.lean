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
#guard_msgs in
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
#guard_msgs in
#eval (2 = 2 : Bool)
end BoolProp
```

## Syntax

:::syntax term
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

:::syntax term
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

{docstring Bool.not}

{docstring Bool.and}

{docstring Bool.or}

{docstring Bool.xor}

{docstring Bool.atLeastTwo}

### Comparisons

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
