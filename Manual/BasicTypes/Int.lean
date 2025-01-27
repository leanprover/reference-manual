/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

#doc (Manual) "Integers" =>
%%%
tag := "Int"
%%%

The integers are whole numbers, both positive and negative.
Integers are arbitrary-precision, limited only by the capability of the hardware on which Lean is running; for fixed-width integers that are used in programming and computer science, please see the {ref "fixed-ints"}[section on fixed-precision integers].

Integers are specially supported by Lean's implementation.
The logical model of the integers is based on the natural numbers: each integer is modeled as either a natural number or the negative successor of a natural number.
Operations on the integers are specified using this model, which is used in the kernel and in interpreted code.
In these contexts, integer code inherits the performance benefits of the natural numbers' special support.
In compiled code, integers are represented as efficient arbitrary-precision integers, and sufficiently small numbers are stored as unboxed values that don't require indirection through a pointer.
Arithmetic operations are implemented by primitives that take advantage of the efficient representations.

# Logical Model
%%%
tag := "int-model"
%%%
Integers are represented either as a natural number or as the negation of the successor of a natural number.

{docstring Int}

This representation of the integers has a number of useful properties.
It is relatively simple to use and to understand.
Unlike a pair of a sign and a {lean}`Nat`, there is a unique representation for $`0`, which simplifies reasoning about equality.
Integers can also be represented as a pair of natural numbers in which one is subtracted from the other, but this requires a {ref "quotients"}[quotient type] to be well-behaved, and quotient types can be laborious to work with due to the need to prove that functions respect the equivalence relation.

# Run-Time Representation
%%%
tag := "int-runtime"
%%%

Like {ref "nat-runtime"}[natural numbers], sufficiently-small integers are represented as unboxed values: the lowest-order bit in an object pointer is used to indicate that the value is not, in fact, a pointer.
If an integer is too large to fit in the remaining bits, it is instead allocated as an ordinary Lean object that consists of an object header and an arbitrary-precision integer.

# Syntax
%%%
tag := "int-syntax"
%%%

```lean (show := false)
section
variable (n : Nat)
```

The {lean}`OfNat Int` instance allows numerals to be used as literals, both in expression and in pattern contexts.
{lean}`(OfNat.ofNat n : Int)` reduces to the constructor application {lean}`Int.ofNat n`.
The {inst}`Neg Int` instance allows negation to be used as well.

```lean (show := false)
open Int
```

On top of these instances, there is special syntax for the constructor {lean}`Int.negSucc` that is available when the `Int` namespace is opened.
The notation {lean}`-[ n +1]` is suggestive of $`-(n + 1)`, which is the meaning of {lean}`Int.negSucc n`.

:::syntax term (title := "Negative Successor")

{lean}`-[ n +1]` is notation for {lean}`Int.negSucc n`.

```grammar
-[ $_ +1]
```
:::

```lean (show := false)
end
```


# API Reference

## Properties

{docstring Int.sign}

## Conversions

{docstring Int.natAbs}

{docstring Int.toNat}

{docstring Int.toNat'}

{docstring Int.toISize}

{docstring Int.toInt16}

{docstring Int.toInt32}

{docstring Int.toInt64}

{docstring Int.toInt8}

{docstring Int.repr}

### Casts

{docstring IntCast}

{docstring Int.cast}

## Arithmetic

Typically, arithmetic operations on integers are accessed using Lean's overloaded arithmetic notation.
In particular, the instances of {inst}`Add Int`, {inst}`Neg Int`, {inst}`Sub Int`, and {inst}`Mul Int` allow ordinary infix operators to be used.
{ref "int-div"}[Division] is somewhat more intricate, because there are multiple sensible notions of division on integers.

{docstring Int.add}

{docstring Int.sub}

{docstring Int.subNatNat}

{docstring Int.neg}

{docstring Int.negOfNat}

{docstring Int.mul}

{docstring Int.pow}

{docstring Int.gcd}

{docstring Int.lcm}

### Division
%%%
tag := "int-div"
%%%
The {inst}`Div Int` and {inst}`Mod Int` instances implement Euclidean division, described in the reference for {name}`Int.ediv`.
This is not, however, the only sensible convention for rounding and remainders in division.
Four pairs of division and modulus functions are available, implementing various conventions.

:::example "Division by 0"
In all integer division conventions, division by {lean type:="Int"}`0` is defined to be {lean type:="Int"}`0`:

```lean (name := div0)
#eval Int.ediv 5 0
#eval Int.ediv 0 0
#eval Int.ediv (-5) 0
#eval Int.bdiv 5 0
#eval Int.bdiv 0 0
#eval Int.bdiv (-5) 0
#eval Int.fdiv 5 0
#eval Int.fdiv 0 0
#eval Int.fdiv (-5) 0
#eval Int.tdiv 5 0
#eval Int.tdiv 0 0
#eval Int.tdiv (-5) 0
```
All evaluate to 0.
```leanOutput div0
0
```
:::

{docstring Int.ediv}

{docstring Int.emod}

{docstring Int.bdiv}

{docstring Int.bmod}

{docstring Int.fdiv}

{docstring Int.fmod}

{docstring Int.tdiv}

{docstring Int.tmod}

## Bitwise Operators

Bitwise operators on {name}`Int` can be understood as bitwise operators on an infinite stream of bits that are the twos-complement representation of integers.

{docstring Int.not}

{docstring Int.shiftRight}

## Comparisons

Equality and inequality tests on {lean}`Int` are typically performed using the decidability of its equality and ordering relations or using the {inst}`BEq Int` and {inst}`Ord Int` instances.

```lean (show := false)
example (i j : Int) : Decidable (i ≤ j) := inferInstance
example (i j : Int) : Decidable (i < j) := inferInstance
example (i j : Int) : Decidable (i = j) := inferInstance
```

{docstring Int.le}

{docstring Int.lt}

{docstring Int.decEq}

## Proof Automation

The functions in this section are primarily parts of the implementation of simplification rules employed by {tactic}`simp`.
They are probably only of interest to users who are implementing custom proof automation that involves integers.


{docstring Int.fromExpr?}

{docstring Int.isPosValue}

{docstring Int.reduceAbs}

{docstring Int.reduceAdd}

{docstring Int.reduceBEq}

{docstring Int.reduceBNe}

{docstring Int.reduceBdiv}

{docstring Int.reduceBin}

{docstring Int.reduceBinIntNatOp}

{docstring Int.reduceBinPred}

{docstring Int.reduceBmod}

{docstring Int.reduceBoolPred}

{docstring Int.reduceDiv}

{docstring Int.reduceEq}

{docstring Int.reduceFDiv}

{docstring Int.reduceFMod}

{docstring Int.reduceGE}

{docstring Int.reduceGT}

{docstring Int.reduceLE}

{docstring Int.reduceLT}

{docstring Int.reduceMod}

{docstring Int.reduceMul}

{docstring Int.reduceNatCore}

{docstring Int.reduceNe}

{docstring Int.reduceNeg}

{docstring Int.reduceNegSucc}

{docstring Int.reduceOfNat}

{docstring Int.reducePow}

{docstring Int.reduceSub}

{docstring Int.reduceTDiv}

{docstring Int.reduceTMod}

{docstring Int.reduceToNat}

{docstring Int.reduceUnary}
