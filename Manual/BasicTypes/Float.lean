/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true

#doc (Manual) "Floating-Point Numbers" =>
%%%
tag := "Float"
%%%

Floating-point numbers are a an approximation of the real numbers that are efficiently implemented in computer hardware.
Computations that use floating-point numbers are very efficient; however, the nature of the way that they approximate the real numbers is complex, with many corner cases.
The IEEE 754 standard, which defines the floating-point format that is used on modern computers, allows hardware designers to make certain choices, and real systems differ in these small details.
For example, there are many distinct bit representations of `NaN`, the indicator that a result is undefined, and some platforms differ with respect to _which_ `NaN` is returned from adding two `NaN`s.

Lean exposes the underlying platform's floating-point values for use in programming, but they are not encoded in Lean's logic.
They are represented by an opaque type.
This means that the {tech}[kernel] is not capable of computing with or reasoning about floating-point values without additional {ref "axioms"}[axioms].
A consequence of this is that equality of floating-point numbers is not decidable.
Furthermore, comparisons between floating-point values are decidable, but the code that does so is opaque; in practice, the decision procedure can only be used in compiled code.

Lean provides two floating-point types: {name}`Float` represents 64-bit floating point values, while {name}`Float32` represents 32-bit floating point values.
The precision of {name}`Float` does not vary based on the platform that Lean is running on.


{docstring Float}

{docstring Float32}


:::example "No Kernel Reasoning About Floating-Point Numbers"
The Lean kernel can compare expressions of type {lean}`Float` for syntactic equality, so {lean type:="Float"}`0.0` is definitionally equal to itself.
```lean
example : (0.0 : Float) = (0.0 : Float) := by rfl
```

Terms that require reduction to become syntactically equal cannot be checked by the kernel:
```lean (error := true) (name := zeroPlusZero)
example : (0.0 : Float) = (0.0 + 0.0 : Float) := by rfl
```
```leanOutput zeroPlusZero
tactic 'rfl' failed, the left-hand side
  0.0
is not definitionally equal to the right-hand side
  0.0 + 0.0
⊢ 0.0 = 0.0 + 0.0
```

Similarly, the kernel cannot evaluate {lean}`Bool`-valued comparisons of floating-point numbers while checking definitional equality:
```lean (error := true) (name := zeroPlusZero') (keep := false)
theorem Float.zero_eq_zero_plus_zero :
    ((0.0 : Float) == (0.0 + 0.0 : Float)) = true :=
  by rfl
```
```leanOutput zeroPlusZero'
tactic 'rfl' failed, the left-hand side
  0.0 == 0.0 + 0.0
is not definitionally equal to the right-hand side
  true
⊢ (0.0 == 0.0 + 0.0) = true
```


However, the {tactic}`native_decide` tactic can invoke the underlying platform's floating-point primitives that are used by Lean for run-time programs:
```lean
theorem Float.zero_eq_zero_plus_zero :
    ((0.0 : Float) == (0.0 + 0.0 : Float)) = true := by
  native_decide
```
This tactic uses the axiom {name}`Lean.ofReduceBool`, which states that the Lean compiler, interpreter and the low-level implementations of built-in operators are trusted in addition to the kernel.
```lean (name := ofRed)
#print axioms Float.zero_eq_zero_plus_zero
```
```leanOutput ofRed
'Float.zero_eq_zero_plus_zero' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool]
```
:::

:::example "Floating-Point Equality Is Not Reflexive"
Floating-point operations may produce `NaN` values that indicate an undefined result.
These values are not comparable with each other; in particular, all comparisons involving `NaN` will return `false`, including equality.
```lean
#eval ((0.0 : Float) / 0.0) == ((0.0 : Float) / 0.0)
```
:::

:::example "Floating-Point Equality Is Not a Congruence"
Applying a function to two equal floating-point numbers may not result in equal numbers.
In particular, positive and negative zero are distinct values that are equated by floating-point equality, but division by positive or negative zero yields positive or negative infinite values.
```lean (name := divZeroPosNeg)
def neg0 : Float := -0.0

def pos0 : Float := 0.0

#eval (neg0 == pos0, 1.0 / neg0 == 1.0 / pos0)
```
```leanOutput divZeroPosNeg
(true, false)
```
:::


# Syntax

Lean does not have dedicated floating-point literals.
Instead, floating-point literals are resolved via the appropriate instances of the {name}`OfScientific` and {name}`Neg` type classes.

:::example "Floating-Point Literals"

The term
```leanTerm
(-2.523 : Float)
```
is syntactic sugar for
```leanTerm
(Neg.neg (OfScientific.ofScientific 22523 true 4) : Float)
```
and the term
```leanTerm
(413.52 : Float32)
```
is syntactic sugar for
```leanTerm
(OfScientific.ofScientific 41352 true 2 : Float32)
```

```lean (show := false)
example : (-2.2523 : Float) = (Neg.neg (OfScientific.ofScientific 22523 true 4) : Float) := by simp [OfScientific.ofScientific]
example : (413.52 : Float32) = (OfScientific.ofScientific 41352 true 2 : Float32) := by simp [OfScientific.ofScientific]
```
:::

# API Reference
%%%
tag := "Float-api"
%%%

## Properties

Floating-point numbers fall into one of three categories:

 * Finite numbers are ordinary floating-point values.

 * Infinities, which may be positive or negative, result from division by zero.

 * `NaN`s, which are not numbers, result from other undefined operations, such as the square root of a negative number.

{docstring Float.isInf}

{docstring Float32.isInf}

{docstring Float.isNaN}

{docstring Float32.isNaN}

{docstring Float.isFinite}

{docstring Float32.isFinite}


## Syntax

These operations exist to support the {inst}`OfScientific Float` and {inst}`OfScientific Float32` instances and are normally invoked indirectly as a result of a literal value.

{docstring Float.ofScientific}

{docstring Float32.ofScientific}


## Conversions

{docstring Float.toBits}

{docstring Float32.toBits}

{docstring Float.ofBits}

{docstring Float32.ofBits}

{docstring Float.toFloat32}

{docstring Float32.toFloat}

{docstring Float.toString}

{docstring Float32.toString}

{docstring Float.toUInt8}

{docstring Float.toInt8}

{docstring Float32.toUInt8}

{docstring Float32.toInt8}

{docstring Float.toUInt16}

{docstring Float.toInt16}

{docstring Float32.toUInt16}

{docstring Float32.toInt16}

{docstring Float.toUInt32}

{docstring Float32.toUInt32}

{docstring Float.toInt32}

{docstring Float32.toInt32}

{docstring Float.toUInt64}

{docstring Float.toInt64}

{docstring Float32.toUInt64}

{docstring Float32.toInt64}

{docstring Float.toUSize}

{docstring Float32.toUSize}

{docstring Float.toISize}

{docstring Float32.toISize}

{docstring Float.ofInt}

{docstring Float32.ofInt}

{docstring Float.ofNat}

{docstring Float32.ofNat}

{docstring Float.ofBinaryScientific}

{docstring Float32.ofBinaryScientific}

{docstring Float.frExp}

{docstring Float32.frExp}

## Comparisons

{docstring Float.beq}

{docstring Float32.beq}

### Inequalities

The decision procedures for inequalities are opaque constants in the logic.
They can only be used via the {name}`Lean.ofReduceBool` axiom, e.g. via the {tactic}`native_decide` tactic.

{docstring Float.le}

{docstring Float32.le}

{docstring Float.lt}

{docstring Float32.lt}

{docstring Float.decLe}

{docstring Float32.decLe}

{docstring Float.decLt}

{docstring Float32.decLt}

## Arithmetic

Arithmetic operations on floating-point values are typically invoked via the {inst}`Add Float`, {inst}`Sub Float`, {inst}`Mul Float`, {inst}`Div Float`, and {inst}`HomogeneousPow Float` instances, along with the corresponding {name}`Float32` instances.

{docstring Float.add}

{docstring Float32.add}

{docstring Float.sub}

{docstring Float32.sub}

{docstring Float.mul}

{docstring Float32.mul}

{docstring Float.div}

{docstring Float32.div}

{docstring Float.pow}

{docstring Float32.pow}

{docstring Float.exp}

{docstring Float32.exp}

{docstring Float.exp2}

{docstring Float32.exp2}

### Roots

Computing the square root of a negative number yields `NaN`.

{docstring Float.sqrt}

{docstring Float32.sqrt}

{docstring Float.cbrt}

{docstring Float32.cbrt}

## Logarithms

{docstring Float.log}

{docstring Float32.log}

{docstring Float.log10}

{docstring Float32.log10}

{docstring Float.log2}

{docstring Float32.log2}

## Scaling

{docstring Float.scaleB}

{docstring Float32.scaleB}

## Rounding

{docstring Float.round}

{docstring Float32.round}

{docstring Float.floor}

{docstring Float32.floor}

{docstring Float.ceil}

{docstring Float32.ceil}

## Trigonometry

### Sine

{docstring Float.sin}

{docstring Float32.sin}

{docstring Float.sinh}

{docstring Float32.sinh}

{docstring Float.asin}

{docstring Float32.asin}

{docstring Float.asinh}

{docstring Float32.asinh}

### Cosine

{docstring Float.cos}

{docstring Float32.cos}

{docstring Float.cosh}

{docstring Float32.cosh}

{docstring Float.acos}

{docstring Float32.acos}

{docstring Float.acosh}

{docstring Float32.acosh}

### Tangent

{docstring Float.tan}

{docstring Float32.tan}

{docstring Float.tanh}

{docstring Float32.tanh}

{docstring Float.atan}

{docstring Float32.atan}

{docstring Float.atanh}

{docstring Float32.atanh}

{docstring Float.atan2}

{docstring Float32.atan2}

## Negation and Absolute Value

{docstring Float.abs}

{docstring Float32.abs}

{docstring Float.neg}

{docstring Float32.neg}
