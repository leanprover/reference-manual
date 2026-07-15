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
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Floating-Point Numbers" =>
%%%
tag := "Float"
%%%

Floating-point numbers are a an approximation of the real numbers that are efficiently implemented in computer hardware.
Computations that use floating-point numbers are very efficient; however, the nature of the way that they approximate the real numbers is complex, with many corner cases.
The IEEE 754 standard, which defines the floating-point format that is used on modern computers, allows hardware designers and programming language implementations to make certain choices, and real systems differ in these small details.
Any given combination of hardware, operating system, C compiler, library versions, and even compilation flags can result in different behavior.
For example, there are many distinct bit representations of `NaN`, the indicator that a result is undefined, and some platforms differ with respect to _which_ `NaN` is returned from adding two `NaN`s.

To enable reasoning about floating-point numbers, Lean exposes a logical model of {name}`Float` that is used in proofs.
In particular, {name}`Float` and {name}`Float32` are implemented as wrappers around the logical model.
In compiled code, this logical model is replaced by efficient native code.
Differences between platforms are resolved by choosing specific representations (for example, all `NaN` values are replaced by a single canonical `NaN` when any operation requests a bit representation) and by modeling only the subset of floating-point operations that are implemented identically on all supported platforms.
Other operations, such as trigonometric functions, are represented as opaque functions in Lean's logic.

The logical model is extensively empirically tested against the floating-point operations on all supported platforms.
As long as FFI code does not modify the floating-point environment, Lean's runtime floating-point primitives match the model's specification.

{docstring Float}

{docstring Float32}

# Logical Model

Lean provides two floating-point types: {name}`Float` represents 64-bit floating-point values, while {name}`Float32` represents 32-bit floating-point values.
The precision of {name}`Float` does not vary based on the platform that Lean is running on.

## Model Details

The logical models of {lean}`Float` and {lean}`Float32` consist of unsigned integers with validity predicates.
Each defined operation first interprets the integer into a {lean}`Float.Model.UnpackedFloat`, which is a higher-level model that is not specific to a bit width.
Then, the defined operation is implemented in terms of {name Float.Model.UnpackedFloat}`UnpackedFloat`, and the result is re-packed.
These definitions constitute a _logical specification_ designed for reasoning.
Although they can be executed, they will run significantly slower than native code.
Not all operations are defined; some are instead opaque functions whose behavior cannot be reasoned about in Lean's logic.

This model is not intended to serve as the basis for a more extensive floating-point library.
It exists only to support the reasoning tools available in Lean and is not suitable for larger-scale development.
Do not use this model as the basis of a more extensive floating-point library.
Instead, implement a suitable model, prove the equivalence of the its operations to this model, and then transfer lemmas using the equivalence.

{docstring Float.Model}

{docstring Float32.Model}

{docstring Float.Model.pack}

{docstring Float32.Model.pack}

{docstring Float.Model.unpack}

{docstring Float32.Model.unpack}

{docstring Float.Model.UnpackedFloat}

## Model Operations

The following operations are specified for floating-point values.
Other operators are represented by opaque functions and do not reduce in the kernel.

{docstring Float.Model.UnpackedFloat.add}

{docstring Float.Model.UnpackedFloat.sub}

{docstring Float.Model.UnpackedFloat.mul}

{docstring Float.Model.UnpackedFloat.div}

{docstring Float.Model.UnpackedFloat.sqrt}

{docstring Float.Model.UnpackedFloat.neg}

{docstring Float.Model.UnpackedFloat.abs}

{docstring Float.Model.UnpackedFloat.isNaN}

{docstring Float.Model.UnpackedFloat.isInf}

{docstring Float.Model.UnpackedFloat.isFinite}

{docstring Float.Model.UnpackedFloat.compare}

{docstring Float.Model.UnpackedFloat.beq}

{docstring Float.Model.UnpackedFloat.lt}

{docstring Float.Model.UnpackedFloat.le}

{docstring Float.Model.UnpackedFloat.ofNat}

{docstring Float.Model.UnpackedFloat.ofInt}

{docstring Float.Model.UnpackedFloat.ofScientific}

{docstring Float.Model.UnpackedFloat.toInt8}

{docstring Float.Model.UnpackedFloat.ofInt8}

{docstring Float.Model.UnpackedFloat.toInt16}

{docstring Float.Model.UnpackedFloat.ofInt16}

{docstring Float.Model.UnpackedFloat.toInt32}

{docstring Float.Model.UnpackedFloat.ofInt32}

{docstring Float.Model.UnpackedFloat.toInt64}

{docstring Float.Model.UnpackedFloat.ofInt64}

{docstring Float.Model.UnpackedFloat.toISize}

{docstring Float.Model.UnpackedFloat.ofISize}

{docstring Float.Model.UnpackedFloat.toUInt8}

{docstring Float.Model.UnpackedFloat.ofUInt8}

{docstring Float.Model.UnpackedFloat.toUInt16}

{docstring Float.Model.UnpackedFloat.ofUInt16}

{docstring Float.Model.UnpackedFloat.toUInt32}

{docstring Float.Model.UnpackedFloat.ofUInt32}

{docstring Float.Model.UnpackedFloat.toUInt64}

{docstring Float.Model.UnpackedFloat.ofUInt64}

{docstring Float.Model.UnpackedFloat.toUSize}

{docstring Float.Model.UnpackedFloat.ofUSize}

:::example "Kernel Reasoning"
The Lean kernel can compare expressions of type {lean}`Float` for syntactic equality, so {lean  (type := "Float")}`0.0` is definitionally equal to itself.
```lean
example : (0.0 : Float) = (0.0 : Float) := by rfl
```

Additionally, terms that require reduction to become syntactically equal can be checked by the kernel when they use only operations that are modeled in Lean's logic:
```lean
example : (0.0 : Float) = (0.0 + 0.0 : Float) := by rfl
```
The kernel cannot reduce terms that use operations that are not directly modeled, such as trigonometric functions:
```lean (name := sin0) +error
example : (0.0 : Float).sin = (0.0 : Float) := by rfl
```
```leanOutput sin0
Tactic `rfl` failed: The left-hand side
  Float.sin 0.0
is not definitionally equal to the right-hand side
  0.0

⊢ Float.sin 0.0 = 0.0
```


However, the {tactic}`native_decide` tactic can invoke the underlying platform's floating-point primitives that are used by Lean for run-time programs:
```lean
theorem Float.sin_zero_eq_zero :
    ((0.0 : Float).sin == (0.0 : Float)) = true := by
  native_decide
```
This tactic executes a decision procedure as compiled native code.
This requires trusting the Lean compiler, interpreter and the low-level implementations of built-in operators in addition to the kernel.
To make this dependency precisely clear, the tactic creates the axiom {name}`Float.sin_zero_eq_zero._native.native_decide.ax_1`:
```lean (name := ofRed)
#print axioms Float.sin_zero_eq_zero
```
```leanOutput ofRed
'Float.sin_zero_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Float.sin_zero_eq_zero._native.native_decide.ax_1]
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

```lean -show
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
