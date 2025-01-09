/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.BasicTypes.UInt.Comparisons
import Manual.BasicTypes.UInt.Arith

open Manual.FFIDocType

open Verso.Genre Manual

#doc (Manual) "Fixed-Precision Integer Types" =>
%%%
tag := "fixed-ints"
%%%

Lean's standard library includes the usual assortment of fixed-width integer types.
From the perspective of formalization and proofs, these types are wrappers around bitvectors of the appropriate size; the wrappers ensure that the correct implementations of e.g. arithmetic operations are applied.
In compiled code, they are represented efficiently: the compiler has special support for them, as it does for other fundamental types.

# Logical Model

Fixed-width integers may be unsigned or signed.
Furthermore, they are available in five sizes: 8, 16, 32, and 64 bits, along with the current architecture's word size.
In their logical models, the unsigned integers are structures that wrap a {name}`BitVec` of the appropriate width.
Signed integers wrap the corresponding unsigned integers, and use a twos-complement representation.

## Unsigned

{docstring USize}

{docstring UInt8}

{docstring UInt16}

{docstring UInt32}

{docstring UInt64}

## Signed

{docstring ISize}

{docstring Int8}

{docstring Int16}

{docstring Int32}

{docstring Int64}

# Run-Time Representation

In compiled code, fixed-width integer types that fit in one less bit than the platform's pointer size are represented unboxed, without additional allocations or indirections.
This always includes {lean}`Int8`, {lean}`UInt8`, {lean}`Int16`, and {lean}`UInt16`.
On 64-bit architectures, {lean}`Int32` and {lean}`UInt32` are also unboxed.

Fixed-width integer types that take at least as many bits as the platform's pointer type are represented the same way as {name}`Nat`: if they are sufficiently small, then they are represented unboxed; if they are larger, then they are represented by a heap-allocated number value.
{lean}`Int64`, {lean}`UInt64`, {lean}`ISize`, and {lean}`USize` are always represented this way, as are {lean}`Int32` and {lean}`UInt32` on 32-bit architectures.

# Syntax

All the fixed-width integer types have {name}`OfNat` instances, which allow numerals to be used as literals, both in expression and in pattern contexts.
The signed types additionally have {lean}`Neg` instances, allowing negation to be applied.

:::example "Fixed-Width Literals"
Lean allows both decimal and hexadecimal literals to be used for types with {name}`OfNat` instances.
In this example, literal notation is used to define masks.

```lean
structure Permissions where
  readable : Bool
  writable : Bool
  executable : Bool

def Permissions.encode (p : Permissions) : UInt8 :=
  let r := if p.readable then 0x01 else 0
  let w := if p.writable then 0x02 else 0
  let x := if p.executable then 0x04 else 0
  r ||| w ||| x

def Permissions.decode (i : UInt8) : Permissions :=
  ⟨i &&& 0x01 ≠ 0, i &&& 0x02 ≠ 0, i &&& 0x04 ≠ 0⟩
```

```lean (show := false)
-- Check the above
theorem Permissions.decode_encode (p : Permissions) : p = .decode (p.encode) := by
  let ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;>
  simp +decide [encode, decode]
```
:::

Literals that overflow their types' precision are interpreted modulus the precision.
Signed types, are interpreted according to the underlying twos-complement representation.

:::example "Overflowing Fixed-Width Literals"
The following statements are all true:
```lean
example : (255 : UInt8) = 255 := by rfl
example : (256 : UInt8) = 0   := by rfl
example : (257 : UInt8) = 1   := by rfl

example : (0x7f : Int8) = 127  := by rfl
example : (0x8f : Int8) = -113 := by rfl
example : (0xff : Int8) = -1   := by rfl
```
:::

# API Reference

## Sizes

Each fixed-width integer has a _size_, which is the number of distinct values that can be represented by the type.
This is not equivalent to C's `sizeof` operator, which instead determines how many bytes the type occupies.

{docstring USize.size}

{docstring ISize.size}

{docstring UInt8.size}

{docstring Int8.size}

{docstring UInt16.size}

{docstring Int16.size}

{docstring UInt32.size}

{docstring Int32.size}

{docstring UInt64.size}

{docstring Int64.size}

## Conversions

### To and From `Int`

{docstring ISize.toInt}

{docstring Int8.toInt}

{docstring Int16.toInt}

{docstring Int32.toInt}

{docstring Int64.toInt}

{docstring ISize.ofInt}

{docstring Int8.ofInt}

{docstring Int16.ofInt}

{docstring Int32.ofInt}

{docstring Int64.ofInt}

### To and From `Nat`

{docstring USize.ofNat}

{docstring ISize.ofNat}

{docstring UInt8.ofNat}

{docstring Int8.ofNat}

{docstring UInt16.ofNat}

{docstring Int16.ofNat}

{docstring UInt32.ofNat}

{docstring UInt32.ofNat'}

{docstring UInt32.ofNatTruncate}

{docstring Int32.ofNat}

{docstring UInt64.ofNat}

{docstring Int64.ofNat}

{docstring USize.ofNat32}

{docstring USize.ofNatCore}

{docstring UInt8.ofNatCore}

{docstring UInt16.ofNatCore}

{docstring UInt32.ofNatCore}

{docstring UInt64.ofNatCore}

{docstring USize.toNat}

{docstring ISize.toNat}

{docstring UInt8.toNat}

{docstring Int8.toNat}

{docstring UInt16.toNat}

{docstring Int16.toNat}

{docstring UInt32.toNat}

{docstring Int32.toNat}

{docstring UInt64.toNat}

{docstring Int64.toNat}

### To Other Fixed-Width Integers

{docstring Int32.toISize}

{docstring Int64.toISize}

{docstring ISize.toInt32}

{docstring Int8.toInt32}

{docstring Int16.toInt32}

{docstring ISize.toInt64}

{docstring USize.toUInt8}

{docstring UInt16.toUInt8}

{docstring Int16.toInt8}

{docstring UInt32.toUInt8}

{docstring Int32.toInt8}

{docstring UInt64.toUInt8}

{docstring Int64.toInt8}

{docstring USize.toUInt16}

{docstring UInt8.toUInt16}

{docstring Int8.toInt16}

{docstring UInt32.toUInt16}

{docstring Int32.toInt16}

{docstring UInt64.toUInt16}

{docstring Int64.toInt16}

{docstring USize.toUInt32}

{docstring UInt8.toUInt32}

{docstring Int8.toInt32}

{docstring UInt16.toUInt32}

{docstring Int16.toInt32}

{docstring UInt64.toUInt32}

{docstring Int64.toInt32}

{docstring USize.toUInt64}

{docstring UInt8.toUInt64}

{docstring Int8.toInt64}

{docstring UInt16.toUInt64}

{docstring Int16.toInt64}

{docstring UInt32.toUInt64}

{docstring Int32.toInt64}

{docstring UInt8.toUSize}

{docstring UInt16.toUSize}

{docstring UInt32.toUSize}

{docstring UInt64.toUSize}

### To Floating-Point Numbers

{docstring UInt64.toFloat}

{docstring UInt64.toFloat32}

### To Bitvectors

{docstring ISize.toBitVec}

{docstring Int8.toBitVec}

{docstring Int16.toBitVec}

{docstring Int32.toBitVec}

{docstring Int64.toBitVec}

### To Finite Numbers

{docstring USize.val}

{docstring UInt8.val}

{docstring UInt16.val}

{docstring UInt32.val}

{docstring UInt64.val}

{docstring USize.repr}

### To Characters

The {name}`Char` type is a wrapper around {name}`UInt32` that requires a proof that the wrapped integer represents a Unicode code point.
This predicate is part of the {name}`UInt32` API.

{docstring UInt32.isValidChar}

{include 2 Manual.BasicTypes.UInt.Comparisons}

{include 2 Manual.BasicTypes.UInt.Arith}

## Bitwise Operations

Typically, bitwise operations on fixed-width integers should be accessed using Lean's overloaded operators, particularly their instances of {name}`ShiftLeft`, {name}`ShiftRight`, {name}`AndOp`, {name}`OrOp`, and {name}`Xor`.

```lean (show := false)
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  let classes := [`ShiftLeft, `ShiftRight, `AndOp, `OrOp, `Xor]
  for t in types do
    for c in classes do
      elabCommand <| ← `(example : $(mkIdent c):ident $(mkIdent t) := inferInstance)
```

{docstring USize.land}

{docstring ISize.land}

{docstring UInt8.land}

{docstring Int8.land}

{docstring UInt16.land}

{docstring Int16.land}

{docstring UInt32.land}

{docstring Int32.land}

{docstring UInt64.land}

{docstring Int64.land}

{docstring USize.lor}

{docstring ISize.lor}

{docstring UInt8.lor}

{docstring Int8.lor}

{docstring UInt16.lor}

{docstring Int16.lor}

{docstring UInt32.lor}

{docstring Int32.lor}

{docstring UInt64.lor}

{docstring Int64.lor}

{docstring USize.xor}

{docstring ISize.xor}

{docstring UInt8.xor}

{docstring Int8.xor}

{docstring UInt16.xor}

{docstring Int16.xor}

{docstring UInt32.xor}

{docstring Int32.xor}

{docstring UInt64.xor}

{docstring Int64.xor}

{docstring USize.complement}

{docstring ISize.complement}

{docstring UInt8.complement}

{docstring Int8.complement}

{docstring UInt16.complement}

{docstring Int16.complement}

{docstring UInt32.complement}

{docstring Int32.complement}

{docstring UInt64.complement}

{docstring Int64.complement}

{docstring USize.shiftLeft}

{docstring ISize.shiftLeft}

{docstring UInt8.shiftLeft}

{docstring Int8.shiftLeft}

{docstring UInt16.shiftLeft}

{docstring Int16.shiftLeft}

{docstring UInt32.shiftLeft}

{docstring Int32.shiftLeft}

{docstring UInt64.shiftLeft}

{docstring Int64.shiftLeft}

{docstring USize.shiftRight}

{docstring ISize.shiftRight}

{docstring UInt8.shiftRight}

{docstring Int8.shiftRight}

{docstring UInt16.shiftRight}

{docstring Int16.shiftRight}

{docstring UInt32.shiftRight}

{docstring Int32.shiftRight}

{docstring UInt64.shiftRight}

{docstring Int64.shiftRight}

## Proof Automation

The functions in this section are primarily parts of the implementation of simplification rules employed by {tactic}`simp`.
They are probably only of interest to users who are implementing custom proof automation that involves fixed-precision integers.

{docstring USize.fromExpr}

{docstring UInt8.fromExpr}

{docstring UInt16.fromExpr}

{docstring UInt32.fromExpr}

{docstring UInt64.fromExpr}

{docstring UInt8.reduceAdd}

{docstring UInt16.reduceAdd}

{docstring UInt32.reduceAdd}

{docstring UInt64.reduceAdd}

{docstring UInt8.reduceDiv}

{docstring UInt16.reduceDiv}

{docstring UInt32.reduceDiv}

{docstring UInt64.reduceDiv}

{docstring UInt8.reduceGE}

{docstring UInt16.reduceGE}

{docstring UInt32.reduceGE}

{docstring UInt64.reduceGE}

{docstring UInt8.reduceGT}

{docstring UInt16.reduceGT}

{docstring UInt32.reduceGT}

{docstring UInt64.reduceGT}

{docstring UInt8.reduceLE}

{docstring UInt16.reduceLE}

{docstring UInt32.reduceLE}

{docstring UInt64.reduceLE}

{docstring UInt8.reduceLT}

{docstring UInt16.reduceLT}

{docstring UInt32.reduceLT}

{docstring UInt64.reduceLT}

{docstring UInt8.reduceMod}

{docstring UInt16.reduceMod}

{docstring UInt32.reduceMod}

{docstring UInt64.reduceMod}

{docstring UInt8.reduceMul}

{docstring UInt16.reduceMul}

{docstring UInt32.reduceMul}

{docstring UInt64.reduceMul}

{docstring UInt8.reduceOfNat}

{docstring UInt16.reduceOfNat}

{docstring UInt32.reduceOfNat}

{docstring UInt64.reduceOfNat}

{docstring UInt8.reduceOfNatCore}

{docstring UInt16.reduceOfNatCore}

{docstring UInt32.reduceOfNatCore}

{docstring UInt64.reduceOfNatCore}

{docstring UInt8.reduceSub}

{docstring UInt16.reduceSub}

{docstring UInt32.reduceSub}

{docstring UInt64.reduceSub}

{docstring USize.reduceToNat}

{docstring UInt8.reduceToNat}

{docstring UInt16.reduceToNat}

{docstring UInt32.reduceToNat}

{docstring UInt64.reduceToNat}
