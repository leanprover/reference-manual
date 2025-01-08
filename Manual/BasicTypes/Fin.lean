/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

#doc (Manual) "Finite Natural Numbers" =>
%%%
tag := "Fin"
%%%

```lean (show := false)
section
variable (n : Nat)
```

For any {tech}[natural number] {lean}`n`, the {lean}`Fin n` is a type that contains all the natural numbers that are strictly less than {lean}`n`.
In other words, {lean}`Fin n` has exactly {lean}`n` elements.
It can be used to represent the valid indices into a list or array, or it can serve as a canonical {lean}`n`-element type.

{docstring Fin}

{lean}`Fin` is closely related to {name}`UInt8`, {name}`UInt16`, {name}`UInt32`, {name}`UInt64`, and {name}`USize`, which also represent finite non-negative integral types.
However, these types are backed by bitvectors rather than by natural numbers, and they have fixed bounds.
{lean}`Fin` is comparatively more flexible, but also less convenient for low-level reasoning.
In particular, using bitvectors rather than proofs that a number is less than some power of two avoids needing to take care to avoid evaluating the concrete bound.

# Run-Time Characteristics

Because {lean}`Fin n` is a structure in which only a single field is not a proof, it is a {ref "inductive-types-trivial-wrappers"}[trivial wrapper].
This means that it is represented identically to the underlying natural number in compiled code.

# Coercions and Literals

There is a {tech}[coercion] from {lean}`Fin n` to {lean}`Nat` that discards the proof that the number is less than the bound.
In particular, this coercion is precisely the projection {name}`Fin.val`.
One consequence of this is that uses of {name}`Fin.val` are displayed as coercions rather than explicit projections in proof states.
:::example "Coercing from {name}`Fin` to {name}`Nat`"
A {lean}`Fin n` can be used where a {lean}`Nat` is expected:
```lean (name := oneFinCoe)
#eval let one : Fin 3 := ⟨1, by omega⟩; (one : Nat)
```
```leanOutput oneFinCoe
1
```

Uses of {name}`Fin.val` show up as coercions in proof states:
```proofState
∀(n : Nat) (i : Fin n), i < n := by
  intro n i
/--
n : Nat
i : Fin n
⊢ ↑i < n
-/

```
:::

Natural number literals may be used for {lean}`Fin` types, implemented as usual via an {name}`OfNat` instance.
The {name}`OfNat` instance for {lean}`Fin n` requires that the upper bound {lean}`n` is not zero, but does not check that the literal is less than {lean}`n`.
If the literal is larger than the type can represent, the remainder when dividing it by {lean}`n` is used.

:::example "Numeric Literals for {name}`Fin`"

If {lean}`n > 0`, then natural number literals can be used for {lean}`Fin n`:
```lean
example : Fin 5 := 3
example : Fin 20 := 19
```
When the literal is greater than or equal to {lean}`n`, the remainder when dividing by {lean}`n` is used:
```lean (name := fivethree)
#eval (5 : Fin 3)
```
```leanOutput fivethree
2
```
```lean (name := fourthree)
#eval ([0, 1, 2, 3, 4, 5, 6] : List (Fin 3))
```
```leanOutput fourthree
[0, 1, 2, 0, 1, 2, 0]
```

If Lean can't synthesize an instance of {lean}`NeZero n`, then there is no {lean}`OfNat (Fin n)` instance:
```lean (error := true) (name := fin0)
example : Fin 0 := 0
```
```leanOutput fin0
failed to synthesize
  OfNat (Fin 0) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin 0
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

```lean (error := true) (name := finK)
example (k : Nat) : Fin k := 0
```
```leanOutput finK
failed to synthesize
  OfNat (Fin k) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin k
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::

# API Reference

## Construction

{docstring Fin.last}

{docstring Fin.succ}

{docstring Fin.pred}

## Arithmetic

Typically, arithmetic operations on {name}`Fin` should be accessed using Lean's overloaded arithmetic notation, particularly via the instances {inst}`Add (Fin n)`, {inst}`Sub (Fin n)`, {inst}`Mul (Fin n)`, {inst}`Div (Fin n)`,  and {inst}`Mod (Fin n)`.
Heterogeneous operators such as {lean}`Fin.natAdd` do not have corresponding heterogeneous instances (e.g. {name}`HAdd`) to avoid confusing type inference behavior.

{docstring Fin.add}

{docstring Fin.natAdd}

{docstring Fin.addNat}

{docstring Fin.mul}

{docstring Fin.sub}

{docstring Fin.subNat}

{docstring Fin.div}

{docstring Fin.mod}

{docstring Fin.modn}

{docstring Fin.log2}

## Bitwise and Logical Operations

Typically, bitwise and logical operations on {name}`Fin` should be accessed using Lean's overloaded arithmetic notation, particularly via the instances {inst}`ShiftLeft (Fin n)`, {inst}`ShiftRight (Fin n)`, {inst}`AndOp (Fin n)`, {inst}`OrOp (Fin n)`, {inst}`Xor (Fin n)`

{docstring Fin.shiftLeft}

{docstring Fin.shiftRight}

{docstring Fin.land}

{docstring Fin.lor}

{docstring Fin.xor}


## Conversions

{docstring Fin.ofNat'}

{docstring Fin.cast}

{docstring Fin.castAdd}

{docstring Fin.castLE}

{docstring Fin.castSucc}

{docstring Fin.castLT}

{docstring Fin.rev}

{docstring Fin.elim0}

## Iteration

{docstring Fin.foldr}

{docstring Fin.foldrM}

{docstring Fin.foldl}

{docstring Fin.foldlM}

{docstring Fin.hIterate}

{docstring Fin.hIterateFrom}

## Reasoning

{docstring Fin.induction}

{docstring Fin.inductionOn}

{docstring Fin.reverseInduction}

{docstring Fin.cases}

{docstring Fin.lastCases}

{docstring Fin.addCases}

{docstring Fin.succRec}

{docstring Fin.succRecOn}

## Proof Automation

{docstring Fin.isValue}

{docstring Fin.fromExpr?}

{docstring Fin.reduceOfNat'}

{docstring Fin.reduceSucc}

{docstring Fin.reduceAdd}

{docstring Fin.reduceNatOp}

{docstring Fin.reduceNatAdd}

{docstring Fin.reduceAddNat}

{docstring Fin.reduceSub}

{docstring Fin.reduceSubNat}

{docstring Fin.reduceMul}

{docstring Fin.reduceDiv}

{docstring Fin.reduceMod}

{docstring Fin.reduceBin}

{docstring Fin.reducePred}

{docstring Fin.reduceBinPred}

{docstring Fin.reduceBoolPred}

{docstring Fin.reduceBNe}

{docstring Fin.reduceEq}

{docstring Fin.reduceLT}

{docstring Fin.reduceGE}

{docstring Fin.reduceGT}

{docstring Fin.reduceLE}

{docstring Fin.reduceNe}

{docstring Fin.reduceBEq}

{docstring Fin.reduceRev}

{docstring Fin.reduceFinMk}

{docstring Fin.reduceXor}

{docstring Fin.reduceOp}

{docstring Fin.reduceAnd}

{docstring Fin.reduceOr}

{docstring Fin.reduceLast}

{docstring Fin.reduceShiftLeft}

{docstring Fin.reduceShiftRight}

{docstring Fin.reduceCastSucc}

{docstring Fin.reduceCastAdd}

{docstring Fin.reduceCastLT}

{docstring Fin.reduceCastLE}
