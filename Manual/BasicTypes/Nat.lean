/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

#doc (Manual) "Natural Numbers" =>
%%%
tag := "Nat"
%%%

The {deftech}[natural numbers] are nonnegative integers.
Logically, they are the numbers 0, 1, 2, 3, …, generated from the constructors {lean}`Nat.zero` and {lean}`Nat.succ`.
Lean imposes no upper bound on the representation of natural numbers other than physical constraints imposed by the available memory of the computer.

Because the natural numbers are fundamental to both mathematical reasoning and programming, they are specially supported by Lean's implementation. The logical model of the natural numbers is as an {tech}[inductive type], and arithmetic operations are specified using this model. In Lean's kernel, the interpreter, and compiled code, closed natural numbers are represented as efficient arbitrary-precision integers. Sufficiently small numbers are immediate values that don't require indirection through a pointer. Arithmetic operations are implemented by primitives that take advantage of the efficient representations.

# Logical Model
%%%
tag := "nat-model"
%%%


{docstring Nat}

The Peano axioms are a consequence of this definition.
The induction principle generated for {lean}`Nat` is the one demanded by the axiom of induction:
```signature
Nat.rec.{u} {motive : Nat → Sort u}
  (zero : motive zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) :
  motive t
```
This induction principle also implements primitive recursion.
The injectivity of {lean}`Nat.succ` and the disjointness of {lean}`Nat.succ` and `Nat.zero` are consequences of the induction principle, using a construction typically called “no confusion”:
```lean
def NoConfusion : Nat → Nat → Prop
  | 0, 0 => True
  | 0, _ + 1 | _ + 1, 0 => False
  | n + 1, k + 1 => n = k

theorem noConfusionDiagonal (n : Nat) : NoConfusion n n :=
  Nat.rec True.intro (fun _ _ => rfl) n

theorem noConfusion (n k : Nat) (eq : n = k) : NoConfusion n k :=
  eq ▸ noConfusionDiagonal n

theorem succ_injective : n + 1 = k + 1 → n = k := noConfusion (n + 1) (k + 1)

theorem succ_not_zero : ¬n + 1 = 0 := noConfusion (n + 1) 0
```

# Run-Time Representation
%%%
tag := "nat-runtime"
%%%


In compiled code, sufficiently-small natural numbers are represented as unboxed values: the lowest-order bit in an object pointer is used to indicate that the value is not, in fact, a pointer, and the remaining bits are used to store the number.
31 bits are available on 32-bits architectures for unboxed {lean}`Nat`s, while 63 bits are available on 64-bit architectures.
In other words, natural numbers smaller than $`2^31 = 2,147,483,648` or $`2^63 = 9,223,372,036,854,775,808` do not require allocations.
If an natural number is too large for the unboxed representation, it is instead allocated as an ordinary Lean object that consists of an object header and an arbitrary-precision integer value.

## Performance Notes
%%%
tag := "nat-performance"
%%%


Using Lean's built-in arithmetic operators, rather than redefining them, is essential.
The logical model of {lean}`Nat` is essentially a linked list, so addition would take time linear in the size of one argument.
Still worse, multiplication takes quadratic time in this model.
While defining arithmetic from scratch can be a useful learning exercise, these redefined operations will not be nearly as fast.

# Syntax
%%%
tag := "nat-syntax"
%%%


Natural number literals are overridden using the {lean}`OfNat` type class, which is described in the {ref "nat-literals"}[section on literal syntax].


# API Reference
%%%
tag := "nat-api"
%%%


## Arithmetic
%%%
tag := "nat-api-arithmetic"
%%%

{docstring Nat.pred}

{docstring Nat.add}

{docstring Nat.sub}

{docstring Nat.mul}

{docstring Nat.div}

{docstring Nat.mod}

{docstring Nat.modCore}

{docstring Nat.pow}

{docstring Nat.log2}

### Bitwise Operations
%%%
tag := "nat-api-bitwise"
%%%

{docstring Nat.shiftLeft}

{docstring Nat.shiftRight}

{docstring Nat.xor}

{docstring Nat.lor}

{docstring Nat.land}

{docstring Nat.bitwise}

{docstring Nat.testBit}

## Minimum and Maximum
%%%
tag := "nat-api-minmax"
%%%


{docstring Nat.min}

{docstring Nat.max}

{docstring Nat.imax}

## GCD and LCM
%%%
tag := "nat-api-gcd-lcm"
%%%


{docstring Nat.gcd}

{docstring Nat.lcm}

## Powers of Two
%%%
tag := "nat-api-pow2"
%%%


{docstring Nat.isPowerOfTwo}

{docstring Nat.nextPowerOfTwo}

## Comparisons
%%%
tag := "nat-api-comparison"
%%%


### Boolean Comparisons
%%%
tag := "nat-api-comparison-bool"
%%%


{docstring Nat.beq}

{docstring Nat.ble}

{docstring Nat.blt}

### Decidable Equality
%%%
tag := "nat-api-deceq"
%%%

{docstring Nat.decEq}

{docstring Nat.decLe}

{docstring Nat.decLt}

### Predicates
%%%
tag := "nat-api-predicates"
%%%

{docstring Nat.le}

{docstring Nat.lt}

{docstring Nat.lt_wfRel}

## Iteration
%%%
tag := "nat-api-iteration"
%%%

Many iteration operators come in two versions: a structurally recursive version and a tail-recursive version.
The structurally recursive version is typically easier to use in contexts where definitional equality is important, as it will compute when only some prefix of a natural number is known.

{docstring Nat.repeat}

{docstring Nat.repeatTR}

{docstring Nat.fold}

{docstring Nat.foldTR}

{docstring Nat.foldM}

{docstring Nat.foldRev}

{docstring Nat.foldRevM}

{docstring Nat.forM}

{docstring Nat.forRevM}

{docstring Nat.all}

{docstring Nat.allTR}

{docstring Nat.any}

{docstring Nat.anyTR}

{docstring Nat.allM}

{docstring Nat.anyM}

## Conversion
%%%
tag := "nat-api-conversion"
%%%

{docstring Nat.toUInt8}

{docstring Nat.toUInt16}

{docstring Nat.toUInt32}

{docstring Nat.toUInt64}

{docstring Nat.toUSize}

{docstring Nat.toFloat}

{docstring Nat.isValidChar}

{docstring Nat.repr}

{docstring Nat.toDigits}

{docstring Nat.toDigitsCore}

{docstring Nat.digitChar}

{docstring Nat.toSubscriptString}

{docstring Nat.toSuperscriptString}

{docstring Nat.toSuperDigits}

{docstring Nat.toSubDigits}

{docstring Nat.subDigitChar}

{docstring Nat.superDigitChar}

### Metaprogramming and Internals
%%%
tag := "nat-api-meta"
%%%

{docstring Nat.fromExpr?}

{docstring Nat.toLevel}

## Casts
%%%
tag := "nat-api-cast"
%%%


{docstring NatCast}

{docstring Nat.cast}

## Elimination
%%%
tag := "nat-api-elim"
%%%


The recursion principle that is automatically generated for {lean}`Nat` results in proof goals that are phrased in terms of {lean}`Nat.zero` and {lean}`Nat.succ`.
This is not particularly user-friendly, so an alternative logically-equivalent recursion principle is provided that results in goals that are phrased in terms of {lean}`0` and `n + 1`.

:::TODO
Insert reference to section on how to do this
:::

{docstring Nat.rec}

{docstring Nat.recOn}

{docstring Nat.casesOn}

{docstring Nat.below}

{docstring Nat.noConfusionType}

{docstring Nat.noConfusion}

{docstring Nat.ibelow}

{docstring Nat.elimOffset}

### Alternative Induction Principles
%%%
tag := "nat-api-induction"
%%%


{docstring Nat.strongInductionOn}

{docstring Nat.caseStrongInductionOn}

{docstring Nat.div.inductionOn}

{docstring Nat.div2Induction}

{docstring Nat.mod.inductionOn}

# Simplification
%%%
tag := "nat-simp"
%%%


{docstring Nat.isValue}

{docstring Nat.reduceUnary}

{docstring Nat.reduceBin}

{docstring Nat.reduceBinPred}

{docstring Nat.reduceBoolPred}

{docstring Nat.reduceSucc}

{docstring Nat.reduceAdd}

{docstring Nat.reduceSub}

{docstring Nat.reduceMul}

{docstring Nat.reducePow}

{docstring Nat.reduceDiv}

{docstring Nat.reduceMod}

{docstring Nat.reduceGcd}

{docstring Nat.reduceLT}

{docstring Nat.reduceLTLE}

{docstring Nat.reduceLeDiff}

{docstring Nat.reduceSubDiff}

{docstring Nat.reduceGT}

{docstring Nat.reduceBEq}

{docstring Nat.reduceBeqDiff}

{docstring Nat.reduceBneDiff}

{docstring Nat.reduceEqDiff}

{docstring Nat.reduceBNe}

{docstring Nat.reduceNatEqExpr}

{docstring Nat.applyEqLemma}

{docstring Nat.applySimprocConst}
