/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option maxRecDepth 768

#doc (Manual) "Bitvectors" =>
%%%
tag := "BitVec"
%%%

Bitvectors are fixed-width sequences of binary digits.
They are frequently used in software verification, because they closely model efficient data structures and operations that are similar to hardware.
A bitvector can be understood from two perspectives: as a sequence of bits, or as a number encoded by a sequence of bits.
When a bitvector represents a number, it can do so as either a signed or an unsigned number.
Signed numbers are represented in two's complement form.

# Logical Model

Bitvectors are represented as a wrapper around a {name}`Fin` with a suitable bound.
Because {name}`Fin` itself is a wrapper around a {name}`Nat`, bitvectors are able to use the kernel's special support for efficient computation with natural numbers.

{docstring BitVec}

# Runtime Representation

Bitvectors are represented as a {lean}`Fin` with the corresponding range.
Because {name}`BitVec` is a {ref "inductive-types-trivial-wrappers"}[trivial wrapper] around {name}`Fin` and {name}`Fin` is a trivial wrapper around {name}`Nat`, bitvectors use the same runtime representation as {name}`Nat` in compiled code.

# Syntax
:::leanSection
```lean (show := false)
variable {w n : Nat}
```
There is an {inst}`OfNat (BitVec w) n` instance for all widths {lean}`w` and natural numbers {lean}`n`.
Natural number literals, including those that use hexadecimal or binary notation, may be used to represent bitvectors in contexts where the expected type is known.
When the expected type is not known, a dedicated syntax allows the width of the bitvector to be specified along with its value.
:::

:::example "Numeric Literals for Bitvectors"
The following literals are all equivalent:
```lean
example : BitVec 8 := 0xff
example : BitVec 8 := 255
example : BitVec 8 := 0b1111_1111
```
```lean (show := false)
-- Inline test
example : (0xff : BitVec 8) = 255 := by rfl
example : (0b1111_1111 : BitVec 8) = 255 := by rfl
```
:::

:::syntax term (title := "Fixed-Width Bitvector Literals")
```grammar
$_:num#$_
```
This notation pairs a numeric literal with a term that denotes its width.
Spaces are forbidden around the `#`.
Literals that overflow the width of the bitvector are truncated.
:::

:::::example "Fixed-Width Bitvector Literals"

Bitvectors may be represented by natural number literals, so {lean}`(5 : BitVec 8)` is a valid bitvector.
Additionally, a width may be specified directly in the literal:

```leanTerm
5#8
```


Spaces are not allowed on either side of the `#`:

```syntaxError spc1 (category := term)
5 #8
```
```leanOutput spc1
<example>:1:2-1:3: expected end of input
```

```syntaxError spc2 (category := term)
5# 8
```
```leanOutput spc2
<example>:1:3-1:4: expected no space before
```


A numeric literal is required to the left of the `#`:

```syntaxError spc3 (category := term)
(3 + 2)#8
```
```leanOutput spc3
<example>:1:7-1:8: expected end of input
```


However, a term is allowed to the right of the `#`:
```leanTerm
5#(4 + 4)
```

If the literal is too large to fit in the specified number of bits, then it is truncated:
```lean (name := overflow)
#eval 7#2
```
```leanOutput overflow
3#2
```
:::::

:::syntax term (title := "Bounded Bitvector Literals") (namespace := BitVec)

```grammar
$_:num#'$_
```

This notation is available only when the `BitVec` namespace has been opened.
Rather than an explicit width, it expects a proof that the literal value is representable by a bitvector of the corresponding width.
:::

::::::leanSection
:::::example "Bounded Bitvector Literals"
The bounded bitvector literal notation ensures that literals do not overflow the specified number of bits.
The notation is only available when the `BitVec` namespace has been opened.

```lean
open BitVec
```

Literals that are in bounds require a proof to that effect:
```lean
example : BitVec 8 := 1#'(by decide)
```

Literals that are not in bounds are not allowed:
```lean (error := true) (name := oob)
example : BitVec 8 := 256#'(by decide)
```
```leanOutput oob
tactic 'decide' proved that the proposition
  256 < 2 ^ 8
is false
```

:::::
::::::

# Automation
%%%
tag := "BitVec-automation"
%%%

In addition to the full suite of automation and tools provided by Lean for every type, the {tactic}`bv_decide` tactic can solve many bitvector-related problems.
This tactic invokes an external automated theorem prover (`cadical`) and reconstructs the proof that it provides in Lean's own logic.
The resulting proofs rely only on the axiom {name}`Lean.ofReduceBool`; the external prover is not part of the trusted code base.

:::example "Popcount"

The function {lean}`popcount` returns the number of set bits in a bitvector.
It can be implemented as a 32-iteration loop that tests each bit, incrementing a counter if the bit is set:

```lean
def popcount_spec (x : BitVec 32) : BitVec 32 :=
  (32 : Nat).fold (init := 0) fun i _ pop =>
    pop + ((x >>> i) &&& 1)
```

An alternative implementation of {lean}`popcount` is described in _Hacker's Delight, Second Edition_, by Henry S. Warren,
Jr. in Figure 5-2 on p. 82.
It uses low-level bitwise operations to compute the same value with far fewer operations:
```lean
def popcount (x : BitVec 32) : BitVec 32 :=
  let x := x - ((x >>> 1) &&& 0x55555555)
  let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333)
  let x := (x + (x >>> 4)) &&& 0x0F0F0F0F
  let x := x + (x >>> 8)
  let x := x + (x >>> 16)
  let x := x &&& 0x0000003F
  x
```

These two implementations can be proven equivalent using {tactic}`bv_decide`:
```lean
theorem popcount_correct : popcount = popcount_spec := by
  funext x
  simp [popcount, popcount_spec]
  bv_decide
```
:::

# API Reference
%%%
tag := "BitVec-api"
%%%


## Bounds

{docstring BitVec.intMax}

{docstring BitVec.intMin}

## Construction

{docstring BitVec.fill}

{docstring BitVec.zero}

{docstring BitVec.allOnes}

{docstring BitVec.twoPow}

## Conversion


{docstring BitVec.toHex}

{docstring BitVec.toInt}

{docstring BitVec.toNat}

{docstring BitVec.ofBool}

{docstring BitVec.ofBoolListBE}

{docstring BitVec.ofBoolListLE}

{docstring BitVec.ofInt}

{docstring BitVec.ofNat}

{docstring BitVec.ofNatLT}

{docstring BitVec.cast}

## Comparisons

{docstring BitVec.ule}

{docstring BitVec.sle}

{docstring BitVec.ult}

{docstring BitVec.slt}

{docstring BitVec.decEq}

## Hashing

{docstring BitVec.hash}

## Sequence Operations

These operations treat bitvectors as sequences of bits, rather than as encodings of numbers.

{docstring BitVec.nil}

{docstring BitVec.cons}

{docstring BitVec.concat}

{docstring BitVec.shiftConcat}

{docstring BitVec.truncate}

{docstring BitVec.setWidth}

{docstring BitVec.setWidth'}

{docstring BitVec.append}

{docstring BitVec.replicate}

{docstring BitVec.reverse}

{docstring BitVec.rotateLeft}

{docstring BitVec.rotateRight}

### Bit Extraction

{docstring BitVec.msb}

{docstring BitVec.getMsbD}

{docstring BitVec.getMsb'}

{docstring BitVec.getMsb?}

{docstring BitVec.getLsbD}

{docstring BitVec.getLsb'}

{docstring BitVec.getLsb?}

{docstring BitVec.extractLsb}

{docstring BitVec.extractLsb'}

## Bitwise Operators

These operators modify the individual bits of one or more bitvectors.

{docstring BitVec.and}

{docstring BitVec.or}

{docstring BitVec.not}

{docstring BitVec.xor}

{docstring BitVec.zeroExtend}

{docstring BitVec.signExtend}

{docstring BitVec.ushiftRight}

{docstring BitVec.sshiftRight}

{docstring BitVec.sshiftRight'}

{docstring BitVec.shiftLeft}

{docstring BitVec.shiftLeftZeroExtend}


## Arithmetic

These operators treat bitvectors as numbers.
Some operations are signed, while others are unsigned.
Because bitvectors are understood as two's complement numbers, addition, subtraction and multiplication coincide for the signed and unsigned interpretations.


{docstring BitVec.add}

{docstring BitVec.sub}

{docstring BitVec.mul}


### Unsigned Operations

{docstring BitVec.udiv}

{docstring BitVec.smtUDiv}

{docstring BitVec.umod}

{docstring BitVec.uaddOverflow}

### Signed Operations

{docstring BitVec.abs}

{docstring BitVec.neg}

{docstring BitVec.sdiv}

{docstring BitVec.smtSDiv}

{docstring BitVec.smod}

{docstring BitVec.srem}

{docstring BitVec.saddOverflow}

## Iteration

{docstring BitVec.iunfoldr}

## Proof Automation

### Bit Blasting

The standard library contains a number of helper implementations that are useful to implement bit blasting, which is the technique used by {tactic}`bv_decide` to encode propositions as Boolean satisfiability problems for external solvers.

{docstring BitVec.adc}

{docstring BitVec.adcb}

{docstring BitVec.carry}

{docstring BitVec.mulRec}

{docstring BitVec.divRec}

{docstring BitVec.divSubtractShift}

{docstring BitVec.shiftLeftRec}

{docstring BitVec.sshiftRightRec}

{docstring BitVec.ushiftRightRec}
