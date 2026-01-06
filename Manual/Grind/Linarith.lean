/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

-- Due to Lean.Grind.Semiring.nsmul_eq_natCast_mul
set_option verso.docstring.allowMissing true

open Lean.Grind

#doc (Manual) "Linear Arithmetic Solver" =>
%%%
tag := "grind-linarith"
%%%

The {tactic}`grind` tactic includes a linear arithmetic solver for arbitrary types, called {name}`linarith`, that is used for types not supported by {ref "cutsat"}`cutsat`.
Like the {ref "grind-ring"}`ring` solver, it can be used with any type that has instances of certain type classes.
It self-configures depending on the availability of these type classes, so it is not necessary to provide all of them to use the solver; however, its capabilities are increased by the availability of more instances.
This solver is useful for reasoning about the real numbers, ordered vector spaces, and other types that can't be embedded into {name}`Int`.


The core functionality of {name}`linarith` is a model-based solver for linear inequalities with integer coefficients.
It can be disabled using the option `grind -linarith`.


:::example "Goals Decided by `linarith`" (open := true)
```imports -show
import Std
```
```lean -show
open Lean.Grind
```
All of these examples rely on instances of the following ordering notation and `linarith` classes:
```lean
variable [LE α] [LT α] [Std.LawfulOrderLT α]  [Std.IsLinearOrder α]
variable [IntModule α] [OrderedAdd α]
```

Integer modules ({name}`IntModule`) are types with zero, addition, negation, subtraction, and scalar multiplication by integers that satisfy the expected properties of these operations.
Linear orders ({name}`Std.IsLinearOrder`) are orders in which any pair of elements is ordered, and {name}`OrderedAdd` states that adding a constant to both sides preserves orderings.

```lean
example {a b : α} : 2 • a + b ≥ b + a + a := by grind

example {a b : α} (h : a ≤ b) : 3 • a + b ≤ 4 • b := by grind

example {a b c : α} :
    a = b + c →
    2 • b ≤ c →
    2 • a ≤ 3 • c := by
  grind

example {a b c d e : α} :
    2 • a + b ≥ 0 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0 →
    a ≥ 3 • c → c ≥ 6 • e → d - 5 • e ≥ 0 →
    a + b + 3 • c + d + 2 • e < 0 →
    False := by
  grind
```
:::

:::example "Commutative Ring Goals Decided by `linarith`" (open := true)
```imports -show
import Std
```
```lean -show
open Lean.Grind
```
For types that are commmutative rings (that is, types in which the multiplication operator is commutative) with {name}`CommRing` instances, `linarith` has more capabilities.

```lean
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
variable [CommRing R] [OrderedRing R]
```

The {inst}`CommRing R` instance allows `linarith` to perform basic normalization, such as identifying linear atoms `a * b` and `b * a`, and to account for scalar multiplication on both sides.
The {inst}`OrderedRing R` instance allows the solver to support constants, because it has access to the fact that {lean}`(0 : R) < 1`.

```lean
example (a b : R) (h : a * b ≤ 1) : b * 3 • a + 1 ≤ 4 := by grind

example (a b c d e f : R) :
    2 • a + b ≥ 1 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e • f ≥ 0 →
    a ≥ 3 • c →
    c ≥ 6 • e • f → d - f * e * 5 ≥ 0 →
    a + b + 3 • c + d + 2 • e • f < 0 →
    False := by
  grind
```
:::

:::TODO
Planned future features
* Support for {name}`NatModule` (by embedding in the Grothendieck envelope, as we already do for semirings),
* Better communication between the {name}`ring` and {name}`linarith` solvers.
  There is currently very little communication between these two solvers.
* Non-linear arithmetic over ordered rings.
:::

# Supporting `linarith`
%%%
tag := "grind-linarith-classes"
%%%

To add support for a new type to `linarith`, the first step is to implement {name}`IntModule` if possible, or {name}`NatModule` otherwise.
Every {name}`Ring` is already an {name}`IntModule`, and every {name}`Semiring` is already a {name}`NatModule`, so implementing one of those instances is also sufficient.
Next, one of the order classes ({name}`Std.IsPreorder`, {name}`Std.IsPartialOrder`, or {name}`Std.IsLinearOrder`) should be implemented.
Typically an {name Std.IsPreorder}`IsPreorder` instance is enough when the context already includes a contradiction, but an {name Std.IsLinearOrder}`IsLinearOrder` instance is required in order to prove linear inequality goals.
Additional features are enabled by implementing {name}`OrderedAdd`, which expresses that the additive structure in a module is compatible with the order, and {name}`OrderedRing`, which improves support for constants.


{docstring Lean.Grind.NatModule}

{docstring Lean.Grind.IntModule}

{docstring Lean.Grind.OrderedAdd}

{docstring Lean.Grind.OrderedRing}
