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
set_option maxHeartbeats 300000

#doc (Manual) "Algebraic Solver (Commutative Rings, Fields)" =>
%%%
tag := "grind-ring"
%%%

The `ring` solver in {tactic}`grind` is inspired by Gröbner basis computation procedures and term rewriting completion.
It views multivariate polynomials as rewriting rules.
For example, the polynomial equality `x * y + x - 2 = 0` is treated as a rewriting rule `x * y ↦ -x + 2`.
It uses superposition to ensure the rewriting system is confluent.

The following examples demonstrate goals that can be decided by the `ring` solver.
In these examples, the `Lean` and `Lean.Grind` namespaces are open:
```lean
open Lean Grind
```

:::example "Commutative Rings" (open := true)
```lean -show
open Lean.Grind
```
```lean
example [CommRing α] (x : α) : (x + 1) * (x - 1) = x ^ 2 - 1 := by
  grind
```
:::
:::example "Ring Characteristics" (open := true)
The solver “knows” that `16*16 = 0` because the [ring characteristic](https://en.wikipedia.org/wiki/Characteristic_%28algebra%29) (that is, the minimum number of copies of the multiplicative identity that sum to the additive identity) is `256`, which is provided by the {name}`IsCharP` instance.

```lean -show
open Lean.Grind
```
```lean
example [CommRing α] [IsCharP α 256] (x : α) :
    (x + 16)*(x - 16) = x^2 := by
  grind
```
:::

:::example "Standard Library Types" (open := true)
```lean -show
open Lean.Grind
```
Types in the standard library are supported by the solver out of the box.
`UInt8` is a commutative ring with characteristic `256`, and thus has instances of {inst}`CommRing UInt8` and {inst}`IsCharP UInt8 256`.
```lean
example (x : UInt8) : (x + 16) * (x - 16) = x ^ 2 := by
  grind
```
:::

:::example "More Commutative Ring Proofs" (open := true)
```lean -show
open Lean.Grind
```
The axioms of a commutative ring are sufficient to prove these statements.

```lean
example [CommRing α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind
```

```lean
example [CommRing α] (x y : α) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
:::

:::example "Characteristic Zero" (open := true)
```lean -show
open Lean.Grind
```
`ring` proves that `a + 1 = 2 + a` is unsatisfiable because the characteristic is known to be 0.

```lean
example [CommRing α] [IsCharP α 0] (a : α) :
    a + 1 = 2 + a → False := by
  grind
```
:::

:::example "Inferred Characteristic" (open := true)
```lean -show
open Lean.Grind
```
Even when the characteristic is not initially known, when `grind` discovers that `n = 0` for some numeral `n`, it makes inferences about the characteristic:
```lean
example [CommRing α] (a b c : α)
    (h₁ : a + 6 = a) (h₂ : c = c + 9) (h : b + 3*c = 0) :
    27*a + b = 0 := by
  grind
```
:::

# Solver Type Classes
%%%
tag := "grind-ring-classes"
%%%

:::paragraph
Users can enable the `ring` solver for their own types by providing instances of the following {tech (key := "type class")}[type classes], all in the `Lean.Grind` namespace:

* {name Lean.Grind.Semiring}`Semiring`

* {name Lean.Grind.Ring}`Ring`

* {name Lean.Grind.CommSemiring}`CommSemiring`

* {name Lean.Grind.CommRing}`CommRing`

* {name Lean.Grind.IsCharP}`IsCharP`

* {name Lean.Grind.AddRightCancel}`AddRightCancel`

* {name Lean.Grind.NoNatZeroDivisors}`NoNatZeroDivisors`

* {name Lean.Grind.Field}`Field`


The algebraic solvers will self-configure depending on the availability of these instances, so not all need to be provided.
The capabilities of the algebraic solvers will, of course, degrade when some are not available.
:::

The Lean standard library contains the applicable instances for the types defined in the standard library.
By providing these instances, other libraries can also enable {tactic}`grind`'s `ring` solver.
For example, the Mathlib `CommRing` type class implements `Lean.Grind.CommRing` to ensure the `ring` solver works out-of-the-box.

## Algebraic Structures

To enable the algebraic solver, a type should have an instance of the most specific possible algebraic structure that the solver supports.
In order of increasing specificity, that is {name Lean.Grind.Semiring}`Semiring`, {name Lean.Grind.Ring}`Ring`, {name Lean.Grind.CommSemiring}`CommSemiring`, {name Lean.Grind.CommRing}`CommRing`, and {name Lean.Grind.Field}`Field`.

{docstring Lean.Grind.Semiring}

{docstring Lean.Grind.CommSemiring}

{docstring Lean.Grind.Ring}

{docstring Lean.Grind.CommRing}

### Fields
%%%
tag := "grind-ring-field"
%%%

:::leanSection
```lean -show
variable {a b p : α} [Field α]
```
The `ring` solver also has support for {name}`Field`s.
If a {name}`Field` instance is available, the solver preprocesses the term `a / b` into `a * b⁻¹`.
It also rewrites every disequality `p ≠ 0` as the equality `p * p⁻¹ = 1`.
:::

::::example "Fields and `grind`"
```lean -show
open Lean.Grind
```
This example requires its {name}`Field` instance:

```lean
example [Field α] (a : α) :
    a ^ 2 = 0 →
    a = 0 := by
  grind
```
::::

{docstring Lean.Grind.Field}

## Ring Characteristics

:::TODO

write

:::

{docstring Lean.Grind.IsCharP}


## Natural Number Zero Divisors
%%%
tag := "NoNatZeroDivisors"
%%%


The class `NoNatZeroDivisors` is used to control coefficient growth.
For example, the polynomial `2 * x * y + 4 * z = 0` is simplified to `x * y + 2 * z = 0`.
It also used when processing disequalities.

:::example "Using `NoNatZeroDivisors`"
```lean -show
open Lean.Grind
```
In this example, {tactic}`grind` relies on the {name}`NoNatZeroDivisors` instance to simplify the goal:
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b : α) :
    2 * a + 2 * b = 0 →
    b ≠ -a → False := by
  grind
```
Without it, the proof fails:
```lean (name := NoNatZero) +error
example [CommRing α] (a b : α) :
    2 * a + 2 * b = 0 →
    b ≠ -a → False := by
  grind
```
```leanOutput NoNatZero
`grind` failed
case grind
α : Type u_1
inst : CommRing α
a b : α
h : 2 * a + 2 * b = 0
h_1 : ¬b = -a
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [ring] Ring `α`
```
:::

{docstring Lean.Grind.NoNatZeroDivisors}

{docstring Lean.Grind.NoNatZeroDivisors.mk'}

The `ring` module also performs case-analysis for terms `a⁻¹` on whether `a` is zero or not.
In the following example, if `2*a` is zero, then `a` is also zero since
we have `NoNatZeroDivisors α`, and all terms are zero and the equality hold. Otherwise,
`ring` adds the equalities `a*a⁻¹ = 1` and `2*a*(2*a)⁻¹ = 1`, and closes the goal.

```lean
example [Field α] [NoNatZeroDivisors α] (a : α) :
    1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind
```

Without `NoNatZeroDivisors`, `grind` will perform case splits on numerals being zero as needed:
```lean
example [Field α] (a : α) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind
```

In the following example, `ring` does not need to perform any case split because
the goal contains the disequalities `y ≠ 0` and `w ≠ 0`.

```lean
example [Field α] {x y z w : α} :
    x / y = z / w →
    y ≠ 0 → w ≠ 0 →
    x * w = z * y := by
  grind (splits := 0)
```

You can disable the `ring` solver using the option `grind -ring`.

```lean +error (name := noRing)
example [CommRing α] (x y : α) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind -ring
```
```leanOutput noRing
`grind` failed
case grind
α : Type u_1
inst : CommRing α
x y : α
h : x ^ 2 * y = 1
h_1 : x * y ^ 2 = y
h_2 : ¬y * x = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [linarith] Linarith assignment for `α`
```

### Right-Cancellative Addition
%%%
tag := "AddRightCancel"
%%%

The `ring` solver automatically embeds `CommSemiring`s into a `CommRing` envelope (using the construction `Lean.Grind.Ring.OfSemiring.Q`).
However, the embedding is injective only when the `CommSemiring` implements the type class `AddRightCancel`.
`Nat` is an example of  a commutative semiring that implements `AddRightCancel`.

```lean
example (x y : Nat) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```

{docstring Lean.Grind.AddRightCancel}

# Resource Limits

Gröbner basis computation can be very expensive. You can limit the number of steps performed by the `ring` solver using the option `grind (ringSteps := <num>)`

:::example "Limiting `ring` Steps"
```lean -show
open Lean.Grind
```
This example cannot be solved by performing at most 100 steps:
```lean +error (name := ring100)
example [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α) :
    d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0 →
    -d ^ 4 * (d + t - d * t - 2) *
      (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t^4 +
      2 * d^2 * t^4 - c * (d + t + d * t)) = 0 →
    d * d_inv = 1 →
    (d + t - d * t - 2) * PSO3_inv = 1 →
    t^2 = t + 1 := by
  grind (ringSteps := 100)
```
```leanOutput ring100
`grind` failed
case grind
α : Type u_1
inst : CommRing α
inst_1 : IsCharP α 0
d t c d_inv PSO3_inv : α
h : d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0
h_1 : -d ^ 4 * (d + t - d * t - 2) *
    (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t ^ 4 + 2 * d ^ 2 * t ^ 4 - c * (d + t + d * t)) =
  0
h_2 : d * d_inv = 1
h_3 : (d + t - d * t - 2) * PSO3_inv = 1
h_4 : ¬t ^ 2 = t + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [ring] Ring `α`
  [limits] Thresholds reached
```
:::

The `ring` solver propagates equalities back to the `grind` core by normalizing terms using the computed Gröbner basis.
In the following example, the equations `x ^ 2 * y = 1` and `x * y ^ 2 = y` imply the equalities `x = 1` and `y = 1`.
Thus, the terms `x * y` and `1` are equal, and consequently `some (x * y) = some 1` by congruence.

```lean
example (x y : Int) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    some (y * x) = some 1 := by
  grind
```

:::comment
Planned future features: support for noncommutative rings and semirings.
:::
