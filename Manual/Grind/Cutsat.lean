/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Linear Integer Arithmetic" =>
%%%
tag := "cutsat"
%%%

:::paragraph
The linear integer arithmetic solver, `cutsat`, implements a model-based decision procedure for linear integer arithmetic.
The solver can process four categories of linear polynomial constraints (where `p` is a [linear polynomial](https://en.wikipedia.org/wiki/Degree_of_a_polynomial)):

: Equality

 `p = 0`

: Divisibility

 `d ∣ p`

: Inequality

  `p ≤ 0`

: Disequality

  `p ≠ 0`

It is complete for linear integer arithmetic, and natural numbers are supported by converting them to integers with {name}`Int.ofNat`.
Support for additional types that can be embedded into {lean}`Int` can be added via instances of {name}`Lean.Grind.ToInt`.
Nonlinear terms (e.g. `x * x`) are allowed, and are represented as variables.
The solver is additionally capable of propagating information back to the metaphorical {tactic}`grind` whiteboard, which can trigger further progress from the other subsystems.
:::



::::example "Examples of `cutsat`" (open := true)

All of these statements can be proved using `cutsat`.
In the first example, the left-hand side must be a multiple of 2, and thus cannot be 5:
```lean
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  grind
```

The solver supports mixing equalities and inequalities:
```lean
example {x y : Int} :
    2 * x + 3 * y = 0 →
    1 ≤ x →
    y < 1 := by
  grind
```

It also supports linear divisibility constraints:
```lean
example (a b : Int) :
    2 ∣ a + 1 →
    2 ∣ b + a →
    ¬ 2 ∣ b + 2 * a := by
  grind
```


Without `cutsat`, {tactic}`grind` cannot prove the statement:

```lean (error := true) (name := noCutsat)
example (a b : Int) :
    2 ∣ a + 1 →
    2 ∣ b + a →
    ¬ 2 ∣ b + 2 * a := by
  grind -cutsat
```
```leanOutput noCutsat
`grind` failed
case grind
a b : Int
h : 2 ∣ a + 1
h_1 : 2 ∣ a + b
h_2 : 2 ∣ 2 * a + b
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [linarith] Linarith assignment for `Int`
```
::::

# Rational Solutions
%%%
tag := "cutsat-qlia"
%%%

The solver is complete for linear integer arithmetic.
However, the search can become vast with very few constraints, but `cutsat` was not designed to perform massive case-analysis.
The `qlia` option to {tactic}`grind` reduces the search space by instructing `cutsat` to accept rational solutions.
With this option, `cutsat` is likely to be faster, but it is incomplete.

:::example "Rational Solutions"
The following example has a rational solution, but does not have integer solutions:
```lean
example {x y : Int} :
    27 ≤ 13 * x + 11 * y →
    13 * x + 11 * y ≤ 30 →
    -10 ≤ 9 * x - 7 * y →
    9 * x - 7 * y > 4 := by
  grind
```

Because it uses the rational solution, {tactic}`grind` fails to refute the negation of the goal when `+qlia` is specified:
```lean (error := true) (name := withqlia)
example {x y : Int} :
    27 ≤ 13 * x + 11 * y →
    13 * x + 11 * y ≤ 30 →
    -10 ≤ 9 * x - 7 * y →
    9 * x - 7 * y > 4 := by
  grind +qlia
```
```leanOutput withqlia (expandTrace := cutsat)
`grind` failed
case grind
x y : Int
h : -13 * x + -11 * y + 27 ≤ 0
h_1 : 13 * x + 11 * y + -30 ≤ 0
h_2 : -9 * x + 7 * y + -10 ≤ 0
h_3 : 9 * x + -7 * y + -4 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
    [assign] x := 62/117
    [assign] y := 2
```

The rational model constructed by `cutsat` is in the section `Assignment satisfying linear constraints` in the goal diagnostics.
:::

# Nonlinear Constraints

The solver currently does support nonlinear constraints, and treats nonlinear terms such as `x * x` as variables.

::::example "Nonlinear Terms" (open := true)
`cutsat` fails to prove this theorem:

```lean (error := true) (name := nonlinear)
example (x : Int) : x * x ≥ 0 := by
  grind
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
```

From the perspective of `cutsat`, it is equivalent to:

```lean (error := true) (name := nonlinear2)
example {y : Int} (x : Int) : y ≥ 0 := by
  grind
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
```

:::paragraph
This can be seen by setting the option {option}`trace.grind.cutsat.assert` to {lean}`true`, which traces all constraints processed by `cutsat`.

```lean (error := true) (name := cutsatDiag)
example (x : Int) : x*x ≥ 0 := by
  set_option trace.grind.cutsat.assert true in
  grind
```
```leanOutput cutsatDiag
[grind.cutsat.assert] -1*「1」 + 1 = 0
[grind.cutsat.assert] -1*「x ^ 2 + 1」 + 「x ^ 2」 + 1 = 0
[grind.cutsat.assert] 「x ^ 2」 + 1 ≤ 0
```
The term `x ^ 2` is “quoted” in `「x ^ 2」 + 1 ≤ 0` to indicate that `x ^ 2` is treated as a variable.
:::
::::

# Division and Modulus

The solver supports linear division and modulo operations.

:::example "Linear Division and Modulo with `cutsat`"
```lean
example (x y : Int) :
    x = y / 2 →
    y % 2 = 0 →
    y - 2 * x = 0 := by
  grind
```
:::

# Algebraic Processing

The `cutsat` solver normalizes commutative (semi)ring expressions.

:::example "Commutative (Semi)ring Normalization"
Commutative ring normalization allows this goal to be solved:
```lean
example (a b : Nat)
    (h₁ : a + 1 ≠ a * b * a)
    (h₂ : a * a * b ≤ a + 1) :
    b * a ^ 2 < a + 1 := by
  grind
```
:::

# Propagating Information
%%%
tag := "cutsat-mbtc"
%%%

The solver also implements {deftech}_model-based theory combination_, which is a mechanism for propagating equalities back to the metaphorical shared whiteboard.
These additional equalities may in turn trigger new congruences.
Model-based theory combination increases the size of the search space; it can be disabled using the option `grind -mbtc`.

::::example "Propagating Equalities"
In the example above, the linear inequalities and disequalities imply `y = 0`:
```lean
example (f : Int → Int) (x y : Int) :
    f x = 0 →
    0 ≤ y → y ≤ 1 → y ≠ 1 →
    f (x + y) = 0 := by
  grind
```
Consequently `x = x + y`, so `f x = f (x + y)` by {tech key:="congruence closure"}[congruence].
Without model-based theory combination, the proof gets stuck:
```lean (error := true) (name := noMbtc)
example (f : Int → Int) (x y : Int) :
    f x = 0 →
    0 ≤ y → y ≤ 1 → y ≠ 1 →
    f (x + y) = 0 := by
  grind -mbtc
```
```leanOutput noMbtc
`grind` failed
case grind
f : Int → Int
x y : Int
h : f x = 0
h_1 : -1 * y ≤ 0
h_2 : y + -1 ≤ 0
h_3 : ¬y = 1
h_4 : ¬f (x + y) = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Int`
```
::::

# Other Types
%%%
tag := "cutsat-ToInt"
%%%

The `cutsat` solver can also process linear constraints that contain natural numbers.
It converts them into integer constraints using `Int.ofNat`.

:::example "Natural Numbers with `cutsat`"
```lean
example (x y z : Nat) :
    x < y + z →
    y + 1 < z →
    z + x < 3 * z := by
  grind
```
:::

There is an extensible mechanism via the {lean}`Lean.Grind.ToInt` type class to tell `cutsat` that a type embeds in the integers.
Using this, we can solve goals such as:

```lean
example (a b c : Fin 11) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
  grind

example (a : Fin 2) : a ≠ 0 → a ≠ 1 → False := by
  grind

example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind
```

{docstring Lean.Grind.ToInt}

{docstring Lean.Grind.IntInterval}

# Implementation Notes

::::leanSection
```lean (show := false)
variable {x y : Int}
```

:::paragraph
The implementation of `cutsat` is inspired by Section 4 of {citet cuttingToTheChase}[].
Compared to the paper, it includes several enhancements and modifications such as:

* extended constraint support (equality and disequality),

* an optimized encoding of the `Cooper-Left` rule using a “big”-disjunction instead of fresh variables, and

* decision variable tracking for case splits (disequalities, `Cooper-Left`, `Cooper-Right`).
:::

:::paragraph
The `cutsat` procedure builds a model (that is, an assignment of the variables in the term) incrementally, resolving conflicts through constraint generation.
For example, given a partial model `{x := 1}` and constraint {lean}`3 ∣ 3 * y + x + 1`:

- The solver cannot extend the model to {lean}`y` because {lean}`3 ∣ 3 * y + 2` is unsatisfiable.

- Thus, it resolves the conflict by generating the implied constraint {lean}`3 ∣ x + 1`.

- The new constraint forces the solver to find a new assignment for {lean}`x`.
:::


:::paragraph
When assigning a variable `y`, the solver considers:

- The best upper and lower bounds (inequalities).

- A divisibility constraint.

- All disequality constraints where `y` is the maximal variable.
:::
::::

The `Cooper-Left` and `Cooper-Right` rules handle the combination of inequalities and divisibility.
For unsatisfiable disequalities `p ≠ 0`, the solver generates the case split: `p + 1 ≤ 0 ∨ -p + 1 ≤ 0`.


:::comment
Planned future features: improved constraint propagation.
:::
