/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers

import Manual.Grind.ConstraintPropagation
import Manual.Grind.CongrClosure
import Manual.Grind.CaseAnalysis
import Manual.Grind.EMatching
import Manual.Grind.Cutsat
import Manual.Grind.Algebra
import Manual.Grind.Linarith
import Manual.Grind.Annotation
import Manual.Grind.ExtendedExamples

-- Needed for the if-then-else normalization example.
import Std.Data.TreeMap
import Std.Data.HashMap

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true

-- TODO (@kim-em): `Lean.Grind.AddCommMonoid` and `Lean.Grind.AddCommGroup` are not yet documented.
set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

-- The verso default max line length is 60, which is very restrictive.
-- TODO: discuss with David.
set_option verso.code.warnLineLength 72

open Manual (comment)

#doc (Manual) "The `grind` tactic" =>
%%%
tag := "grind-tactic"
%%%

:::tutorials
 * {ref "grind-index-map" (remote := "tutorials")}[Using `grind` for Ordered Maps]
:::

```lean -show
-- Open some namespaces for the examples.
open Lean Lean.Grind Lean.Meta.Grind
```

The {tactic}`grind` tactic uses techniques inspired by modern SMT solvers to automatically construct proofs.
It produces proofs by incrementally collecting sets of facts, deriving new facts from the existing ones using a set of cooperating techniques.
Behind the scenes, all proofs are by contradiction, so there is no operational distinction between the expected conclusion and the premises; {tactic}`grind` always attempts to derive a contradiction.

Picture a virtual whiteboard.
Every time {tactic}`grind` discovers a new equality, inequality, or Boolean literal it writes that fact on the board, merges equivalent terms into buckets, and invites each engine to read from—and add back to—the shared whiteboard.
In particular, because all true propositions are equal to {lean}`True` and all false propositions are equal to {lean}`False`, {tactic}`grind` tracks a set of known facts as part of tracking equivalence classes.

:::paragraph
The cooperating engines are:

* {tech}[congruence closure],
* {tech}[constraint propagation],
* {tech}[E‑matching],
* guided {ref "grind-split"}[case analysis], and
* a suite of satellite theory solvers, including both {ref "cutsat"}[linear integer arithmetic] and {ref "grind-ring"}[commutative rings].

Like other tactics, {tactic}`grind` produces ordinary Lean proof terms for every fact it adds.
Lean’s standard library is already annotated with `@[grind]` attributes, so common lemmas are discovered automatically.
:::

{tactic}`grind` is *not* designed for goals whose search space explodes combinatorially—think large‑`n` pigeonhole instances, graph‑coloring reductions, high‑order N‑queens boards, or a 200‑variable Sudoku encoded as Boolean constraints.
Such encodings require thousands (or millions) of case‑splits that overwhelm {tactic}`grind`’s branching search.
For bit‑level or pure Boolean combinatorial problems, use {tactic}`bv_decide`.  The {tactic}`bv_decide` tactic calls a state‑of‑the‑art SAT solver (e.g. CaDiCaL or Kissat) and then returns a compact, machine‑checkable certificate.
All heavy search happens outside Lean; the certificate is replayed and verified inside Lean, so trust is preserved (verification time scales with certificate size).

:::TODO
Include this when it's available:
* *Full SMT problems that need substantial case analysis across multiple theories* (arrays, bit‑vectors, rich arithmetic, quantifiers, …) → use the forthcoming *`lean‑smt`* tactic—a tight Lean front‑end for CVC5 that replays unsat cores or models inside Lean.
:::


:::example "Congruence Closure" (open := true)

This proof succeeds instantly using {tech}[congruence closure], which discovers sets of equal terms.

```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  grind
```

:::

:::example "Algebraic Reasoning" (open := true)

This proof uses {tactic}`grind`'s commutative ring solver.

```lean -show
open Lean.Grind
```
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind
```
:::

:::example "Finite-Field Reasoning" (open := true)
Arithmetic operations on {name}`Fin` overflow, wrapping around to {lean  (type := "Fin 11")}`0` when the result would be outside the bound.
{tactic}`grind` can use this fact to prove theorems such as this:

```lean
example (x y : Fin 11) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
:::

:::example "Linear Integer Arithmetic with Case Analysis" (open := true)

```lean
example (x y : Int) :
    27 ≤ 11 * x + 13 * y →
    11 * x + 13 * y ≤ 45 →
    -10 ≤ 7 * x - 9 * y →
    7 * x - 9 * y ≤ 4 →
    False := by
  grind
```

:::

# Error Messages
%%%
tag := "grind-errors"
%%%

When {tactic}`grind` fails, it prints the remaining subgoal followed by all the information returned by its subsystems—the contents of the “shared whiteboard.”
In particular, it presents equivalence classes of terms that it has determined to be equal.
The two largest classes are shown as `True propositions` and `False propositions`, listing every literal currently known to be provable or refutable.
Inspect these lists to spot missing facts or contradictory assumptions.

# Minimizing `grind` calls

The `grind only [...]` tactic invokes {tactic}`grind` with a limited set of theorems, which can improve performance.
Calls to `grind only` can be conveniently constructed using {tactic}`grind?`, which automatically records the theorems used by {tactic}`grind` and suggests a suitable `grind only`.

These theorems will typically include a symbol prefix such as `=`, `←`, or `→`, indicating the
pattern that triggered the instantiation. See the {ref "e-matching"}[section on E-matching] for details.
Some theorems may be labelled with a `usr` prefix, which indicates that a custom pattern was used.

{include 1 Manual.Grind.CongrClosure}

{include 1 Manual.Grind.ConstraintPropagation}

{include 1 Manual.Grind.CaseAnalysis}

{include 1 Manual.Grind.EMatching}

{include 1 Manual.Grind.Cutsat}

{include 1 Manual.Grind.Algebra}

{include 1 Manual.Grind.Linarith}

{include 1 Manual.Grind.Annotation}

# Reducibility

{tech}[Reducible] definitions in terms are eagerly unfolded by {tactic}`grind`.
This enables more efficient definitional equality comparisons and indexing.

:::example "Reducibility and Congruence Closure"
The definition of {name}`one` is not {tech}[reducible]:
```lean
def one := 1
```
This means that {tactic}`grind` does not unfold it:
```lean +error (name := noUnfold)
example : one = 1 := by grind
```
```leanOutput noUnfold
`grind` failed
case grind
h : ¬one = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [cutsat] Assignment satisfying linear constraints
```

{name}`two`, on the other hand, is an abbreviation and thus reducible:
```lean
abbrev two := 2
```

{tactic}`grind` unfolds {name}`two` before adding it to the “whiteboard”, allowing the proof to be completed immediately:
```lean
example : two = 2 := by grind
```
:::

E-matching patterns also unfold reducible definitions.
The patterns generated for theorems about abbreviations are expressed in terms of the unfolded abbreviations.
Abbreviations should not generally be recursive; in particular, when using {tactic}`grind`, recursive abbreviations can result in poor indexing performance and unpredictable patterns.

:::example "E-matching and Unfolding Abbreviations"
When adding {attr}`grind` annotations to theorems, E-matching patterns are generated based on the theorem statement.
These patterns determine when the theorem is instantiated.
The theorem {name}`one_eq_1` mentions the {tech}[semireducible] definition {name}`one`, and the resulting pattern is also {name}`one`:
```lean (name := one_eq_1)
def one := 1

@[grind? =]
theorem one_eq_1 : one = 1 := by rfl
```
```leanOutput one_eq_1
one_eq_1: [one]
```

Applying the same annotation to a theorem about the {tech}`reducible` abbreviation {name}`two` results in a pattern in which {name}`two` is unfolded:
```lean (name := two_eq_2)
abbrev two := 2

@[grind? =]
theorem two_eq_2: two = 2 := by grind
```
```leanOutput two_eq_2
two_eq_2: [@OfNat.ofNat `[Nat] `[2] `[instOfNatNat 2]]
```

:::

:::example "Recursive Abbreviations and `grind`"
Using the {attr}`grind` attribute to add E-matching patterns for a recursive abbreviation's {tech}[equational lemmas] does not result in useful patterns for recursive abbreviations.
The {attrs}`@[grind?]` attribute on this definition of the Fibonacci function results in three patterns, each corresponding to one of the three possibilities:
```lean (name := fib1) -keep
@[grind?]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```
```leanOutput fib1
fib.eq_1: [fib `[0]]
```
```leanOutput fib1
fib.eq_2: [fib `[1]]
```
```leanOutput fib1
fib.eq_3: [fib (#0 + 2)]
```
Replacing the definition with an abbreviation results in patterns in which occurrences of the function are unfolded.
These patterns are not particularly useful:
```lean (name := fib2) -keep
@[grind?]
abbrev fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```
```leanOutput fib2
fib.eq_1: [@OfNat.ofNat `[Nat] `[0] `[instOfNatNat 0]]
```
```leanOutput fib2
fib.eq_2: [@OfNat.ofNat `[Nat] `[1] `[instOfNatNat 1]]
```
```leanOutput fib2
fib.eq_3: [@HAdd.hAdd `[Nat] `[Nat] `[Nat] `[instHAdd] (fib #0) (fib (#0 + 1))]
```
:::



```comment
# Diagnostics
TBD
Threshold notices, learned equivalence classes, integer assignments, algebraic basis, performed splits, instance statistics.

# Troubleshooting & FAQ
TBD
```

{include 1 Manual.Grind.ExtendedExamples}
