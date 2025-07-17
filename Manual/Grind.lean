/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

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

-- The verso default max line length is 60, which is very restrictive.
-- TODO: discuss with David.
set_option verso.code.warnLineLength 72

set_option maxHeartbeats 400000 -- Needed for elaboration of the `IndexMap` example.

open Manual (comment)

#doc (Manual) "The `grind` tactic" =>
%%%
tag := "grind"
%%%

```lean (show := false)
-- Open some namespaces for the examples.
open Lean Lean.Grind Lean.Meta.Grind
```

# Quick Start

* *Availability* – {tactic}`grind` ships with Lean 4 (no extra installation) and is usable in any Lean file—just write `by grind`. No extra `import` is required beyond what your own definitions already need.

* *Library support* – Lean’s standard library is already annotated with `@[grind]` attributes, so common lemmas are discovered automatically. Mathlib will be annotated gradually, starting with its most frequently used theories.

* *First proof*

  ```lean
  example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) :
      a = c := by
    grind
  ```

  This succeeds instantly using congruence closure.

* *Power examples* – showcasing {tactic}`grind`'s satellite solvers:

  * *Algebraic reasoning* (commutative‑ring solver):

    ```lean
    example [CommRing α] [NoNatZeroDivisors α] (a b c : α)
        : a + b + c = 3 →
          a^2 + b^2 + c^2 = 5 →
          a^3 + b^3 + c^3 = 7 →
          a^4 + b^4 = 9 - c^4 := by
      grind
    ```

  * *Finite‑field style reasoning* (works in {lean}`Fin 11`):

    ```lean
    example (x y : Fin 11) :
        x^2*y = 1 → x*y^2 = y → y*x = 1 := by
      grind
    ```

  * *Linear integer arithmetic with case analysis*:

    ```lean
    example (x y : Int) :
        27 ≤ 11*x + 13*y →
        11*x + 13*y ≤ 45 →
        -10 ≤ 7*x - 9*y →
        7*x - 9*y ≤ 4 → False := by
      grind
    ```

* *Useful flags*

  * `by grind (splits := 3) (ematch := 2)` – limit case splits / E‑matching rounds.

# What is {tactic}`grind`?

A proof‑automation tactic inspired by modern SMT solvers.

*Picture a virtual white‑board:* every time {tactic}`grind` discovers a new equality, inequality, or Boolean literal it writes that fact on the board, merges equivalent terms into buckets, and invites each engine to read from—and add back to—the shared white-board. The cooperating engines are:
* congruence closure,
* constraint propagation,
* E‑matching,
* guided case analysis, and
* a suite of satellite theory solvers (linear integer arithmetic, commutative rings, …).

Lean supports dependent types and a powerful type‑class system, and {tactic}`grind` produces ordinary Lean proof terms for every fact it adds.

# What {tactic}`grind` is *not*.

{tactic}`grind` is *not* designed for goals whose search space explodes combinatorially—think large‑`n` pigeonhole instances, graph‑coloring reductions, high‑order N‑queens boards, or a 200‑variable Sudoku encoded as Boolean constraints.  Such encodings require thousands (or millions) of case‑splits that overwhelm {tactic}`grind`’s branching search.

* *Bit‑level or pure Boolean combinatorial problems* → use {tactic}`bv_decide`.
  The {tactic}`bv_decide` tactic calls a state‑of‑the‑art SAT solver (e.g. CaDiCaL or Kissat) and then returns a *compact, machine‑checkable certificate*.  All heavy search happens outside Lean; the certificate is replayed and verified inside Lean, so trust is preserved (verification time scales with certificate size).
* *Full SMT problems that need substantial case analysis across multiple theories* (arrays, bit‑vectors, rich arithmetic, quantifiers, …) → use the forthcoming *`lean‑smt`* tactic—a tight Lean front‑end for CVC5 that replays unsat cores or models inside Lean.

# Congruence Closure

## What is congruence closure?

Congruence closure maintains *equivalence classes of terms* under the reflexive–symmetric–transitive closure of "is equal to" _and_ the rule that equal arguments yield equal function results.  Formally, if `a = a'` and `b = b'`, then `f a b = f a' b'` is added.  The algorithm merges classes until a fixed point is reached.

Think of a *shared white‑board*:

1. Every hypothesis `h : t₁ = t₂` writes a line connecting `t₁` and `t₂`.
2. Each merge paints both terms the same color.  Soon whole constellations (`f a`, `g (f a)`, …) share the color.
3. If {lean}`True` and {lean}`False` ever land in the same color—or likewise two different constructors of the _same inductive type_ such as {lean}`none` and {lean}`some 1`—the goal is closed by contradiction.

## How it differs from {tactic}`simp`

* {tactic}`simp` _rewrites_ a goal, replacing occurrences of `t₁` with `t₂` as soon as it sees `h : t₁ = t₂`.  The rewrite is directional and destructive.
* {tactic}`grind` _accumulates_ equalities bidirectionally.  No term is rewritten; instead, both representatives live in the same class.  All other engines (E‑matching, theory solvers, propagation) can query these classes and add new facts, then the closure updates incrementally.

This makes congruence closure especially robust in the presence of symmetrical reasoning, mutual recursion, and large nestings of constructors where rewriting would duplicate work.

## Minimal examples

```lean
example {α} (f g : α → α) (x y : α)
    (h₁ : x = y) (h₂ : f y = g y) :
    f x = g x := by
  -- After `h₁`, `x` and `y` share a class,
  -- `h₂` adds `f y = g y`, and
  -- closure bridges to `f x = g x`
  grind

example (a b c : Nat) (h : a = b) : (a, c) = (b, c) := by
  -- Pair constructor obeys congruence,
  -- so once `a = b` the tuples are equal
  grind
```

# Debugging tip

When {tactic}`grind` *fails* it prints the remaining subgoal *followed by all equivalence classes*.  The two largest classes are shown as *True propositions* and *False propositions*, listing every literal currently known to be provable or refutable.  Inspect these lists to spot missing facts or contradictory assumptions.

# Constraint Propagation

Constraint propagation works on the *True* and *False* buckets of the white‑board.  Whenever a literal is added to one of those buckets, {tactic}`grind` fires dozens of small _forward rules_ to push its logical consequences:

* Boolean connectives — e.g. if `A` is {lean}`True`, mark `A ∨ B` as {lean}`True`; if `A ∧ B` is {lean}`True`, mark both `A` and `B` as {lean}`True`; if `A ∧ B` is {lean}`False`, at least one of `A`, `B` becomes {lean}`False`.
* Inductive datatypes — two different constructors (`none` vs `some _`) collapsing into the same class yields a contradiction; equal tuples yield equal components.
* Projections and casts — from `h : (x, y) = (x', y')` we derive `x = x'` and `y = y'`; any term `cast h a` is merged with `a` immediately (using a heterogeneous equality) so both live in the same class.
* Structural eta and definitional equalities — `⟨a, b⟩.1` propagates to `a`, etc.

Below is a _representative slice_ of the propagators so you can see the style they follow.  Each follows the same skeleton: inspect the truth‑value of sub‑expressions, push equalities ({lean}`pushEq`) or truth‑values ({lean}`pushEqTrue` / {lean}`pushEqFalse`), and optionally close the goal if a contradiction ({lean}`closeGoal`) arises.  A few high‑signal examples:

```lean (show := false)
namespace ExamplePropagators
```
```lean (keep := false)

/-- Propagate equalities *upwards* for conjunctions. -/
builtin_grind_propagator propagateAndUp ↑And := fun e => do
  let_expr And a b := e | return ()
  if (← isEqTrue a) then
    -- a = True  ⇒  (a ∧ b) = b
    pushEq e b <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_left)
        a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    pushEq e a <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_right)
        a b (← mkEqTrueProof b)
  else if (← isEqFalse a) then
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_left)
        a b (← mkEqFalseProof a)
  else if (← isEqFalse b) then
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_right)
        a b (← mkEqFalseProof b)

/--
Truth flows *down* when the whole `And` is proven `True`.
-/
builtin_grind_propagator propagateAndDown ↓And :=
  fun e => do
  if (← isEqTrue e) then
    let_expr And a b := e | return ()
    let h ← mkEqTrueProof e
    pushEqTrue a <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_left) a b h
    pushEqTrue b <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_right) a b h
```
```lean (show := false)
end ExamplePropagators
```

Other frequently‑triggered propagators follow the same pattern:

:::table (header := true)
*
  * Propagator
  * Handles
  * Notes
*
  * {lean}`propagateOrUp` / {lean}`propagateOrDown`
  * `a ∨ b`
  * True/False pushes for disjunctions
*
  * {lean}`propagateNotUp` / {lean}`propagateNotDown`
  * `¬ a`
  * Links `¬ a` with the Boolean of `a`
*
  * {lean}`propagateEqUp` / {lean}`propagateEqDown`
  * `a = b`
  * Bridges Booleans, detects constructor clash
*
  * {lean}`propagateIte` / {lean}`propagateDIte`
  * `ite` / `dite`
  * Replaces chosen branch once condition is fixed
*
  * `propagateEtaStruct`
  * structures tagged `[grind ext]`
  * Generates η‑expansion `a = ⟨a.1, …⟩`
:::

:::comment
TODO (@kim-em): we don't add the `{lean}` literal type to `propagateEtaStruct` above because it is private.
:::

Many specialized variants for {lean}`Bool` mirror these rules exactly (e.g. {lean}`propagateBoolAndUp`).

## Propagation‑only examples

These goals are closed *purely* by constraint propagation—no case splits, no theory solvers:

```lean
-- Boolean connective: a && !a is always false.
example (a : Bool) : (a && !a) = false := by
  grind

-- Conditional (ite):
-- once the condition is true, ite picks the 'then' branch.
example (c : Bool) (t e : Nat) (h : c = true) :
    (if c then t else e) = t := by
  grind

-- Negation propagates truth downwards.
example (a : Bool) (h : (!a) = true) : a = false := by
  grind
```

These snippets run instantly because the relevant propagators ({lean}`propagateBoolAndUp`, {lean}`propagateIte`, {lean}`propagateBoolNotDown`) fire as soon as the hypotheses are internalized.

> *Note* If you toggle `set_option trace.grind.eqc true`, {tactic}`grind` will print a line every time two equivalence classes merge—handy for seeing propagation in action.

*Implementation tip*  {tactic}`grind` is still under active development. Until the API has stabilized we recommend _refraining from custom elaborators or satellite solvers_. If you really need a project‑local propagator, use the user‑facing `grind_propagator` command rather than `builtin_grind_propagator` (the latter is reserved for Lean’s own code). When adding new propagators keep them *small and orthogonal*—they should fire in ≤1 µs and either push one fact or close the goal. This keeps the propagation phase predictable and easy to debug.

We continuously expand and refine the rule set—expect the *Info View* to show increasingly rich {lean}`True`/{lean}`False` buckets over time. The full equivalence classes are displayed automatically _only when {tactic}`grind` fails_, and only for the first subgoal it could not close—use this output to inspect missing facts and understand why the subgoal remains open.

# Case Analysis

## Selection heuristics

{tactic}`grind` decides which sub‑term to split on by combining three sources of signal:

1. *Structural flags* — quick Booleans that enable whole syntactic classes:

   * `splitIte` (default {lean}`true`) → split every `if … then … else …` term.
   * `splitMatch` (default {lean}`true`) → split on all `match` expressions (the {tactic}`grind` analogue of Lean’s {tactic}`split` tactic, just like `splitIte`).
   * `splitImp` (default {lean}`false`) → when {lean}`true` splits on any hypothesis `A → B` whose antecedent `A` is *propositional*.  Arithmetic antecedents are special‑cased: if `A` is an arithmetic literal (`≤`, `=`, `¬`, `Dvd`, …) {tactic}`grind` will split _even when `splitImp := false`_ so the integer solver can propagate facts.

👉 Shorthand toggles: `by grind -splitIte +splitImp` expands to `by grind (splitIte := false) (splitImp := true)`.
2. *Global limit* — `splits := n` caps the *depth* of the search tree.  Once a branch performs `n` splits {tactic}`grind` stops splitting further in that branch; if the branch cannot be closed it reports that the split threshold has been reached.
3. *Manual annotations* — you may mark *any* inductive predicate or structure with

  :::comment
  Note this *not* a lean code block, because `Even` and `Sorted` do not exist.
  TODO: replace this with a checkable example.
  :::
  ```
  attribute [grind cases] Even Sorted
  ```

  and {tactic}`grind` will treat every instance of that predicate as a candidate for splitting.

## Examples

```lean
-- splitIte demonstration
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind

example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  -- The following fails because we need one case split
  fail_if_success grind (splits := 0)
  grind (splits := 1)

-- User‑defined predicate with [grind cases]
inductive Even : Nat → Prop
  | zero : Even 0
  | step : Even n → Even (n+2)

attribute [grind cases] Even

example (h : Even 5) : False := by
  -- With the attribute,
  -- grind immediately splits on the Even hypothesis
  grind

example (h : Even (n + 2)) : Even n := by
  grind

example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  -- `grind` fails if we disable `splitMatch`
  fail_if_success grind -splitMatch
  grind
```

## Tips

* Increase `splits` *only* when the goal genuinely needs deeper branching; each extra level multiplies the search space.
* Disable `splitMatch` when large pattern‑matching definitions explode the tree.
* You can combine flags: `by grind -splitMatch (splits := 10) +splitImp`.
* The `[grind cases]` attribute is *scoped*; you can use the modifiers `local`/`scoped` if you only want extra splits inside a section or namespace.

# E‑matching

E-matching is a mechanism used by `grind` to instantiate theorems efficiently.
It is especially effective when combined with congruence closure, enabling
`grind` to discover non-obvious consequences of equalities and annotated theorems
automatically.

Consider the following functions and theorems:
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```
The theorem `gf` asserts that `g (f x) = x` for all natural numbers `x`.
The attribute `[grind =]` instructs `grind` to use the left-hand side of the equation,
`g (f x)`, as a pattern for heuristic instantiation via E-matching.
Suppose we now have a goal involving:
```lean
example {a b} (h : f b = a) : g a = b := by
  grind
```
Although `g a` is not an instance of the pattern `g (f x)`,
it becomes one modulo the equation `f b = a`.
By substituting `a` with `f b` in `g a`, we obtain the term `g (f b)`,
which matches the pattern `g (f x)` with the assignment `x := b`.
Thus, the theorem `gf` is instantiated with `x := b`,
and the new equality `g (f b) = b` is asserted.
`grind` then uses congruence closure to derive the implied equality
`g a = g (f b)` and completes the proof.

The pattern used to instantiate theorems affects the effectiveness of `grind`.
For example, the pattern `g (f x)` is too restrictive in the following case:
the theorem `gf` will not be instantiated because the goal does not even
contain the function symbol `g`.

```lean (error := true)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```

You can use the command `grind_pattern` to manually select a pattern for a given theorem.
In the following example, we instruct `grind` to use `f x` as the pattern,
allowing it to solve the goal automatically:
```lean
grind_pattern gf => f x

example {a b c} (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```
You can enable the option `trace.grind.ematch.instance` to make `grind` print a
trace message for each theorem instance it generates.
```lean
/--
trace: [grind.ematch.instance] gf: g (f c) = c
[grind.ematch.instance] gf: g (f b) = b
-/
#guard_msgs (trace) in
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  set_option trace.grind.ematch.instance true in
  grind
```

You can also specify a *multi-pattern* to control when `grind` should instantiate a theorem.
A multi-pattern requires that all specified patterns are matched in the current context
before the theorem is instantiated. This is useful for lemmas such as transitivity rules,
where multiple premises must be simultaneously present for the rule to apply.
The following example demonstrates this feature using a transitivity axiom for a binary relation `R`:
```lean (keep := false)
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z

grind_pattern Rtrans => R x y, R y z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```
By specifying the multi-pattern `R x y, R y z`, we instruct `grind` to
instantiate `Rtrans` only when both `R x y` and `R y z` are available in the context.
In the example, `grind` applies `Rtrans` to derive `R a c` from `R a b` and `R b c`,
and can then repeat the same reasoning to deduce `R a d` from `R a c` and `R c d`.

Instead of using `grind_pattern` to explicitly specify a pattern,
you can use the `@[grind]` attribute or one of its variants, which will use a heuristic to generate a (multi-)pattern.
The `@[grind?]` attribute displays an info message showing the pattern which was selected—this is very helpful for debugging!

* `@[grind →]` will select a multi-pattern from the hypotheses of the theorem (i.e. it will use the theorem for forwards reasoning).
  In more detail, it will traverse the hypotheses of the theorem from left-to-right, and each time it encounters a minimal indexable (i.e. has a constant as its head) subexpression which "covers" (i.e. fixes the value of) an argument which was not previously covered, it will add that subexpression as a pattern, until all arguments have been covered. This rule is described in more detail below.
* `@[grind ←]` will select a multi-pattern from the conclusion of theorem (i.e. it will use the theorem for backwards reasoning).
  This may fail if not all the arguments to the theorem appear in the conclusion.
* `@[grind]` will traverse the conclusion and then the hypotheses left-to-right, adding patterns as they increase the coverage, stopping when all arguments are covered.
* `@[grind =]` checks that the conclusion of the theorem is an equality, and then uses the left-hand-side of the equality as a pattern.
  This may fail if not all of the arguments appear in the left-hand-side.
* `@[grind =_]` is like `@[grind =]`, but using the right-hand-side of the equality.
* `@[grind _=_]` acts like a macro which expands to `@[grind =, grind =_]` (i.e. it will add *two* multipatterns, allowing the equality theorem to trigger in either direction).

Although it is tempting to just use `@[grind]` by default, we recommend that when one of the other forms achieves the desired effect, you use those.
In every case, it is worthwhile to verify the chosen pattern using `@[grind?]` (which accepts all of these modifiers).

There are also three less commonly used modifiers:

* `@[grind =>]` traverses all the hypotheses left-to-right and then the conclusion.
* `@[grind <=]` traverses the conclusion and then all hypotheses right-to-left.
* `@[grind ←=]` is unlike the others, and it used specifically for backwards reasoning on equality. As an example, suppose we have a theorem
  ```lean (keep := false)
  theorem inv_eq [One α] [Mul α] [Inv α] {a b : α} (w : a * b = 1) : a⁻¹ = b := sorry
  ```
  Adding `@[grind ←=]` will cause this theorem to be instantiated whenever we are trying to prove `a⁻¹ = b`, i.e. whenever we have the disequality `a⁻¹ ≠ b` (recall `grind` proves goals by contradiction).
  Without special support via `←=` this instantiation would be not possible as `grind` does not consider the `=` symbol while generating patterns.


The rule for selecting patterns from subexpressions of the hypotheses and conclusion as described above is subtle, so we'll give some examples.

```lean
axiom p : Nat → Nat
axiom q : Nat → Nat

/-- info: h₁: [q #1] -/
#guard_msgs (info) in
@[grind? →] theorem h₁ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```

First, to understand the output we need to recall that the `#n` appearing in patterns are arguments of the theorem, numbered as de-Bruijn variables, i.e. in reverse order (so `#0` would be `w : p (q x) = 7`, while `#1` is the implicit argument `x`).

Why was `q #1` selected when we use `@[grind →]`? The attribute `@[grind →]` instructed grind to find patterns by traversing the hypotheses from left-to-right.
In this case, there's only the one hypothesis `p (q x) = 7`. The heuristic described above says that `grind` will search for a minimal indexable subexpression which covers a previously uncovered argument.
There's just one uncovered argument, `x`, so we're looking for a minimal expression containing that.
We can't take the whole `p (q x) = 7` because `grind` will not index on equality. The right-hand-side `7` is not helpful, because it doesn't determine the value of `x`.
We don't take `p (q x)` because it is not minimal: it has `q x` inside of it, which is indexable (its head is the constant `q`),
and it determines the value of `x`. The expression `q x` itself is minimal, because `x` is not indexable. Thus {tactic}`grind` selects `q x` as the pattern.

Let's see some more examples:
```lean
/-- info: h₂: [p (#1 + 1)] -/
#guard_msgs (info) in
@[grind? ←] theorem h₂ (w : 7 = p (q x)) : p (x + 1) = q x := sorry

/--
info: h₃: [p (#1 + 1)]
---
info: h₃: [q #1]
-/
#guard_msgs (info) in
@[grind? _=_] theorem h₃ (w : 7 = p (q x)) : p (x + 1) = q x := sorry

/-- info: h₄: [p (#2 + 2), q #1] -/
#guard_msgs (info) in
@[grind?] theorem h₄ (w : p x = q y) : p (x + 2) = 7 := sorry

/--
error: `@[grind ←] theorem h₅` failed to
find patterns in the theorem's conclusion,
consider using different options or the `grind_pattern` command
-/
#guard_msgs (error) in
@[grind? ←] theorem h₅ (w : p x = q y) : p (x + 2) = 7 := sorry

/-- info: h₆: [q (#3 + 2), p (#2 + 2)] -/
#guard_msgs (info) in
@[grind? =>] theorem h₆ (_ : q (y + 2) = q y) (_ : q (y + 1) = q y) : p (x + 2) = 7 := sorry
```

If you're planning to do substantial annotation work, you should study these examples and verify that
they follow the rules described above.

E-matching can generate too many theorem instances. Some patterns may even generate an unbounded
number of instances. For example, consider the pattern `s x` in the following example.

```lean (error := true)
def s (x : Nat) := 0

@[grind =] theorem s_eq (x : Nat) : s x = s (x + 1) :=
  rfl

example : s 0 > 0 := by
  grind
```

In the example above, `grind` instantiates `s_eq` with `x := 0` which generates the term
`s 1` with is then used to instantiate `s_eq` with `x := 1` which generates the term `s 2`
and so on. The instantiation process is interrupted using the `generation` threshold.
Terms occurring in the input goal have `generation` zero. When `grind` instantiates
a theorem using terms with generation `≤ n`, the new generated terms have generation `n+1`.
You can set the maximum generation using the option `grind (gen := <num>)`.
You can also control the number of E-matching rounds using the option `grind (ematch := <num>)`.
In the following example, we prove that `(iota 20).length > 10` by instantiating `iota_succ`
and `List.length_cons`

```lean
def iota : Nat → List Nat
  | 0 => []
  | n+1 => n :: iota n

@[grind =] theorem iota_succ : iota (n+1) = n :: iota n :=
  rfl

example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```

You can set the option `set_option diagnostics true` to obtain the number of
theorem instances generated by `grind` per theorem. This is useful to detect
theorems that contain patterns that are triggering too many instances.

:::comment
FIXME: the relevant grind diagnostic hover doesn't show up in the docs, it's obscured by generic diagnostics.
:::
```lean
set_option diagnostics true in
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```

By default, `grind` uses automatically generated equations for `match`-expressions as E-matching theorems.

```lean
example (x y : Nat)
    : x = y + 1 →
      0 < match x with
          | 0 => 0
          | _+1 => 1 := by
  grind
```

You can disable this feature by using `grind -matchEqs`

```lean (error := true)
example (x y : Nat)
    : x = y + 1 →
      0 < match x with
          | 0 => 0
          | _+1 => 1 := by
  grind -matchEqs
```

:::comment
TBD
* anti‑patterns
* local vs global attributes
* `gen` modifier?
:::

# Linear Integer Arithmetic Solver

The linear integer arithmetic solver, `cutsat`, implements a model-based decision procedure for linear integer arithmetic,
inspired by Section 4 of "Cutting to the Chase: Solving Linear Integer Arithmetic".
The implementation in `grind` includes several enhancements and modifications such as

- Extended constraint support (equality and disequality).
- Optimized encoding of the `Cooper-Left` rule using a "big"-disjunction instead of fresh variables.
- Decision variable tracking for case splits (disequalities, `Cooper-Left`, `Cooper-Right`).

The solver can process four categories of linear polynomial constraints (where `p` is a linear polynomial):
1. Equality:     `p = 0`
2. Divisibility: `d ∣ p`
3. Inequality:   `p ≤ 0`
4. Disequality:  `p ≠ 0`

The procedure builds a model incrementally, resolving conflicts through constraint generation.
For example, given a partial model `{x := 1}` and constraint `3 ∣ 3*y + x + 1`:
- The solve cannot extend the model to `y` because `3 ∣ 3*y + 2` is unsatisfiable.
- Thus, it resolves the conflict by generating the implied constraint `3 ∣ x + 1`.
- The new constraint forces the solver to find a new assignment for `x`.

When assigning a variable `y`, the solver considers:
- The best upper and lower bounds (inequalities).
- A divisibility constraint.
- All disequality constraints where `y` is the maximal variable.

The `Cooper-Left` and `Cooper-Right` rules handle the combination of inequalities and divisibility.
For unsatisfiable disequalities `p ≠ 0`, the solver generates the case split: `p + 1 ≤ 0 ∨ -p + 1 ≤ 0`.

The following examples demonstrate goals that can be decide by `cutsat`.

```lean
-- The left-hand-side is a multiple of 2.
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  grind

-- Mixing equalities and inequalities.
example {x y : Int} : 2 * x + 3 * y = 0 → 1 ≤ x → y < 1 := by
  grind

-- Linear divisibility constraints.
example (a b : Int) : 2 ∣ a + 1 → 2 ∣ b + a → ¬ 2 ∣ b + 2*a := by
  grind
```

You can disable this solver using the option  `grind -cutsat`.

```lean (error := true)
example (a b : Int) : 2 ∣ a + 1 → 2 ∣ b + a → ¬ 2 ∣ b + 2*a := by
  grind -cutsat
```

The solver is complete for linear integer arithmetic.
The following example has a rational solution, but does not have integer ones.

```lean
-- The following example has rational solutions, but no integer one.
example {x y : Int}
    : 27 ≤ 13*x + 11*y → 13*x + 11*y ≤ 30 →
      -10 ≤ 9*x - 7*y → 9*x - 7*y > 4 := by
  grind
```

The search can become vast with very few constraints, but `cutsat` was
not designed to perform massive case-analysis. You can reduce the search
space by instructing `cutsat` to accept rational solutions using the option
`grind +qlia`.

```lean (error := true)
example {x y : Int}
    : 27 ≤ 13*x + 11*y → 13*x + 11*y ≤ 30 →
      -10 ≤ 9*x - 7*y → 9*x - 7*y > 4 := by
  grind +qlia
```

In the example above, you can inspect the rational model constructed by `cutsat`
by expanding the section "Assignment satisfying linear constraints" in the goal
diagnostics.

The solver currently does not have support for nonlinear constraints, and treats
nonlinear terms such as `x*x` as variables. Thus, it fails to solve the following goal.
You can use the option `trace.grind.cutsat.assert` to trace all constraints processed
by `cutsat`. Note that the term `x*x` is "quoted" in `「x * x」 + 1 ≤ 0` to indicate
that `x*x` is treated as a variable.

```lean (error := true)
example (x : Int) : x*x ≥ 0 := by
  set_option trace.grind.cutsat.assert true in
  grind
```

The solver also implements model-based theory combination. This is a mechanism for
propagating equalities back to the core module that might trigger new congruences.

```lean
example (f : Int → Int) (x y : Int)
    : f x = 0 → 0 ≤ y → y ≤ 1 → y ≠ 1 →
      f (x + y) = 0 := by
  grind
```

In the example above, the linear inequalities and disequalities imply `y = 0`,
and consequently `x = x + y`, and `f x = f (x + y)` by congruence.
Model-based theory combination increases the size of the search space, and you
can disable it using the option `grind -mbtc`

```lean (error := true)
example (f : Int → Int) (x y : Int)
    : f x = 0 → 0 ≤ y → y ≤ 1 → y ≠ 1 →
      f (x + y) = 0 := by
  grind -mbtc
```

The `cutsat` solver can also process linear constraints containing natural numbers.
It converts them into integer constraints by using `Int.ofNat`.

```lean
example (x y z : Nat) : x < y + z → y + 1 < z → z + x < 3*z := by
  grind
```

The solver also supports linear division and modulo operations.

```lean
example (x y : Int) : x = y / 2 → y % 2 = 0 → y - 2*x = 0 := by
  grind
```

The `cutsat` solver normalizes commutative (semi)ring expressions, so can solve goals like
```lean
example (a b : Nat) (h₁ : a + 1 ≠ a * b * a) (h₂ : a * a * b ≤ a + 1) : b * a^2 < a + 1 := by
  grind
```

There is an extensible mechanism via the {lean}`Lean.Grind.ToInt` typeclass to tell cutsat that a type embeds in the integers.
Using this, we can solve goals such as:

```lean
example (a b c : Fin 11) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
  grind

example (a : Fin 2) : a ≠ 0 → a ≠ 1 → False := by
  grind

example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind
```

Planned future features: improved constraint propagation.

# Algebraic Solver (Commutative Rings, Fields)

The `ring` solver is inspired by Gröbner basis computation procedures and term rewriting completion.
It views multivariate polynomials as rewriting rules. For example, the polynomial equality `x*y + x - 2 = 0`
is treated as a rewriting rule `x*y ↦ -x + 2`. It uses superposition to ensure the rewriting system is
confluent. Users can enable the `ring` solver for their own types by providing instances of
the following type classes, all in the `Lean.Grind` namespace.
The algebraic solvers will self-configure depending on the availability of these typeclasses, so not all need to be provided.
The capabilities of the algebraic solvers will of course degrade when some are not available.

{docstring Lean.Grind.Semiring}

{docstring Lean.Grind.Ring}

{docstring Lean.Grind.CommSemiring}

{docstring Lean.Grind.CommRing}

{docstring Lean.Grind.IsCharP}

{docstring Lean.Grind.AddRightCancel}

{docstring Lean.Grind.NoNatZeroDivisors}

{docstring Lean.Grind.Field}

The Lean standard library contains the applicable instances for the types defined in core.
Mathlib is also pre-configured. For example, the Mathlib `CommRing` type class implements
the `Lean.Grind.CommRing α` to ensure the `ring` solver works out-of-the-box.

The following examples demonstrate goals that can be decided by the `ring` solver.

```lean
open Lean Grind

example [CommRing α] (x : α) : (x + 1)*(x - 1) = x^2 - 1 := by
  grind

-- The solver "knows" that `16*16 = 0` because the
-- ring characteristic is `256`.
example [CommRing α] [IsCharP α 256] (x : α)
    : (x + 16)*(x - 16) = x^2 := by
  grind

-- Types in the std library implement the appropriate type classes.
-- `UInt8` is a commutative ring with characteristic `256`.
example (x : UInt8) : (x + 16)*(x - 16) = x^2 := by
  grind

example [CommRing α] (a b c : α)
    : a + b + c = 3 →
      a^2 + b^2 + c^2 = 5 →
      a^3 + b^3 + c^3 = 7 →
      a^4 + b^4 = 9 - c^4 := by
  grind

example [CommRing α] (x y : α)
    : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind

-- `ring` proves that `a + 1 = 2 + a` is unsatisfiable because
-- the characteristic is known.
example [CommRing α] [IsCharP α 0] (a : α)
    : a + 1 = 2 + a → False := by
  grind
```

Even when the characteristic is not initially known, when `grind` discovers that `n = 0` for some numeral `n`, it makes inferences about the characteristic:
```lean
example [CommRing α] (a b c : α)
    (h₁ : a + 6 = a) (h₂ : c = c + 9) (h : b + 3*c = 0) :
    27*a + b = 0 := by
  grind
```

The class `NoNatZeroDivisors` is used to control coefficient growth.
For example, the polynomial `2*x*y + 4*z = 0` is simplified to `x*y + 2*z = 0`.
It also used when processing disequalities. In the following example,
if you remove the local instance `[NoNatZeroDivisors α]`, the goal will not be solved.

```lean
example [CommRing α] [NoNatZeroDivisors α] (a b : α)
    : 2*a + 2*b = 0 → b ≠ -a → False := by
  grind
```

The `ring` solver also has support for `[Field α]`. During preprocessing,
it rewrites the term `a/b` as `a*b⁻¹`. It also rewrites every disequality
`p ≠ 0` as the equality `p * p⁻¹ = 1`. This transformation is essential to
prove the following example:

```lean
example [Field α] (a : α)
    : a^2 = 0 → a = 0 := by
  grind
```

The `ring` module also performs case-analysis for terms `a⁻¹` on whether `a` is zero or not.
In the following example, if `2*a` is zero, then `a` is also zero since
we have `NoNatZeroDivisors α`, and all terms are zero and the equality hold. Otherwise,
`ring` adds the equalities `a*a⁻¹ = 1` and `2*a*(2*a)⁻¹ = 1`, and closes the goal.

```lean
example [Field α] [NoNatZeroDivisors α] (a : α)
    : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind
```

Without `NoNatZeroDivisors`, `grind` will perform case splits on numerals being zero as needed:
```lean
example [Field α] (a : α) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind
```

In the following example, `ring` does not need to perform any case split because
the goal contains the disequalities `y ≠ 0` and `w ≠ 0`.

```lean
example [Field α] {x y z w : α}
    : x / y = z / w → y ≠ 0 → w ≠ 0 → x * w = z * y := by
  grind (splits := 0)
```

You can disable the `ring` solver using the option `grind -ring`.

```lean (error := true)
example [CommRing α] (x y : α)
    : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind -ring
```

The `ring` solver automatically embeds `CommSemiring`s into a `CommRing` envelope (using the construction `Lean.Grind.Ring.OfSemiring.Q`).
However, the embedding is injective only when the `CommSemiring` implements the type class `AddRightCancel`.
The type `Nat` is an example of such a commutative semiring implementing `AddRightCancel`.

```lean
example (x y : Nat)
    : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind
```

Gröbner basis computation can be very expensive. You can limit the number of steps performed by
the `ring` solver using the option `grind (ringSteps := <num>)`

```lean (error := true)
example {α} [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α)
    : d^2 * (d + t - d * t - 2) * (d + t + d * t) = 0 →
     -d^4 * (d + t - d * t - 2) *
     (2 * d + 2 * d * t - 4 * d * t^2 + 2 * d * t^4 +
      2 * d^2 * t^4 - c * (d + t + d * t)) = 0 →
     d * d_inv = 1 →
     (d + t - d * t - 2) * PSO3_inv = 1 →
     t^2 = t + 1 := by
  -- This example cannot be solved by performing at most 100 steps
  grind (ringSteps := 100)
```

The `ring` solver propagates equalities back to the `grind` core by normalizing terms using the
computed Gröbner basis. In the following example, the equations `x^2*y = 1` and `x*y^2 = y` imply the equalities
`x = 1` and `y = 1`. Thus, the terms `x*y` and `1` are equal, and consequently `some (x*y) = some 1`
by congruence.

```lean
example (x y : Int)
    : x^2*y = 1 → x*y^2 = y → some (y*x) = some 1 := by
  grind
```

Planned future features: support for noncommutative rings and semirings.

# Linear Arithmetic Solver

`grind` also contains a linear arithmetic `linarith` solver parametrized by type classes.
It self-configures depending on the availability of these type classes, so not all need to be provided.
The capabilities of the `linarith` solver will of course degrade when some are not available.
The solver ignores any type supported by `cutsat`. This module is useful for reasoning about `Real`,
ordered vector spaces, etc.

The main type classes for module structures are `NatModule` (every `Semiring` is a `NatModule`) and `IntModule` (every `Ring` is an `IntModule`).
These may interact with the three order classes `Preorder`, `PartialOrder`, and `LinearOrder`.
(Typically a `Preorder` is enough when the context already includes a contradiction, but to prove linear inequality goals you will need a `LinearOrder`.)
To express that the additive structure in a module is compatible with the order we need `OrderedAdd`. We have limited support for ordered rings at present, represented by the typeclass `OrderedRing`.

{docstring Lean.Grind.NatModule}

{docstring Lean.Grind.IntModule}

{docstring Lean.Grind.Preorder}

{docstring Lean.Grind.PartialOrder}

{docstring Lean.Grind.LinearOrder}

{docstring Lean.Grind.OrderedAdd}

{docstring Lean.Grind.OrderedRing}

The core functionality of `linarith` is a model based solver for linear inequalities with integer coefficients.
You can disable this solver using the option `grind -linarith`.

The following examples demonstrate goals that can be decided by the `linarith` solver.

```lean (show := false)
section
```
```lean
variable [IntModule α] [LinearOrder α] [OrderedAdd α]

example (a b : α) : 2*a + b ≥ b + a + a := by grind
example (a b : α) (h : a ≤ b) : 3 * a + b ≤ 4 * b := by grind
example (a b c : α) (_ : a = b + c) (_ : 2 * b ≤ c) :
    2 * a ≤ 3 * c := by grind

example (a b c d e : α) :
    2*a + b ≥ 0 → b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0
    → a ≥ 3*c → c ≥ 6*e → d - 5*e ≥ 0
    → a + b + 3*c + d + 2*e < 0 → False := by
  grind
```
```lean (show := false)
end
```

```lean (show := false)
section
```
At present we only use the `CommRing` structure to do basic normalization (e.g. identifying linear atoms `a * b` and `b * a`),
and to allow constants (with the fact `0 < 1`) and scalar multiplication on both sides.

```lean
variable [CommRing R] [LinearOrder R] [OrderedRing R]

example (a b : R) (h : a * b ≤ 1) : b * 3 * a + 1 ≤ 4 := by grind

example (a b c d e f : R) :
    2*a + b ≥ 1 → b ≥ 0 → c ≥ 0 → d ≥ 0 → e*f ≥ 0
    → a ≥ 3*c → c ≥ 6*e*f → d - f*e*5 ≥ 0
    → a + b + 3*c + d + 2*e*f < 0 → False := by
  grind
```
```lean (show := false)
end
```

Planned future features
* Support for `NatModule` (by embedding in the Grothendieck envelope, as we already do for semirings),
* Better communication between the `ring` and `linarith` solvers.
  There is currently very little communication between these two solvers.
* Non-linear arithmetic over ordered rings.

:::comment
# Diagnostics
TBD
Threshold notices, learned equivalence classes, integer assignments, algebraic basis, performed splits, instance statistics.

# Troubleshooting & FAQ
TBD
:::

# Bigger Examples

## Integrating `grind`'s features.

This example demonstrates how the various submodules of `grind` are seamlessly integrated. In particular we can
* instantiate theorems from the library, using custom patterns,
* perform case splitting,
* do linear integer arithmetic reasoning, including modularity conditions, and
* do Gröbner basis reasoning
all without providing explicit instructions to drive the interactions between these modes of reasoning.

For this example we'll being with a "mocked up" version of the real numbers, and the `sin` and `cos` functions.
Of course, this example works [without any changes](https://github.com/leanprover-community/mathlib4/blob/master/MathlibTest/grind/trig.lean) using Mathlib's versions of these!

```lean
axiom R : Type

-- TODO: a `sorry` here was causing a run-time crash. It's unclear why.
@[instance] axiom instCommRingR : Lean.Grind.CommRing R

axiom sin : R → R
axiom cos : R → R
axiom trig_identity : ∀ x, (cos x)^2 + (sin x)^2 = 1
```

Our first step is to tell grind to "put the trig identity on the whiteboard" whenever it sees a goal involving `sin` or `cos`:

```lean
grind_pattern trig_identity => cos x
grind_pattern trig_identity => sin x
```

Note here we use *two* different patterns for the same theorem, so the theorem is instantiated even if `grind` sees just one of these functions.
If we preferred to more conservatively instantiate the theorem only when both `sin` and `cos` are present, we could have used a multi-pattern:

```lean (keep := false)
grind_pattern trig_identity => cos x, sin x
```

For this example, either approach will work.

Because `grind` immediately notices the trig identity, we can prove goals like this:
```lean
example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind
```
Here `grind`:
* Notices `cos x` and `sin x`, so instantiates the trig identity.
* Notices that this is a polynomial in `CommRing R`, so sends it to the Gröbner basis module.
  No calculation happens at this point: it's the first polynomial relation in this ring, so the Gröbner basis is updated to `[(cos x)^2 + (sin x)^2 - 1]`.
* Notices that the left and right hand sides of the goal are polynomials in `CommRing R`, so sends them to the Gröbner basis module for normalization.
* Since their normal forms modulo `(cos x)^2 + (sin x)^2 = 1` are equal, their equivalence classes are merged, and the goal is solved.

We can also do this sort of argument when congruence closure is needed:
```lean
example (f : R → Nat) :
    f ((cos x + sin x)^2) = f (2 * cos x * sin x + 1) := by
  grind
```

As before, `grind` instantiates the trig identity, notices that `(cos x + sin x)^2` and `2 * cos x * sin x + 1` are equal modulo `(cos x)^2 + (sin x)^2 = 1`,
puts those algebraic expressions in the same equivalence class, and then puts the function applications `f((cos x + sin x)^2)` and `f(2 * cos x * sin x + 1)` in the same equivalence class,
and closes the goal.

Notice that we've used arbitrary function `f : R → Nat` here; let's check that `grind` can use some linear integer arithmetic reasoning after the Gröbner basis steps:
```lean
example (f : R → Nat) :
    4 * f ((cos x + sin x)^2) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind
```

Here `grind` first works out that this goal reduces to `4 * x ≠ 2 + x` for some `x : Nat` (i.e. by identifying the two function applications as described above),
and then uses modularity to derive a contradiction.

Finally, we can also mix in some case splitting:
```
example (f : R → Nat) : max 3 (4 * f ((cos x + sin x)^2)) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind
```
As before, `grind` first does the instantiation and Gröbner basis calculations required to identify the two function applications.
However the `cutsat` algorithm by itself can't do anything with `max 3 (4 * x) ≠ 2 + x`.
Next, instantiating {lean}`Nat.max_def` (automatically, because of an annotation in the standard library) which states `max n m = if n ≤ m then m else n`,
we then case split on the inequality.
In the branch `3 ≤ 4 * x`, cutsat again uses modularity to prove `4 * x ≠ 2 + x`.
In the branch `4 * x < 3`, cutsat quickly determines `x = 0`, and then notices `4 * 0 ≠ 2 + 0`.

This has been, of course, a quite artificial example! In practice this sort of automatic integration of different reasoning modes is very powerful:
the central "whiteboard" which tracks instantiated theorems and equivalence classes can hand off relevant terms and equalities to the appropriate modules (here, `cutsat` and Gröbner bases),
which can then return new facts to the whiteboard.

## if-then-else normalization

```lean (show := false)
open Std
```

:::comment
FIXME (@david-christiansen): I'd like to be able to write ``{attr}`@[grind]` ``.
:::

This example is a showcase for the "out of the box" power of {tactic}`grind`.
Later examples will explore adding `@[grind]` annotations as part of the development process, to make {tactic}`grind` more effective in a new domain.
This example does not rely on any of the algebra extensions to `grind`, we're just using:
* instantiation of annotated theorems from the library,
* congruence closure, and
* case splitting.

The solution here builds on an earlier formalization by Chris Hughes, but with some notable improvements:
* the verification is separate from the code,
* the proof is now a one-liner combining {tactic}`fun_induction` and {tactic}`grind`,
* the proof is robust to changes in the code (e.g. swapping out {name}`HashMap` for {name}`TreeMap`) as well as changes to the precise verification conditions.


### The problem

Here is Rustan Leino's original description of the problem, as [posted by Leonardo de Moura](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rustan's.20challenge) on the Lean Zulip:

> The data structure is an expression with Boolean literals, variables, and if-then-else expressions.
>
> The goal is to normalize such expressions into a form where:
> a) No nested ifs: the condition part of an if-expression is not itself an if-expression
> b) No constant tests: the condition part of an if-expression is not a constant
> c) No redundant ifs: the then and else branches of an if are not the same
> d) Each variable is evaluated at most once: the free variables of the condition are disjoint from those in the then branch, and also disjoint from those in the else branch.
>
> One should show that a normalization function produces an expression satisfying these four conditions, and one should also prove that the normalization function preserves the meaning of the given expression.

### The formal statement

:::comment
FIXME: @david-christiansen: can I give `IfExpr` a hover/linkify even though it is a forward reference? Similarly `eval` below?
:::

To formalize the statement in Lean, we use an inductive type `IfExpr`:

```lean
/-- An if-expression is either boolean literal,
a numbered variable, or an if-then-else expression
where each subexpression is an if-expression. -/
inductive IfExpr
  | lit : Bool → IfExpr
  | var : Nat → IfExpr
  | ite : IfExpr → IfExpr → IfExpr → IfExpr
deriving DecidableEq
```

and define some inductive predicates and an `eval` function, so we can state the four desired properties:

```lean
namespace IfExpr

/--
An if-expression has a "nested if" if it contains
an if-then-else where the "if" is itself an if-then-else.
-/
def hasNestedIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (ite _ _ _) _ _ => true
  | ite _ t e => t.hasNestedIf || e.hasNestedIf

/--
An if-expression has a "constant if" if it contains
an if-then-else where the "if" is itself a literal.
-/
def hasConstantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (lit _) _ _ => true
  | ite i t e =>
    i.hasConstantIf || t.hasConstantIf || e.hasConstantIf

/--
An if-expression has a "redundant if" if
it contains an if-then-else where
the "then" and "else" clauses are identical.
-/
def hasRedundantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite i t e => t == e || i.hasRedundantIf ||
      t.hasRedundantIf || e.hasRedundantIf

/--
All the variables appearing in an if-expressions,
read left to right, without removing duplicates.
-/
def vars : IfExpr → List Nat
  | lit _ => []
  | var i => [i]
  | ite i t e => i.vars ++ t.vars ++ e.vars

/--
A helper function to specify that two lists are disjoint.
-/
def _root_.List.disjoint {α} [DecidableEq α] :
    List α → List α → Bool
  | [], _ => true
  | x::xs, ys => x ∉ ys && xs.disjoint ys

/--
An if expression evaluates each variable at most once if
for each if-then-else the variables in the "if" clause
are disjoint from the variables in the "then" clause
and the variables in the "if" clause
are disjoint from the variables in the "else" clause.
-/
def disjoint : IfExpr → Bool
  | lit _ => true
  | var _ => true
  | ite i t e =>
      i.vars.disjoint t.vars && i.vars.disjoint e.vars &&
        i.disjoint && t.disjoint && e.disjoint

/--
An if expression is "normalized" if it has
no nested, constant, or redundant ifs,
and it evaluates each variable at most once.
-/
def normalized (e : IfExpr) : Bool :=
  !e.hasNestedIf && !e.hasConstantIf &&
    !e.hasRedundantIf && e.disjoint

/--
The evaluation of an if expression
at some assignment of variables.
-/
def eval (f : Nat → Bool) : IfExpr → Bool
  | lit b => b
  | var i => f i
  | ite i t e => bif i.eval f then t.eval f else e.eval f

end IfExpr
```


Using these we can state the problem. The challenge is to inhabit the following type (and to do so nicely!):

:::comment
FIXME (@david-christiansen): No long line warning here?
:::
```lean
def IfNormalization : Type :=
  { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }
```

### Other solutions

At this point, it's worth pausing and doing at least one of the following:

:::comment
TODO (@david-christiansen): We include a link here to live-lean and an externally hosted blob of code. There's no way to keep this in sync. :-(
:::

* Try to prove this yourself! It's quite challenging for a beginner!
  You can [have a go](https://live.lean-lang.org/#project=lean-nightly&url=https%3A%2F%2Fgist.githubusercontent.com%2Fkim-em%2Ff416b31fe29de8a3f1b2b3a84e0f1793%2Fraw%2F75ca61230b50c126f8658bacd933ecf7bfcaa4b8%2Fgrind_ite.lean)
  in the Live Lean editor without any installation.
* Read Chris Hughes's [solution](https://github.com/leanprover-community/mathlib4/blob/master/Archive/Examples/IfNormalization/Result.lean),
  which is included in the Mathlib Archive.
  This solution makes good use of Aesop, but is not ideal because
  1. It defines the solution using a subtype, simultaneously giving the construction and proving properties about it.
     We think it's better stylistically to keep these separate.
  2. Even with Aesop automation, there's still about 15 lines of manual proof work before we can hand off to Aesop.
* Read Wojciech Nawrocki's [solution](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Rustan's.20challenge/near/398824748).
  This one uses less automation, at about 300 lines of proof work.

### The solution using {tactic}`grind`

Actually solving the problem is not that hard:
we just need a recursive function that carries along a record of "already assigned variables",
and then, whenever performing a branch on a variable, adding a new assignment in each of the branches.
It also needs to flatten nested if-then-else expressions which have another if-then-else in the "condition" position.
(This is extracted from Chris Hughes's solution, but without the subtyping.)

:::comment
FIXME: @david-christiansen: the long line linter complains in the next code block, but I can't wrap the options.
:::

Let's work inside the `IfExpr` namespace.
```lean
namespace IfExpr
```

```lean (error := true) (name := failed_to_show_termination) (keep := false)
def normalize (assign : Std.HashMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
```

This is pretty straightforward, but it immediately runs into a problem:

:::comment
This output is extremely fragile, because it includes line numbers.
I would like to stop at "Could not find a decreasing measure."
but for this we need support for showing subsets of the output.
:::
```leanOutput failed_to_show_termination
fail to show termination for
  IfExpr.normalize
with errors
failed to infer structural recursion:
Cannot use parameter assign:
  the type HashMap Nat Bool does not have a `.brecOn` recursor
Cannot use parameter #2:
  failed to eliminate recursive application
    normalize assign (a.ite (b.ite t e) (c.ite t e))


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
              #1 x2
1) 1296:27-45  =  <
2) 1297:27-45  =  <
3) 1299:4-52   =  ?
4) 1303:16-50  ?  _
5) 1304:16-51  _  _
6) 1306:16-50  _  _

#1: assign

Please use `termination_by` to specify a decreasing measure.
```


Lean here is telling us that it can't see that the function is terminating.
Often Lean is pretty good at working this out for itself, but for sufficiently complicated functions
we need to step in to give it a hint.

In this case we can see that it's the recursive call
`ite (ite a b c) t e` which is calling {lean}`normalize` on `(ite a (ite b t e) (ite c t e))`
where Lean is having difficulty. Lean has made a guess at a plausible termination measure,
based on using automatically generated `sizeOf` function, but can't prove the resulting goal,
essentially because `t` and `e` appear multiple times in the recursive call.

To address problems like this, we nearly always want to stop using the automatically generated `sizeOf` function,
and construct our own termination measure. We'll use

```lean
@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1
```


Many different functions would work here. The basic idea is to increase the "weight" of the "condition" branch
(this is the multiplicative factor in the `2 * normSize i` ),
so that as long the "condition" part shrinks a bit, the whole expression counts as shrinking even if the "then" and "else" branches have grown.
We've annotated the definition with `@[simp]` so Lean's automated termination checker is allowed to unfold the definition.

With this in place, the definition goes through using the {keywordOf Lean.Parser.Command.declaration}`termination_by` clause:

:::keepEnv
```lean
def normalize (assign : Std.HashMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
termination_by e => e.normSize
```

Now it's time to prove some properties of this function.
We're just going to package together all the properties we want:

```lean (keep := false)
theorem normalize_spec
    (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign :=
  sorry
```

That is:
* the result of {lean}`normalize` is actually normalized according to the initial definitions,
* if we normalize an "if-then-else" expression using some assignments, and then evaluate the remaining variables,
  we get the same result as evaluating the original "if-then-else" using the composite of the two assignments,
* and any variable appearing in the assignments no longer appears in the normalized expression.

You might think that we should state these three properties as separate lemmas,
but it turns out that proving them all at once is really convenient, because we can use the {tactic}`fun_induction`
tactic to assume that all these properties hold for {lean}`normalize` in the recursive calls, and then
{tactic}`grind` will just put all the facts together for the result:

```lean
-- We tell `grind` to unfold our definitions above.
attribute [local grind]
  normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars eval List.disjoint

theorem normalize_spec
    (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind
```

The fact that the {tactic}`fun_induction` plus {tactic}`grind` combination just works here is sort of astonishing.
We're really excited about this, and we're hoping to see a lot more proofs in this style!

A lovely consequence of highly automated proofs is that often you have some flexibility to change the statements,
without changing the proof at all! As examples, the particular way that we asserted above that
"any variable appearing in the assignments no longer appears in the normalized expression"
could be stated in many different ways (although not omitted!). The variations really don't matter,
and {tactic}`grind` can both prove, and use, any of them:

Here we use `assign.contains v = false`:
```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat), v ∈ vars (normalize assign e) →
          assign.contains v = false := by
  fun_induction normalize with grind
```

and here we use `assign[v]? = none`:

```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → assign[v]? = none := by
  fun_induction normalize with grind
```

In fact, it's also of no consequence to `grind` whether we use a
{name}`HashMap` or a {name}`TreeMap` to store the assignments,
we can simply switch that implementation detail out, without having to touch the proofs:

:::


```lean (show := false)
-- We have to repeat these annotations because we've rolled back the environment to before we defined `normalize`.
attribute [local grind]
  normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars eval List.disjoint
```
```lean
def normalize (assign : Std.TreeMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
termination_by e => e.normSize

theorem normalize_spec
    (assign : Std.TreeMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind
```

(The fact that we can do this relies on the fact that all the lemmas for both `HashMap` and for `TreeMap` that `grind` needs have already be annotated in the standard library.)

If you'd like to play around with this code,
you can find the whole file [here](https://github.com/leanprover/lean4/blob/master/tests/lean/run/grind_ite.lean),
or in fact [play with it with no installation](https://live.lean-lang.org/#project=lean-nightly&url=https%3A%2F%2Fraw.githubusercontent.com%2Fleanprover%2Flean4%2Frefs%2Fheads%2Fmaster%2Ftests%2Flean%2Frun%2Fgrind_ite.lean)
in the Live Lean editor.

```lean (show := false)
end IfExpr
```

##  `IndexMap`

In this section we'll build an example of a new data structure and basic API for it, illustrating the use of {tactic}`grind`.

The example will be derived from Rust's [`indexmap`](https://docs.rs/indexmap/latest/indexmap/) data structure.

`IndexMap` is intended as a replacement for `HashMap` (in particular, it has fast hash-based lookup), but allowing the user to maintain control of the order of the elements.
We won't give a complete API, just set up some basic functions and theorems about them.

The two main functions we'll implement for now are `insert` and `eraseSwap`:
* `insert k v` checks if `k` is already in the map. If so, it replaces the value with `v`, keeping `k` in the same position in the ordering.
  If it is not already in the map, `insert` adds `(k, v)` to the end of the map.
* `eraseSwap k` removes the element with key `k` from the map, and swaps it with the last element of the map (or does nothing if `k` is not in the map).
  (This semantics is maybe slightly surprising: this function exists because it is an efficient way to erase element, when you don't care about the order of the remaining elements.
  Another function, not implemented here, would preserve the order of the remaining elements, but at the cost of running in time proportional to the number of elements after the erased element.)

Our goals will be:
* complete encapsulation: the implementation of `IndexMap` is hidden from the users, *and* the theorems about the implementation details are private.
* to use `grind` as much as possible: we'll preferring adding a private theorem and annotating it with `@[grind]` over writing a longer proof whenever practical.
* to use auto-parameters as much as possible, so that we don't even see the proofs, as they're mostly handled invisibly by `grind`.

To begin with, we'll write out a skeleton of what we want to achieve, liberally using `sorry` as a placeholder for all proofs.
In particular, this version makes no use of `grind`.

```lean (keep := false)

open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  indices : HashMap α Nat
  keys : Array α
  values : Array β
  size_keys : keys.size = values.size
  WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i

namespace IndexMap

variable {α : Type u} {β : Type v}
  [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity
  size_keys := sorry
  WF := sorry

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

instance :
    GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]'(by sorry)
  getElem? m a :=
    m.indices[a]?.bind (m.values[·]?)
  getElem! m a :=
    m.indices[a]?.bind (m.values[·]?) |>.getD default

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := sorry
  getElem!_def := sorry

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a sorry
      values := m.values.set i b sorry
      size_keys := sorry
      WF := sorry }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b
      size_keys := sorry
      WF := sorry }

instance : Singleton (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) :=
  ⟨fun _ => rfl⟩

/--
Erase the key-value pair with the given key,
moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop
        size_keys := sorry
        WF := sorry }
    else
      let lastKey := m.keys.back sorry
      let lastValue := m.values.back sorry
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey sorry
        values := m.values.pop.set i lastValue sorry
        size_keys := sorry
        WF := sorry }
  | none => m

/-! ### Verification theorems -/

theorem getIdx_findIdx (m : IndexMap α β) (a : α)
    (h : a ∈ m) :
    m.getIdx (m.findIdx a h) sorry = m[a] :=
  sorry

theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  sorry

theorem getElem_insert
    (m : IndexMap α β) (a a' : α) (b : β)
    (h : a' ∈ m.insert a b) :
    (m.insert a b)[a']'h =
      if h' : a' == a then b else m[a']'sorry := by
  sorry

theorem findIdx_insert_self
    (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a sorry =
      if h : a ∈ m then m.findIdx a h else m.size := by
  sorry

end IndexMap
```

::::keepEnv
Let's get started.
We'll aspire to never writing a proof by hand, and the first step of that is to install auto-parameters for the `size_keys` and `WF` field,
so we can omit these fields whenever `grind` can prove them.
While we're modifying the definition of `IndexMap` itself, lets make all the fields private, since we're planning on having complete encapsulation.

```lean
structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind
```


```lean (show := false)
namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}
```

Let's give `grind` access to the definition of `size`, and `size_keys` private field:

```lean
@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

attribute [local grind] size
attribute [local grind _=_] size_keys
```

Our first `sorry`s in the draft version are the `size_keys` and `WF` fields in our construction of `def emptyWithCapacity`.
Surely these are trivial, and solvable by `grind`, so we simply delete those fields:
```lean
def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity
```

```lean (show := false)
instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]
```

Our next task is to deal with the `sorry` in our construction of the `GetElem?` instance:
```lean (keep := false)
instance :
    GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]'(by sorry)
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default
```

The goal at this sorry is
```
m : IndexMap α β
a : α
h : a ∈ m
⊢ m.indices[a] < m.values.size
```

:::comment
FIXME (Q3): @david-christiansen:
We need to keep the goal display above in sync with the `sorry` in the code block before it.
:::

Let's try proving this as a stand-alone theorem, via `grind`, and see where `grind` gets stuck.
Because we've added `grind` annotations for `size` and `size_keys` already, we can safely reformulate the goal as:

```lean (name := getElem_indices_lt_1) (error := true) (keep := false)
theorem getElem_indices_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.indices[a] < m.size := by
  grind
```

This fails, and looking at the message from `grind` we see that it hasn't done much:
:::comment
FIXME (Q3): @david-christiansen:
This needs a mechanism for keeping up to date.
:::
```
[grind] Goal diagnostics ▼
  [facts] Asserted facts ▼
    [prop] a ∈ m
    [prop] m.size ≤ (indices m)[a]
    [prop] m.size = (values m).size
  [eqc] True propositions ▼
    [prop] m.size ≤ (indices m)[a]
    [prop] a ∈ m
  [eqc] Equivalence classes ▼
    [] {Membership.mem, fun m a => a ∈ m}
    [] {m.size, (values m).size}
  [ematch] E-matching patterns ▼
    [thm] size.eq_1: [@size #4 #3 #2 #1 #0]
    [thm] HashMap.contains_iff_mem: [@Membership.mem #5 (HashMap _ #4 #3 #2) _ #1 #0]
  [cutsat] Assignment satisfying linear constraints ▼
    [assign] m.size := 0
    [assign] (indices m)[a] := 0
    [assign] (values m).size := 0
```

An immediate problem we can see here is that
`grind` does not yet know that `a ∈ m` is the same as `a ∈ m.indices`.
Let's add this fact:

```lean
@[local grind] private theorem mem_indices_of_mem
    {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices :=
  Iff.rfl
```

However this proof is going to work, we know the following:
* It must use the well-formedness condition of the map.
* It can't do so without relating `m.indices[a]` and `m.indices[a]?` (because the later is what appears in the well-formedness condition).
* The expected relationship there doesn't even hold unless the map `m.indices` satisfies {lean}`LawfulGetElem`,
  for which we need `[LawfulBEq α]` and `[LawfulHashable α]`.

:::comment
TODO: I'd like to ensure there's a link to the `LawfulGetElem` instance for `HashMap`, so we can see these requirements!
:::

Let's configure things so that those are available:

```lean
variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF
```

and then give `grind` one manual hint, to relate `m.indices[a]` and `m.indices[a]?`:

```lean (name := getElem_indices_lt_2)
theorem getElem_indices_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind
```

With that theorem proved, we want to make it accessible to `grind`.
We could either add `@[local grind]` before the theorem statement,
or write `attribute [local grind] getElem_indices_lt` after the theorem statement.
These will use `grind` built-in heuristics for deciding a pattern to match the theorem on.

In this case, let's use the `grind?` attribute to see the pattern that is being generated:
```lean (name := grind?) (keep := false)
attribute [local grind?] getElem_indices_lt
```
```leanOutput grind? (whitespace := lax)
getElem_indices_lt:
  [@LE.le `[Nat] `[instLENat]
    ((@getElem (HashMap #8 `[Nat] #6 #5) _ `[Nat] _ _
      (@indices _ #7 _ _ #2) #1 #0) + 1)
    (@size _ _ _ _ #2)]
```
This is not a useful pattern: it's matching on the entire conclusion of the theorem
(in fact, a normalized version of it, in which `x < y` has been replaced by `x + 1 ≤ y`).

We want something more general: we'd like this theorem to fire whenever `grind` sees `m.indices[a]`,
and so instead of using the attribute we write a custom pattern:

```lean
grind_pattern getElem_indices_lt => m.indices[a]
```

The Lean standard library uses the `get_elem_tactic` tactic as an auto-parameter for the `xs[i]` notation
(which desugars to `GetElem.getElem xs i h`, with the proof `h` generated by `get_elem_tactic`).
We'd like to not only have `grind` fill in these proofs, but even to be able to omit these proofs.
To achieve this, we add the line
```lean (show := false)
-- This block is just here as a guard: when/if the global `get_elem_tactic` uses grind, this will fail,
-- prompting us to update the sentence about "later versions of Lean" below.
example (m : HashMap Nat Nat) : (m.insert 1 2).size ≤ m.size + 1 := by
  fail_if_success get_elem_tactic
  sorry
```
```lean
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)
```
```lean (show := false)
example (m : HashMap Nat Nat) : (m.insert 1 2).size ≤ m.size + 1 := by get_elem_tactic
```
(In later versions of Lean this may be part of the built-in behavior.)

We can now return to constructing our `GetElem?` instance, and simply write:
```lean
instance :
    GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default
```
with neither any `sorry`s, nor any explicitly written proofs.

Next, we want to expose the content of these definitions, but only locally in this file:
```lean
@[local grind] private theorem getElem_def
    (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m[a] = m.values[m.indices[a]'h] :=
  rfl
@[local grind] private theorem getElem?_def
    (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) :=
  rfl
@[local grind] private theorem getElem!_def
    [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (m.values[·]?)).getD default :=
  rfl
```

Again we're using the `@[local grind] private theorem` pattern to hide these implementation details,
but allow `grind` to see these facts locally.

Next, we want to prove the `LawfulGetElem` instance, and hope that `grind` can fill in the proofs:
```lean
instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind
```

Success!

Let's press onward, and see if we can define `insert` without having to write any proofs:
```lean

@[inline] def insert [LawfulBEq α] (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a
      values := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b }
```
In both branches, `grind` is automatically proving both the `size_keys` and `WF` fields!
Note also in the first branch the `set` calls `m.keys.set i a` and `m.values.set i b`
are having there "in-bounds" obligations automatically filled in by `grind` via the `get_elem_tactic` auto-parameter.

Next let's try `eraseSwap`:
```lean (name := eraseSwap_1) (error := true) (keep := false)
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m
```
This fails while attempting to prove the `WF` field in the second branch.
As usual, there is detailed information from `grind` about its failure state, but almost too much to be helpful!
Let's look at the model produced by `cutsat` and see if we can see what's going on:
```
[cutsat] Assignment satisfying linear constraints ▼
  [assign] i_1 := 0
  [assign] i_2 := 1
  [assign] (keys m_1).pop.size := 2
  [assign] (keys m_1).size := 3
  [assign] m_1.size := 3
  [assign] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size := 2
  [assign] (values m_1).size := 3
  [assign] (indices m_1)[a_1] := 0
  [assign] (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2] := 0
  [assign] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop.size := 2
  [assign] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size := 3
  [assign] (indices m_1)[a_1] := 0
  [assign] (indices m_1)[a_2] := 1
  [assign] (indices m_1)[(keys m_1)[i_2]] := 1
  [assign] (indices m_1)[(keys m_1)[i_2]] := 1
```
:::comment
FIXME (@kim-em / @leodemoura): there is some repeated output here.
:::

This model consists of an `IndexMap` of size `3`,
with keys `a_1`, `a_2` and the otherwise unnamed `(keys m_1).back ⋯`.

Everything looks fine, *except* the line:
```
(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2] := 0
```
This shouldn't be possible! Since the three keys are distinct,
we should have
```
(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2] =
  ((indices m_1).erase a_1)[a_2] =
  (indices m_1)[a_2] =
  1
```
Now that we've found something suspicious, we can look through the equivalence classes identified by `grind`.
(In the future we'll be providing search tools for inspecting equivalence classes, but for now you need to read through manually.)
We find amongst many others:
```
{a_2,
  (keys m_1).back ⋯,
  (keys m_1)[(keys m_1).size - 1],
  (keys m_1)[i_2], ...}
```
This should imply, by the injectivity of `keys`, that `i_2 = (keys m_1).size - 1`.
Since this identity *wasn't* reflected by the cutsat model,
we suspect that `grind` is not managing to use the injectivity of `keys`.

Thinking about the way that we've provided the well-formedness condition, as
`∀ (i : Nat) (a : α), keys[i]? = some a ↔ indices[a]? = some i`, this perhaps isn't surprising:
it's expressed in terms of `keys[i]?` and `indices[a]?`.
Let's add a variant version of the well-formedness condition using `getElem` instead of `getElem?`:

```lean
@[local grind] private theorem WF'
    (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind
```
We can verify that with this available, `grind` can now prove:
```lean
example {m : IndexMap α β} {a : α} {h : a ∈ m} :
  m.keys[m.indices[a]'h] = a := by grind
```

Trying again with `eraseSwap`, everything goes through cleanly now, with no manual proofs:
```lean
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m
```

Finally we turn to the verification theorems about the basic operations, relating `getIdx`, `findIdx`, and `insert`.
By adding a `local grind` annotation allowing `grind` to unfold the definitions of these operations,
the proofs all go through effortlessly:

```
/-! ### Verification theorems -/

attribute [local grind] getIdx findIdx insert

@[grind] theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind

@[grind] theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind

@[grind] theorem getElem_insert
    (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind

@[grind] theorem findIdx_insert_self
    (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a =
      if h : a ∈ m then m.findIdx a else m.size := by
  grind
```

Note that these are part of the public API of `IndexMap`, so we need to mark them as `@[grind]`,
so that users without our internal `local grind` annotations can still use them in `grind` proofs.

::::

Putting this all together, our prototype API has reached the following state:

```lean
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size :=
  m.size_keys'

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[local grind] private theorem mem_indices_of_mem
    {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices := Iff.rfl

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α)
    (h : a ∈ m := by get_elem_tactic) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF

private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind

grind_pattern getElem_indices_lt => m.indices[a]

attribute [local grind] size

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

@[local grind] private theorem getElem_def
    (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m[a] = m.values[m.indices[a]'h] :=
  rfl
@[local grind] private theorem getElem?_def
    (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) :=
  rfl
@[local grind] private theorem getElem!_def
    [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (m.values[·]?)).getD default :=
  rfl

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind

@[inline] def insert [LawfulBEq α] (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a
      values := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b }

instance [LawfulBEq α] : Singleton (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance [LawfulBEq α] : Insert (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance [LawfulBEq α] : LawfulSingleton (α × β) (IndexMap α β) :=
    ⟨fun _ => rfl⟩

@[local grind] private theorem WF'
    (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind

/--
Erase the key-value pair with the given key,
moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m

/-! ### Verification theorems -/

attribute [local grind] getIdx findIdx insert

@[grind] theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind

@[grind] theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind

@[grind] theorem getElem_insert
    (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind

@[grind] theorem findIdx_insert_self
    (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a =
      if h : a ∈ m then m.findIdx a else m.size := by
  grind

end IndexMap
```

We haven't yet proved all the theorems we would want about these operations (or indeed any theorems about `eraseSwap`); the interested reader is encouraged to try proving more,
and perhaps even releasing a complete `IndexMap` library!

Summarizing the design principles discussed above about encapsulation:
* the fields of `IndexMap` are all private, as these are implementation details.
* the theorems about these fields are all private, and marked as `@[local grind]`, rather than `@[grind]`, as they won't be needed after we've set up the API.
* the verification theorems are both marked as `@[grind]`, and proved by `grind`:
  the annotation is necessary because we want grind to be able to prove these facts even once we're outside the current module, and the `@[local grind]` theorems are no longer available.
