/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

-- Needed for the if-then-else normalization example.
import Std.Data.TreeMap

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

-- The verso default max line length is 60, which is very restrictive.
-- Currently we satisfy it, but you can increase it here if it becomes annoying.
-- TODO: discuss with David.
set_option verso.code.warnLineLength 60

#doc (Manual) "The `grind` tactic" =>
%%%
tag := "grind"
%%%

-- TODO: remove this code block once the warning is removed.
```lean (show := false)
set_option grind.warning false
```
-- Open some namespaces for the examples.
```lean (show := false)
open Lean Lean.Grind Lean.Meta.Grind
```

# Quick Start

* **Availability** – {tactic}`grind` ships with Lean 4 (no extra installation) and is usable in any Lean file—just write `by grind`. No extra `import` is required beyond what your own definitions already need.

* **Library support** – Lean’s standard library is already annotated with `[grind]` attributes, so common lemmas are discovered automatically. Mathlib will be annotated gradually, starting with its most frequently used theories.

* **First proof**

```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  grind
```

This succeeds instantly using congruence closure.

* **Power examples** – showcasing {tactic}`grind`'s satellite solvers:

  * *Algebraic reasoning* (commutative‑ring solver):

    ```lean
    example [CommRing α] [NoNatZeroDivisors α] (a b c : α)
        : a + b + c = 3 →
          a^2 + b^2 + c^2 = 5 →
          a^3 + b^3 + c^3 = 7 →
          a^4 + b^4 = 9 - c^4 := by
      grind +ring
    ```

  * *Finite‑field style reasoning* (works in {lean}`Fin 11`):

    ```lean
    example (x y : Fin 11) :
        x^2*y = 1 → x*y^2 = y → y*x = 1 := by
      grind +ring
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

* **Useful flags**

  * `by grind (splits := 3) (ematch := 2)` – limit case splits / E‑matching rounds.

# What is {tactic}`grind`?

A proof‑automation tactic inspired by modern SMT solvers. **Picture a virtual white‑board:** every time {tactic}`grind` discovers a new equality, inequality, or Boolean literal it writes that fact on the board, merges equivalent terms into buckets, and invites each engine to read from—and add back to—the same workspace. The cooperating engines are: congruence closure, constraint propagation, E‑matching, guided case analysis, and a suite of satellite theory solvers (linear integer arithmetic, commutative rings, …). Lean supports dependent types and a powerful type‑class system, and {tactic}`grind` produces ordinary Lean proof terms for every fact it adds.

# What {tactic}`grind` is *not*.

{tactic}`grind` is *not* designed for goals whose search space explodes combinatorially—think large‑`n` pigeonhole instances, graph‑coloring reductions, high‑order N‑queens boards, or a 200‑variable Sudoku encoded as Boolean constraints.  Such encodings require thousands (or millions) of case‑splits that overwhelm {tactic}`grind`’s branching search.

* **Bit‑level or pure Boolean combinatorial problems** → use **{tactic}`bv_decide`**.
  {tactic}`bv_decide` calls a state‑of‑the‑art SAT solver (e.g. CaDiCaL or Kissat) and then returns a *compact, machine‑checkable certificate*.  All heavy search happens outside Lean; the certificate is replayed and verified inside Lean, so trust is preserved (verification time scales with certificate size).
* **Full SMT problems that need substantial case analysis across multiple theories** (arrays, bit‑vectors, rich arithmetic, quantifiers, …) → use the forthcoming **`lean‑smt`** tactic—a tight Lean front‑end for CVC5 that replays unsat cores or models inside Lean.

# Congruence Closure

## What is congruence closure?

Congruence closure maintains **equivalence classes of terms** under the reflexive–symmetric–transitive closure of "is equal to" *and* the rule that equal arguments yield equal function results.  Formally, if `a = a'` and `b = b'`, then `f a b = f a' b'` is added.  The algorithm merges classes until a fixed point is reached.

Think of a **shared white‑board**:

1. Every hypothesis `h : t₁ = t₂` writes a line connecting `t₁` and `t₂`.
2. Each merge paints both terms the same color.  Soon whole constellations (`f a`, `g (f a)`, …) share the color.
3. If {lean}`True` and {lean}`False` ever land in the same color—or likewise two different constructors of the **same inductive type** such as {lean}`none` and {lean}`some 1`—the goal is closed by contradiction.

## How it differs from {tactic}`simp`

* {tactic}`simp` **rewrites** a goal, replacing occurrences of `t₁` with `t₂` as soon as it sees `h : t₁ = t₂`.  The rewrite is directional and destructive.
* {tactic}`grind` **accumulates** equalities bidirectionally.  No term is rewritten; instead, both representatives live in the same class.  All other engines (E‑matching, theory solvers, propagation) can query these classes and add new facts, then the closure updates incrementally.

This makes congruence closure especially robust in the presence of symmetrical reasoning, mutual recursion, and large nestings of constructors where rewriting would duplicate work.

## Minimal examples

```lean
example {α} (f g : α → α) (x y : α)
    (h₁ : x = y) (h₂ : f y = g y) :
    f x = g x := by
  -- After h₁, x and y share a class,
  -- h₂ adds f y = g y, and
  -- closure bridges to f x = g x
  grind

example (a b c : Nat) (h : a = b) : (a, c) = (b, c) := by
  -- Pair constructor obeys congruence,
  -- so once a = b the tuples are equal
  grind
```

# Debugging tip

When {tactic}`grind` *fails* it prints the remaining subgoal **followed by all equivalence classes**.  The two largest classes are shown as **True propositions** and **False propositions**, listing every literal currently known to be provable or refutable.  Inspect these lists to spot missing facts or contradictory assumptions.

# Constraint Propagation

Constraint propagation works on the **True** and **False** buckets of the white‑board.  Whenever a literal is added to one of those buckets, {tactic}`grind` fires dozens of small *forward rules* to push its logical consequences:

* Boolean connectives — e.g. if `A` is **True**, mark `A ∨ B` **True**; if `A ∧ B` is **True**, mark both `A` and `B` **True**; if `A ∧ B` is **False**, at least one of `A`, `B` becomes **False**.
* Inductive datatypes — two different constructors (`none` vs `some _`) collapsing into the same class yield contradiction; equal tuples yield equal components.
* Projections and casts — from `h : (x, y) = (x', y')` we derive `x = x'` and `y = y'`; any term `cast h a` is merged with `a` immediately (using a heterogeneous equality) so both live in the same class.
* Structural eta and definitional equalities — `⟨a, b⟩.1` propagates to `a`, etc.

Below is a **representative slice** of the propagators so you can see the style they follow.  Each follows the same skeleton: inspect the truth‑value of sub‑expressions, push equalities ({lean}`pushEq`) or truth‑values ({lean}`pushEqTrue` / {lean}`pushEqFalse`), and optionally close the goal if a contradiction ({lean}`closeGoal`) arises.  A few high‑signal examples:

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

-- TODO (@kim-em): we don't add the `{lean}` literal type to `propagateEtaStruct` above because it is private.

Many specialised variants for {lean}`Bool` mirror these rules exactly (e.g. {lean}`propagateBoolAndUp`).

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

These snippets run instantly because the relevant propagators ({lean}`propagateBoolAndUp`, {lean}`propagateIte`, {lean}`propagateBoolNotDown`) fire as soon as the hypotheses are internalised.

> **Note** If you toggle `set_option trace.grind.eqc true`, {tactic}`grind` will print a line every time two equivalence classes merge—handy for seeing propagation in action.

**Implementation tip**  {tactic}`grind` is still under active development. Until the API has stabilised we recommend **refraining from custom elaborators or satellite solvers**. If you really need a project‑local propagator, use the user‑facing `grind_propagator` command rather than `builtin_grind_propagator` (the latter is reserved for Lean’s own code). When adding new propagators keep them *small and orthogonal*—they should fire in ≤1 µs and either push one fact or close the goal. This keeps the propagation phase predictable and easy to debug.

We continuously expand and refine the rule set—expect the **Info View** to show increasingly rich {lean}`True`/{lean}`False` buckets over time. The full equivalence classes are displayed automatically **only when {tactic}`grind` fails**, and only for the first subgoal it could not close—use this output to inspect missing facts and understand why the subgoal remains open.

# Case Analysis

## Selection heuristics

{tactic}`grind` decides which sub‑term to split on by combining three sources of signal:

1. **Structural flags** — quick booleans that enable whole syntactic classes:

   * `splitIte` (default **true**) → split every `if … then … else …` term.
   * `splitMatch` (default **true**)→ split on all `match` expressions (the {tactic}`grind` analogue of Lean’s {tactic}`split` tactic, just like `splitIte`).
   * `splitImp` (default **false**) → when {lean}`true` splits on any hypothesis `A → B` whose antecedent `A` is **propositional**.  Arithmetic antecedents are special‑cased: if `A` is an arithmetic literal (`≤`, `=`, `¬`, `Dvd`, …) {tactic}`grind` will split **even when `splitImp := false`** so the integer solver can propagate facts.

👉 Shorthand toggles: `by grind -splitIte +splitImp` expands to `by grind (splitIte := false) (splitImp := true)`.
2. **Global limit** — `splits := n` caps the *depth* of the search tree.  Once a branch performs `n` splits {tactic}`grind` stops splitting further in that branch; if the branch cannot be closed it reports that the split threshold has been reached.
3. **Manual annotations** — you may mark *any* inductive predicate or structure with

-- Note this *not* a lean code block, because `Even` and `Sorted` do not exist.
-- TODO: replace this with a checkable example.
```
attribute [grind cases] Even Sorted
```

and {tactic}`grind` will treat every instance of that predicate as a split candidate.

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
example (h : f b = a) : g a = b := by
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

example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
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

You can also specify a **multi-pattern** to control when `grind` should instantiate a theorem.
A multi-pattern requires that all specified patterns are matched in the current context
before the theorem is instantiated. This is useful for lemmas such as transitivity rules,
where multiple premises must be simultaneously present for the rule to apply.
The following example demonstrates this feature using a transitivity axiom for a binary relation `R`:
```lean
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z

grind_pattern Rtrans => R x y, R y z

example : R a b → R b c → R c d → R a d := by
  grind
```
By specifying the multi-pattern `R x y, R y z`, we instruct `grind` to
instantiate `Rtrans` only when both `R x y` and `R y z` are available in the context.
In the example, `grind` applies `Rtrans` to derive `R a c` from `R a b` and `R b c`,
and can then repeat the same reasoning to deduce `R a d` from `R a c` and `R c d`.




TBD
Pattern annotations (`[grind =]`, `[grind →]`, …), anti‑patterns, local vs global attributes, debugging with the attribute `[grind?]`. Flags: `ematch`, `instances`, `matchEqs`.

# Linear Integer Arithmetic Solver
TBD
Model‑building CutSAT‑style procedure, model‑based theory combination. Flags: `+qlia`, `-mbtc`.

# Algebraic Solver (Commutative Rings, Fields)
TBD
Grobner‑style basis construction, class parameters ({lean}`IsCharP`, {lean}`NoNatZeroDivisors`), step budget `algSteps`.

# Normalizer / Pre‑processor
TBD
Canonicalization pass; extending with `[grind norm]` (expert only).

# Diagnostics
TBD
Threshold notices, learned equivalence classes, integer assignments, algebraic basis, performed splits, instance statistics.

# Troubleshooting & FAQ
TBD

# Bigger Examples

## if-then-else normalization

FIXME (@kim-em / @leodemoura): The language in this section is chatty, because it started life as a blog post. Should I rewrite?

FIXME (@david-christiansen): I can't use `leanSection` with section titles inside?
-- ::::: leanSection

```lean (show := false)
open Std
```

FIXME (@david-christiansen): I'd like to be able to write ``{attr}`@[grind]` ``.

This example is a showcase for the "out of the box" power of {tactic}`grind`.
Later examples will explore adding `@[grind]` annotations as part of the development process, to make {tactic}`grind` more effective in a new domain.

The solution here builds on an earlier formalization by Chris Hughes, but with some notable improvements:
* the verification is separate from the code,
* the proof is now a one-liner combining {tactic}`fun_induction` and {tactic}`grind`,
* the proof is robust to changes in the code (e.g. swapping out {name}`HashMap` for {name}`TreeMap`) as well as changes to the precise verification conditions.


### The problem

Here is Rustan Leino's original description of the problem, as [posted by Leo](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rustan's.20challenge) on the Lean Zulip:

> The data structure is an expression with boolean literals, variables, and if-then-else expressions.
>
> The goal is to normalize such expressions into a form where:
> a) No nested ifs: the condition part of an if-expression is not itself an if-expression
> b) No constant tests: the condition part of an if-expression is not a constant
> c) No redundant ifs: the then and else branches of an if are not the same
> d) Each variable is evaluated at most once: the free variables of the condition are disjoint from those in the then branch, and also disjoint from those in the else branch.
>
> One should show that a normalization function produces an expression satisfying these four conditions, and one should also prove that the normalization function preserves the meaning of the given expression.

### The formal statement

FIXME: @david-christiansen: can I give `IfExpr` a hover/linkify even though it is a forward reference? Similarly `eval` below?

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

```lean
namespace IfExpr

def IfNormalization : Type := { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }
```

### Other solutions

At this point, it's worth pausing and doing at least one of the following:

* Try to prove this yourself! It's quite challenging for a beginner!
  You can [have a go](https://live.lean-lang.org/#project=lean-nightly&url=https://gist.github.com/kim-em/f416b31fe29de8a3f1b2b3a84e0f1793)
  in the Live Lean editor without any installation.
  FIXME (@kim-em / @david-christiansen): work out how to make this a more durable link.
* Read Chris Hughes's [solution](https://github.com/leanprover-community/mathlib4/blob/master/Archive/Examples/IfNormalization/Result.lean),
  which is included in the Mathlib Archive.
  This solution makes good use of Aesop, but is not ideal because
  1. It defines the solution using a subtype, simultaneously giving the construction and proving properties about it.
     We think it's better stylistically to keep these separate.
  2. Even with Aesop automation, there's still about 15 lines of manual proof work before we can hand off to Aesop.
* Read Wojciech Nawrocki's [solution](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Rustan's.20challenge/near/398824748).
  This one uses less automation, at about 300 lines of proof work.

# The solution using {tactic}`grind`

Actually solving the problem is not that hard:
we just need a recursive function that carries along a record of "already assigned variables",
and then, whenever performing a branch on a variable, adding a new assignment in each of the branches.
It also needs to flatten nested if-then-else expressions which have another if-then-else in the "condition" position.
(This is extracted from Chris Hughes's solution, but without the subtyping.)

FIXME: @david-christiansen: the long line linter complains in the next code block, but I can't wrap the options.

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


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
assign : HashMap Nat Bool
a b c t e : IfExpr
⊢ 1 + sizeOf a + (1 + sizeOf b + sizeOf t + sizeOf e) + (1 + sizeOf c + sizeOf t + sizeOf e) <
    1 + (1 + sizeOf a + sizeOf b + sizeOf c) + sizeOf t + sizeOf e
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
  fun_induction normalize with grind (gen := 7)
```

FIXME (@kim-em): increase the `gen` default to at least 8.

The fact that the {tactic}`fun_induction` plus {tactic}`grind` combination just works here is sort of astonishing.
We're really excited about this, and we're hoping to see a lot more proofs in this style!

A lovely consequence of highly automated proofs is that often you have some flexibility to change the statements,
without changing the proof at all! As examples, the particular way that we asserted above that
"any variable appearing in the assignments no longer appears in the normalized expression"
could be stated in many different ways (although not omitted!). The variations really don't matter,
and {tactic}`grind` can both prove, and use, any of them:

```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → assign.contains v = false := by
  fun_induction normalize with grind (gen := 7)

example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → assign[v]? = none := by
  fun_induction normalize with grind (gen := 8)
```

In fact, it's also of no consequence to `grind` whether we use a
{name}`HashMap` or a {name}`TreeMap` to store the assignments,
we can simply switch that implementation detail out, without having to touch the proofs:

FIXME: @david-christiansen: I want to "roll-back" the Lean state to what it was before we gave the first definition of `normalize`.

```lean (error := true)
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
  fun_induction normalize with grind (gen := 7)
```

If you'd like to play around with this code,
you can find the whole file [here](https://github.com/leanprover/lean4/blob/master/tests/lean/run/grind_ite.lean),
or in fact [play with it with no installation](https://live.lean-lang.org/#project=lean-nightly&url=https%3A%2F%2Fraw.githubusercontent.com%2Fleanprover%2Flean4%2Frefs%2Fheads%2Fmaster%2Ftests%2Flean%2Frun%2Fgrind_ite.lean)
in the Live Lean editor.
