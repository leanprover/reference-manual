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


open Lean.Grind

#doc (Manual) "`if`-`then`-`else` Normalization" =>
%%%
tag := "grind-if-then-else-norm"
%%%

```lean -show
open Std
```

This example is a showcase for the “out of the box” power of {tactic}`grind`.
Later examples will explore adding {attrs}`@[grind]` annotations as part of the development process, to make {tactic}`grind` more effective in a new domain.
This example does not rely on any of the algebra extensions to {tactic}`grind`, we're just using:
* instantiation of annotated theorems from the library,
* {tech}[congruence closure], and
* case splitting.

The solution here builds on an earlier formalization by Chris Hughes, but with some notable improvements:
* the verification is separate from the code,
* the proof is now a one-liner combining {tactic}`fun_induction` and {tactic}`grind`,
* the proof is robust to changes in the code (e.g. swapping out {name}`HashMap` for {name}`TreeMap`) as well as changes to the precise verification conditions.


# The problem

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

# The formal statement

:::comment
FIXME: @david-christiansen: can I give `IfExpr` a hover/linkify even though it is a forward reference? Similarly `eval` below?
:::

To formalize the statement in Lean, we use an inductive type `IfExpr`:

```lean
/--
An if-expression is either boolean literal, a
numbered variable, or an if-then-else expression
where each subexpression is an if-expression.
-/
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
def IfNormalization : Type :=
  { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }
```

# Other solutions

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

# The solution using {tactic}`grind`

Actually solving the problem is not that hard:
we just need a recursive function that carries along a record of “already assigned variables”,
and then, whenever performing a branch on a variable, adding a new assignment in each of the branches.
It also needs to flatten nested if-then-else expressions which have another if-then-else in the “condition” position.
(This is extracted from Chris Hughes's solution, but without the subtyping.)

Let's work inside the {name}`IfExpr` namespace.
```lean
namespace IfExpr
```

:::keepEnv

```lean +error (name := failed_to_show_termination)
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

```leanOutput failed_to_show_termination (stopAt := "Could not find a decreasing measure.")
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
```


Lean here is telling us that it can't see that the function is terminating.
Often Lean is pretty good at working this out for itself, but for sufficiently complicated functions
we need to step in to give it a hint.

In this case we can see that it's the recursive call
`ite (ite a b c) t e` which is calling {lean}`normalize` on `(ite a (ite b t e) (ite c t e))`
where Lean is having difficulty. Lean has made a guess at a plausible termination measure,
based on using automatically generated {name}`sizeOf` function, but can't prove the resulting goal,
essentially because `t` and `e` appear multiple times in the recursive call.
:::

To address problems like this, we nearly always want to stop using the automatically generated `sizeOf` function,
and construct our own termination measure. We'll use

```lean
@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1
```


Many different functions would work here. The basic idea is to increase the “weight” of the “condition” branch
(this is the multiplicative factor in the `2 * normSize i` ),
so that as long the “condition” part shrinks a bit, the whole expression counts as shrinking even if the “then” and “else” branches have grown.
We've annotated the definition with {attrs}`@[simp]` so Lean's automated termination checker is allowed to unfold the definition.

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

```lean -keep
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
* if we normalize an “if-then-else” expression using some assignments, and then evaluate the remaining variables,
  we get the same result as evaluating the original “if-then-else” using the composite of the two assignments,
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
“any variable appearing in the assignments no longer appears in the normalized expression”
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


```lean -show
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

(The fact that we can do this relies on the fact that all the lemmas for both {name}`HashMap` and for {name}`TreeMap` that {tactic}`grind` needs have already be annotated in the standard library.)

If you'd like to play around with this code,
you can find the whole file [here](https://github.com/leanprover/lean4/blob/master/tests/lean/run/grind_ite.lean),
or in fact [play with it with no installation](https://live.lean-lang.org/#project=lean-nightly&url=https%3A%2F%2Fraw.githubusercontent.com%2Fleanprover%2Flean4%2Frefs%2Fheads%2Fmaster%2Ftests%2Flean%2Frun%2Fgrind_ite.lean)
in the Live Lean editor.

```lean -show
end IfExpr
```
