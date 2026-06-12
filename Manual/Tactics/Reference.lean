/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers
import Manual.Tactics.Reference.Simp


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

set_option maxHeartbeats 250000

#doc (Manual) "Tactic Reference" =>
%%%
tag := "tactic-ref"
%%%

# Classical Logic
%%%
tag := "tactic-ref-classical"
%%%

:::tactic "classical"
:::


# Assumptions
%%%
tag := "tactic-ref-assumptions"
%%%

The {tactic}`assumption` tactic closes the goal if there is a hypothesis in the context whose type matches the goal's target.

:::tactic Lean.Parser.Tactic.assumption
:::

:::example "Closing a Goal from Context"
Here the hypothesis `h₃` has exactly the type needed by the goal, so {tactic}`assumption` finds it automatically:
```lean
example (a b c d e : Nat)
    (h₁ : a < b) (h₂ : b < c) (h₃ : c < d)
    (h₄ : d < e) : c < d := by
  assumption
```
:::

:::tactic "apply_assumption"
:::

# Quantifiers
%%%
tag := "tactic-ref-quantifiers"
%%%

The {tactic}`exists` tactic is used to prove an existential goal by providing a witness.

:::tactic "exists"
:::

:::example "Providing a Witness"
To prove that there exists a natural number whose double is 4, it suffices to provide the witness `2`:
```lean
example : ∃ n : Nat, n + n = 4 := by
  exists 2
```
:::

The {tactic}`intro` tactic makes progress on goals whose target type is a function type or a universal quantifier.
It introduces the function's parameter into the local context as a new assumption (for propositions) or a new local variable (for data) and changes the goal to the function's body.

:::tactic "intro"
:::

:::example "Introducing an Implication"
The goal `P → R` is an implication. {tactic}`intro` moves its premise into the context as `hp`:
```lean
example (P Q R : Prop) (hpq : P → Q) (hqr : Q → R) :
    P → R := by
  intro hp
  exact hqr (hpq hp)
```
:::

:::example "Introducing a Universal Quantifier"
To prove a universally quantified statement, {tactic}`intro` introduces the quantified variable:
```lean
example : ∀ (n : Nat), n + 0 = n := by
  intro n
  rfl
```
:::

:::example "Multiple Introductions"
Multiple names can be provided to introduce several assumptions at once.
Calling {tactic}`intro` once with multiple names is equivalent to calling it multiple times:
```lean
example (P Q R : Prop) (h : P → Q → R) :
    P → Q → R := by
  intro hP hQ
  exact h hP hQ
```
:::

:::example "Anonymous Introduction"
When called with no arguments, {tactic}`intro` introduces one parameter using the binder's name if available:
```lean
example : ∀ (n : Nat), n = n := by
  intro
  rfl
```
:::

:::tactic "intros"
:::

The {tactic}`rintro` tactic combines {tactic}`intro` with pattern matching, allowing hypotheses to be destructured as they are introduced.

:::tactic "rintro"
:::

:::example "Introducing and Destructuring"
The anonymous constructor pattern `⟨hp, hq⟩` destructs the conjunction as it is introduced:
```lean
example : P ∧ Q → Q ∧ P := by
  rintro ⟨hp, hq⟩
  exact ⟨hq, hp⟩
```
:::

:::example "Introducing a Disjunction"
For a disjunction, {tactic}`rintro` creates one subgoal per case:
```lean
example : P ∨ Q → Q ∨ P := by
  rintro (hp | hq)
  · right; exact hp
  · left; exact hq
```
:::

:::example "Substituting on Introduction"
When matching on an equality where one side is a single variable also matched by {tactic}`rintro`, one
can use `rfl` as a pattern name. This causes the equality to be immediately used as a substition applied to the goal.
Here, instead of introducing a hypothesis `h : 7 * b = a`, {tactic}`rintro` directly replaces `a` with `7 * b`:
```lean
example : ∀ (a b : Nat), 7 * b = a → a + 1 = 7 * b + 1 := by
  rintro a b rfl
  rfl
```
:::


# Relations
%%%
tag := "tactic-ref-relations"
%%%

The {tactic}`rfl` tactic succeeds whenever the two sides of the relation are {tech (key := "definitional equality")}[definitionally equal], even if they are not syntactically identical.

:::tactic "rfl"
:::

:::example "Reflexivity"
When both sides of an equation are the same, {tactic}`rfl` closes the goal immediately:
```lean
example (n : Nat) : n = n := by
  rfl
```
:::

:::example "Definitional Equality"
Even though `2 + 3` and `5` are syntactically different, they are definitionally equal, so {tactic}`rfl` succeeds:
```lean
example : 2 + 3 = 5 := by
  rfl
```
:::

:::example "Reflexive Relations"
The {tactic}`rfl` tactic works with any relation that has a lemma tagged with the {attr}`refl` attribute, not just equality.
For instance, it can close goals involving {lean}`Iff`:
```lean
example (P : Prop) : P ↔ P := by
  rfl
```
:::

:::tactic "rfl'"
:::


:::tactic Lean.Parser.Tactic.applyRfl
:::

:::syntax attr (title := "Reflexive Relations")
The {attr}`refl` attribute marks a lemma as a proof of reflexivity for some relation.
These lemmas are used by the {tactic}`rfl`, {tactic}`rfl'`, and {tactic}`apply_rfl` tactics.

```grammar
refl
```
:::

The {tactic}`symm` tactic swaps the two sides of a symmetric relation in the goal, such as turning `a = b` into `b = a`.
It can also be applied to a hypothesis with `symm at h`.

:::tactic "symm"
:::

:::example "Swapping Sides of an Equality"
After {tactic}`symm`, the goal becomes `a = b`, which matches the hypothesis `h`:
```lean
example (a b : Nat) (h : a = b) : b = a := by
  symm
  exact h
```
:::

:::tactic "symm_saturate"
:::

:::syntax attr (title := "Symmetric Relations")
The {attr}`symm` attribute marks a lemma as a proof that a relation is symmetric.
These lemmas are used by the {tactic}`symm` and {tactic}`symm_saturate` tactics.

```grammar
symm
```
:::

The {tactic}`calc` tactic opens a calculation block for chaining a sequence of relation steps (equalities, inequalities, etc.), where each step is justified by a tactic.

:::tactic "calc"
:::

:::example "A Chain of Equalities"
Each step in a {tactic}`calc` block can be justified by a term, or a tactic after `by`:
```lean
example (a b c : Nat) (hab : a = b) (hbc : b = c) :
    a + 1 = c + 1 + 0 := by
  calc
    a + 1 = b + 1 := by rw [hab]
    _ = c + 1 := by rw [hbc]
    _ = c + 1 + 0 := by rw [Nat.add_zero]
```
:::

:::example "Mixing Relations"
A {tactic}`calc` block can chain different relations, such as equalities and inequalities, as long as {name}`Trans` instances are available:
```lean
example (a b : Nat) (h : a = b) (h2 : b + 5 ≤ 3 * a^2) :
    a ≤ 3 * a^2 := by
  calc
    a = b := h
    _ ≤ b + 5 := by apply Nat.le_add_right
    _ ≤ 3 * a^2 := h2
```
:::

## Equality
%%%
tag := "tactic-ref-equality"
%%%

The {tactic}`subst` tactic eliminates a variable that is known to be equal to some expression.
Given a hypothesis `h : x = e` or `h : e = x` where `x` is a local variable, it replaces all occurrences of `x` with `e` throughout the goal and context, and removes both `x` and `h`.

:::tactic "subst"
:::

:::example "Substituting a Known Equality"
After `subst h`, the variable `n` is replaced by `3` everywhere, and the goal becomes `3 + 1 = 4`:
```lean
example (n : Nat) (h : n = 3) : n + 1 = 4 := by
  subst h
  rfl
```
:::

:::tactic "subst_eqs"
:::

:::tactic "subst_vars"
:::

The {tactic}`congr` tactic reduces an equality goal to equalities between the arguments of the outermost function application on each side.

:::tactic "congr"
:::

:::example "Basic Congruence"
The goal `n + 1 = m + 1` is reduced to `n = m`, which {tactic}`congr` closes using the hypothesis `h`:
```lean
example (n m : Nat) (h : n = m) : n + 1 = m + 1 := by
  congr
```
:::

:::example "Controlling Depth"
A numeric argument controls how many layers {tactic}`congr` descends.
Here `congr 2` peels off two layers of arithmetic operations, leaving `a * c = b * c` as a subgoal that still needs to be solved:
```lean
example (a b c : Nat) (h : b * c = a * c) :
    (a * c) * 2 + 3 = (b * c) * 2 + 3 := by
  congr 2
  symm
  exact h
```
Using uncontrolled {tactic}`congr` would have left us with the goal `a = b`,
which we cannot close, because even though `b * c = a * c`, it might be because `c` is zero.
```lean +error (name := bareCongr)
example (a b c : Nat) (h : b * c = a * c) :
    (a * c) * 2 + 3 = (b * c) * 2 + 3 := by
  congr
```
```leanOutput bareCongr
unsolved goals
case e_a.e_a.e_a
a b c : Nat
h : b * c = a * c
⊢ a = b
```
:::

:::tactic "eq_refl"
:::

:::tactic "ac_rfl"
:::

# Associativity and Commutativity
%%%
tag := "tactic-ref-associativity-commutativity"
%%%

:::tactic "ac_nf"
:::

:::tactic "ac_nf0"
:::


# Lemmas
%%%
tag := "tactic-ref-lemmas"
%%%

The {tactic}`exact` tactic closes the current goal by providing a term whose type matches the goal's target type.
It works up to {tech}[definitional equality], so the term's type does not need to be syntactically identical to the goal.

:::tactic "exact"
:::

:::example "Closing a Goal with a Hypothesis"
When a hypothesis already has the exact type of the goal, {tactic}`exact` can close it directly:
```lean
example (P : Prop) (h : P) : P := by
  exact h
```
:::

:::example "Applying a Lemma"
The argument to {tactic}`exact` can be any expression, including function applications:
```lean
example (P Q : Prop) (hp : P) (hpq : P → Q) : Q := by
  exact hpq hp
```
:::

The {tactic}`apply` tactic works backwards from the goal.
Given an expression whose type is a function type ending in the goal's target, it replaces the goal with one subgoal for each remaining argument.
Where {tactic}`exact` requires the term to have exactly the goal's type, {tactic}`apply` allows the term to require additional premises that become new goals.

:::tactic "apply"
:::

:::example "Reducing a Goal with an Implication"
Applying `hpq` reduces the goal from `Q` to `P`, which can then be closed with {tactic}`exact`:
```lean
example (P Q : Prop) (hpq : P → Q) (hp : P) : Q := by
  apply hpq
  exact hp
```
:::

:::example "Multiple Subgoals"
When the applied term has multiple premises, {tactic}`apply` creates a subgoal for each:
```lean
example (P Q R : Prop) (h : P → Q → R)
    (hp : P) (hq : Q) : R := by
  apply h
  · exact hp
  · exact hq
```
:::

:::example "Applying Lemmas"
The argument to {tactic}`apply` is not limited to local hypotheses.
Any term whose conclusion matches the goal can be used, including lemmas:
```lean
example (a b c : Nat) (hab : a < b) (hbc : b < c) :
    a < c := by
  apply Nat.lt_trans
  · exact hab
  · exact hbc
```
:::

Note that {tactic}`apply` does not work directly with `↔` (if-and-only-if) hypotheses.
To use a hypothesis `h : P ↔ Q` backwards on the goal, use {tactic}`rw` instead, or extract one direction with `h.mp` or `h.mpr`.

The {tactic}`refine` tactic is like {tactic}`exact`, but allows holes written as `?_` that become new goals.
This is useful when part of a term is known but some arguments still need to be proved.

:::tactic "refine"
:::

:::example "Exact with Holes"
The anonymous constructor provides the witness `2`, while `?_` leaves the proof obligation `2 + 2 = 4` as a new goal:
```lean
example : ∃ n : Nat, n + n = 4 := by
  refine ⟨2, ?_⟩
  rfl
```
:::

:::tactic "refine'"
:::

:::tactic "solve_by_elim"
:::

:::tactic "apply_rules"
:::

:::tactic "as_aux_lemma"
:::


# Falsehood
%%%
tag := "tactic-ref-false"
%%%

The {tactic}`exfalso` tactic changes the goal to `False`. It is named after the Latin phrase _ex falso quodlibet_, that is, “from falsehood, anything follows”.
This is useful when the hypotheses are contradictory: once the goal is {name}`False`, it can be closed by deriving a contradiction.
Because it discards the original goal entirely, {tactic}`exfalso` should only be used when the hypotheses are genuinely contradictory.
If they are not, the resulting `False` goal will be unsolvable.

:::tactic "exfalso"
:::

:::example "Reasoning from a Contradiction"
The hypothesis `h : n < n` is contradictory because no number is strictly less than itself.
After {tactic}`exfalso` changes the goal to `False`, we can close it using the irreflexivity lemma:
```lean
example (n : Nat) (h : n < n) : n * n = n + 1 := by
  exfalso
  exact Nat.lt_irrefl n h
```
:::

The {tactic}`contradiction` tactic automatically closes a goal when the hypotheses are trivially contradictory, without requiring the user to identify the specific contradiction.

:::tactic "contradiction"
:::

:::example "Closing a Goal by Contradiction"
{tactic}`contradiction` searches the hypotheses automatically for immediate logical contradictions.
```lean
example (hp : P) (hnp : ¬P) : Q := by
  contradiction
```
It also recognizes incompatibilities between constructors of the same type.
```lean
example (h : Nat.zero = Nat.succ Nat.zero) : P := by
  contradiction
```
:::

:::tactic "false_or_by_contra"
:::


# Goal Management
%%%
tag := "tactic-ref-goals"
%%%

The {tactic}`suffices` tactic replaces the goal with another statement that is at least as strong.
That is, the new goal suffices to show the old one.

:::tactic "suffices"
:::

:::example "Suffices with a Term Proof"
Using {tactic}`suffices` with `from` shows how the sufficient condition `h : a = b` implies the original goal, and the second goal requires proving `a = b`:
```lean
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  suffices h : a = b from congrArg (· + 1) h
  exact h
```
:::

:::example "Suffices with a Tactic Proof"
We first show that it suffices to know that the list of the length is 3 in order to conclude that
the list has nonzero length. Then we prove that the list does in fact have lengtht three.
```lean
example (xs : List Nat) (h : xs = [1, 2, 3]) :
    xs.length > 0 := by
  suffices hsuff : xs.length = 3 by
    rw [hsuff]
    decide
  simp [h]
```
:::

The {tactic}`change` tactic replaces the goal (or a hypothesis) with a {tech (key := "definitional equality")}[definitionally equal] alternative.
This can make the goal easier to read or bring it into a form that other tactics expect.

:::tactic "change"
:::

:::example "Unfolding a Definition"
Because `¬P` is defined as `P → False`, {tactic}`change` can make this explicit:
```lean
example (hp : P) : ¬¬P := by
  change ¬P → False
  intro hnp
  exact hnp hp
```
:::

:::tactic "generalize"
:::

The {tactic}`specialize` tactic instantiates a universally quantified or function-typed hypothesis with specific arguments, replacing it in the context with the result.
Because {tactic}`specialize` modifies the hypothesis in place, the original general statement is lost after specialization.
If the original hypothesis is needed again, use {tactic}`have` to create a copy first, for example `have h' := h` before specializing `h`.

:::tactic "specialize"
:::

:::example "Partially Specializing a Hypothesis"
After `specialize h 1`, the hypothesis becomes `h : ∀ b, 1 + b = b + 1`, which can then be applied to `2`:
```lean
example (h : ∀ a b : Nat, a + b = b + a) :
    1 + 2 = 2 + 1 := by
  specialize h 1
  exact h 2
```
:::

The {tactic}`obtain` tactic is used when a hypothesis or proof term has internal structure that should be broken apart.
Where {tactic}`have` introduces a single new fact into the context, {tactic}`obtain` destructs a term into its pieces using pattern matching. For example, extracting the witness from an existential or the two sides of a conjunction.

:::tactic "obtain"
:::

:::example "Unpacking an Existential"
The pattern `⟨n, hn⟩` extracts the witness `n` and the proof `hn : n + n = 10` from the existential hypothesis:
```lean
example (h : ∃ n : Nat, n + n = 10) : ∃ m : Nat, m = 5 := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by grind⟩
```
:::

:::example "Unpacking a Conjunction"
The same pattern works for conjunctions:
```lean
example (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩
```
:::

The {tactic}`show` tactic selects a goal whose target unifies with the given type and makes it the current goal.
When there is only one goal, it can be used like {tactic}`change` to restate the goal in a {tech (key := "definitional equality")}[definitionally equal] form.

:::tactic "show"
:::

:::example "Selecting a Goal"
When there are multiple goals, {tactic}`show` brings a specific one to the front.
Here, after {tactic}`constructor` the goals are `⊢ P` then `⊢ Q`, but `show Q` reorders them:
```lean
example (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  show Q
  exact hq
  exact hp
```
:::

:::tactic Lean.Parser.Tactic.showTerm
:::


# Cast Management
%%%
tag := "tactic-ref-casts"
%%%

The tactics in this section make it easier avoid getting stuck on {deftech}_casts_, which are functions that coerce data from one type to another, such as converting a natural number to the corresponding integer.
They are described in more detail by {citet castPaper}[].

:::tactic Lean.Parser.Tactic.tacticNorm_cast__
:::

:::tactic Lean.Parser.Tactic.pushCast
:::

:::tactic Lean.Parser.Tactic.tacticExact_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticApply_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticRw_mod_cast___
:::

:::tactic Lean.Parser.Tactic.tacticAssumption_mod_cast_
:::

# Managing `let` Expressions

:::tactic "extract_lets"
:::

:::tactic "lift_lets"
:::

:::tactic "let_to_have"
:::

:::tactic "clear_value"
:::


# Extensionality
%%%
tag := "tactic-ref-ext"
%%%

The {tactic}`ext` tactic applies extensionality lemmas registered with the {attr}`ext` attribute.
The principle of extensionality states that two objects are equal if they are built from the same components. For example, two functions are equal if they return the same value on every input.

:::tactic "ext"
:::

:::example "Function Extensionality"
After `ext n`, the goal changes from an equality of functions to an equality of their values at an arbitrary `n`:
```lean
example : (fun n : Nat => n + 0) = (fun n => n) := by
  ext n
  rfl
```
:::

:::tactic Lean.Elab.Tactic.Ext.tacticExt1___
:::

:::tactic Lean.Elab.Tactic.Ext.applyExtTheorem
:::

The {tactic}`funext` tactic is a variant of {tactic}`ext` that specifically applies function extensionality.

:::tactic "funext"
:::

:::example "Proving Functions Equal with `funext`"
After `funext x`, the goal reduces to showing `f x = g x` for an arbitrary `x`:
```lean
example (f g : Nat → Nat)
    (hf : ∀ x, f x = 2 * x) (hg : ∀ x, g x = x + x) : f = g := by
  funext x
  simp only [hf, hg]
  exact Nat.two_mul x
```
:::

# SMT-Inspired Automation
:::tactic "grind"
:::

:::tactic "grind?"
:::

:::tactic "lia"
:::

:::tactic "grobner"
:::


{include 0 Manual.Tactics.Reference.Simp}

# Rewriting
%%%
tag := "tactic-ref-rw"
%%%

The {tactic}`rw` uses proofs of equality to rewrite goals and/or hypotheses, replacing occurrences of one of the equated terms with the other.
Given a proof of an equality `h : x = y` or an if-and-only-if `h : P ↔ Q`, it replaces occurrences of the left-hand side with the right-hand side in the goal.
Use `rw [← h]` to rewrite in the reverse direction, and `rw [h] at hyp` to rewrite in a hypothesis `hyp` rather than the goal.
After rewriting, {tactic}`rw` automatically tries to close the goal with {tactic}`rfl`.

:::tactic "rw"
:::

:::example "Rewriting Forward and Backward"
Given `h : x = y`, writing `rw [h]` replaces `x` with `y`, while `rw [← h]` replaces `y` with `x`:
```lean
example (x y : Nat) (h : x = y) (hy : y < 10) :
    x < 10 := by
  rw [h]
  exact hy
```
```lean
example (x y : Nat) (h : x = y) (hx : x < 10) :
    y < 10 := by
  rw [← h]
  exact hx
```
:::

:::example "Rewriting in a Hypothesis"
The `at` clause directs the rewrite to a hypothesis instead of the goal:
```lean
example (x y : Nat) (h : x = y) (h2 : x + 1 = 3) :
    y + 1 = 3 := by
  rw [h] at h2
  exact h2
```
:::

Note that {tactic}`rw` does not rewrite under binders such as `∀`, `∃`, or `∑`.
For example, if `h : a = b`, then `rw [h]` will not rewrite occurrences of `a` inside `∀ x, f a x = g x`.

:::tactic "rewrite"
:::

:::tactic "erw"
:::

:::tactic Lean.Parser.Tactic.tacticRwa__
:::

{docstring Lean.Meta.Rewrite.Config +allowMissing}

{docstring Lean.Meta.Occurrences}

{docstring Lean.Meta.TransparencyMode +allowMissing}

{docstring Lean.Meta.Rewrite.NewGoals +allowMissing}


:::tactic "unfold"

Implemented by {name}`Lean.Elab.Tactic.evalUnfold`.
:::

:::tactic "replace"
:::

:::tactic "delta"
:::


# Inductive Types
%%%
tag := "tactic-ref-inductive"
%%%

## Introduction
%%%
tag := "tactic-ref-inductive-intro"
%%%

The {tactic}`constructor` tactic tries to solve the goal by application of a constructor.
When the goal's target type has a single constructor, it replaces the goal with one subgoal for each of the constructor's arguments.
This is commonly used to split a goal of the form `P ∧ Q` into separate goals for `P` and `Q`, or to split `P ↔ Q` into the two implications.
It is essentially syntactic sugar for `refine ⟨?_, ?_, …⟩` with as many holes as the constructor has arguments.

:::tactic "constructor"
:::

:::example "Splitting a Conjunction"
The {tactic}`constructor` tactic splits the goal `P ∧ Q` into two subgoals, one for each conjunct:
```lean
example (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq
```
:::

:::example "Splitting an If-and-only-If"
Because `P ↔ Q` is defined as `(P → Q) ∧ (Q → P)`, {tactic}`constructor` splits it into the two directions:
```lean
example : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor
  · intro ⟨hp, hq⟩; exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩; exact ⟨hp, hq⟩
```
:::

:::tactic "injection"
:::

:::tactic "injections"
:::

The {tactic}`left` and {tactic}`right` tactics select which side of a disjunction to prove.

:::tactic "left"
:::

:::tactic "right"
:::

:::example "Proving a Disjunction"
Using {tactic}`left` selects the first disjunct, reducing the goal from `P ∨ Q` to `P`:
```lean
example (hp : P) : P ∨ Q := by
  left
  exact hp
```
:::

## Elimination
%%%
tag := "tactic-ref-inductive-elim"
%%%

Elimination tactics use {ref "recursors"}[recursors] and the automatically-derived {ref "recursor-elaboration-helpers"}[`casesOn` helper] to implement induction and case splitting.
The {tech}[subgoals] that result from these tactics are determined by the types of the minor premises of the eliminators, and using different eliminators with the {keyword}`using` option results in different subgoals.

:::::leanSection
```lean -show
variable {n : Nat}
```
::::example "Choosing Eliminators"

:::tacticExample
```setup
intro n i
```
{goal -show}`∀(n : Nat) (i : Fin (n + 1)), 0 + i = i`

```pre -show
n : Nat
i : Fin (n + 1)
⊢ 0 + i = i
```

When attempting to prove that {lean}`∀(i : Fin (n + 1)), 0 + i = i`, after introducing the hypotheses the tactic {tacticStep}`induction i` results in:

```post
case mk
n val✝ : Nat
isLt✝ : val✝ < n + 1
⊢ 0 + ⟨val✝, isLt✝⟩ = ⟨val✝, isLt✝⟩
```

This is because {name}`Fin` is a {tech}[structure] with a single non-recursive constructor.
Its recursor has a single minor premise for this constructor:
```signature
Fin.rec.{u} {n : Nat} {motive : Fin n → Sort u}
  (mk : (val : Nat) →
    (isLt : val < n) →
    motive ⟨val, isLt⟩)
  (t : Fin n) : motive t
```
:::
:::tacticExample
```setup
intro n i
```
{goal -show}`∀(n : Nat) (i : Fin (n + 1)), 0 + i = i`

```pre -show
n : Nat
i : Fin (n + 1)
⊢ 0 + i = i
```

Using the tactic {tacticStep}`induction i using Fin.induction` instead results in:

```post
case zero
n : Nat
⊢ 0 + 0 = 0

case succ
n : Nat
i✝ : Fin n
a✝ : 0 + i✝.castSucc = i✝.castSucc
⊢ 0 + i✝.succ = i✝.succ
```

{name}`Fin.induction` is an alternative eliminator that implements induction on the underlying {name}`Nat`:
```signature
Fin.induction.{u} {n : Nat}
  {motive : Fin (n + 1) → Sort u}
  (zero : motive 0)
  (succ : (i : Fin n) →
    motive i.castSucc →
    motive i.succ)
  (i : Fin (n + 1)) : motive i
```
:::

::::
:::::

{deftech}[Custom eliminators] can be registered using the {attr}`induction_eliminator` and {attr}`cases_eliminator` attributes.
The eliminator is registered for its explicit targets (i.e. those that are explicit, rather than implicit, parameters to the eliminator function) and will be applied when {tactic}`induction` or {tactic}`cases` is used on targets of those types.
When present, custom eliminators take precedence over recursors.
Setting {option}`tactic.customEliminators` to {lean}`false` disables the use of custom eliminators.

:::syntax attr (title := "Custom Eliminators")
The {attr}`induction_eliminator` attribute registers an eliminator for use by the {tactic}`induction` tactic.
```grammar
induction_eliminator
```

The {attr}`cases_eliminator` attribute registers an eliminator for use by the {tactic}`cases` tactic.
```grammar
cases_eliminator
```
:::

The {tactic}`cases` tactic performs case analysis on a term in the local context.
It decomposes the term according to the constructors of its inductive type, creating one subgoal for each constructor.
For a hypothesis `h : P ∧ Q`, this yields its two components; for `h : P ∨ Q`, it creates two separate goals; for a natural number `n`, it splits into the `zero` and `succ` cases.

:::tactic "cases"
:::

:::example "Destructuring a Conjunction"
```lean
example (h : P ∧ Q) : Q ∧ P := by
  cases h with
  | intro left right => exact ⟨right, left⟩
```
:::

:::example "Disjunction"
For a disjunction, {tactic}`cases` creates one subgoal per case:
```lean
example (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq
```
:::

:::example "Case Analysis on Natural Numbers"
The {tactic}`cases` tactic can also split data, such as a natural number into the `zero` and `succ` cases:
```lean
example (n : Nat) : n = 0 ∨ n ≥ 1 := by
  cases n with
  | zero => left; rfl
  | succ m => right; grind
```
:::

The {tactic}`rcases` tactic is a recursive version of {tactic}`cases` that destructs a hypothesis using pattern matching notation.
It uses `⟨x, y⟩` for constructor patterns and `(x | y)` for disjunctive patterns, and these can be nested.

:::tactic "rcases"
:::

:::example "Nested Destructuring"
The pattern `⟨hp, hq, hr⟩` destructs the nested conjunction `P ∧ Q ∧ R` in one step:
```lean
example (h : P ∧ Q ∧ R) : R ∧ Q ∧ P := by
  rcases h with ⟨hp, hq, hr⟩
  exact ⟨hr, hq, hp⟩
```
:::

:::tactic "fun_cases"
:::

The {tactic}`induction` tactic performs mathematical induction.
Like {tactic}`cases`, it splits into cases, but it additionally provides an inductive hypothesis in each recursive case.
This makes {tactic}`induction` a useful tool for proving properties of recursive data, especially natural numbers.

:::tactic "induction"
:::

:::example "Induction on Natural Numbers"
Here we use induction to establish that zero is the identity for addition on the left.
The base case `zero` is closed by {tactic}`rfl`, and the successor case uses the inductive hypothesis `ih : 0 + n = n`:
```lean
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
```
:::

:::example "Induction on Lists"
The {tactic}`induction` tactic works on any inductive type, not just natural numbers:
```lean
example (xs : List α) : xs.reverse.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse_cons, ih]
```
:::

:::tactic "fun_induction"
:::


:::tactic "nofun"
:::

:::tactic "nomatch"
:::


# Library Search
%%%
tag := "tactic-ref-search"
%%%

The library search tactics are intended for interactive use.
When run, they search the Lean library for lemmas or rewrite rules that could be applicable in the current situation, and suggests a new tactic.
These tactics should not be left in a proof; rather, their suggestions should be incorporated.

:::tactic "exact?"
:::

:::tactic "apply?"
:::




:::tacticExample
{goal -show}`∀ (i j k : Nat), i < j → j < k → i < k`
```setup
intro i j k h1 h2
```
In this proof state:
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```

invoking {tacticStep}`apply?` suggests:

```tacticOutput
Try this:
  [apply] exact Nat.lt_trans h1 h2
```

```post -show

```
:::


:::tactic "rw?"
:::

# Case Analysis
%%%
tag := "tactic-ref-cases"
%%%


The {tactic}`split` tactic splits the goal on a match expression or if-then-else, creating one subgoal per branch.

:::tactic "split"
:::

:::example "Splitting a Match Expression"
The {tactic}`split` tactic creates one subgoal per branch, allowing each to be proved using the relevant hypotheses:
```lean
example (p : Bool) (x y : Nat) (hx : x > 0) (hy : y > 0) :
    (match p with | true => x | false => y) > 0 := by
  split
  · exact hx
  · exact hy
```
:::

The {tactic}`by_cases` tactic splits the proof into two cases based on whether a proposition holds or not.
Always name the hypothesis with `h : P` syntax; without a name, Lean generates an inaccessible name (`h✝`) that cannot be referred to in the proof.

:::tactic "by_cases"
:::

:::example "Case Split on a Proposition"
After `by_cases h : n = 0`, the proof splits into a branch where `h : n = 0` and a branch where `h : n ≠ 0`:
```lean
example (n : Nat) : n = 0 ∨ n ≠ 0 := by
  by_cases h : n = 0
  · left; exact h
  · right; exact h
```
:::

# Decision Procedures
%%%
tag := "tactic-ref-decision"
%%%


The {tactic}`decide` tactic closes goals whose truth is decidable in the sense that it
can be determined by computation, such as concrete arithmetic facts or membership in finite structures.

:::tactic Lean.Parser.Tactic.decide (show := "decide")
:::

:::example "Deciding Concrete Propositions"
Here we see how {tactic}`decide` can close simple goals.
```lean
example : 2 + 2 = 4 := by decide
```
```lean
example : ¬(3 = 5) := by decide
```
:::

Because {tactic}`decide` runs the decision procedure using the kernel's term reduction, it can be extremely slow or time out on large problems.
For example, checking `Nat.Prime 104729` with {tactic}`decide` would take impractically long.
For arithmetic goals involving large numbers, {tactic}`grind`, {tactic}`omega` or `norm_num` are more performant.

:::tactic Lean.Parser.Tactic.nativeDecide (show := "native_decide")
:::

:::tactic "omega"
:::

:::tactic "bv_omega"
:::


## SAT Solver Integration
%%%
tag := "tactic-ref-sat"
%%%

:::tactic "bv_decide"
:::

:::tactic "bv_normalize"
:::

:::tactic "bv_check"
:::

:::tactic Lean.Parser.Tactic.bvTraceMacro
:::

# Call-by-Value Evaluation
%%%
tag := "tactic-ref-cbv"
%%%

The {tactic}`cbv` tactic simulates call-by-value evaluation to reduce terms.
In {deftech}[call-by-value evaluation], the arguments to a function are reduced to values before the function call is reduced.
Roughly speaking, _values_ are either functions or applications of constructors to values; the body of a function does not need to be a value for the function itself to count as a value.
This evaluation strategy matches the execution order of code produced by the Lean compiler, which makes it a good match for code that is written to perform well at run time.

{tactic}`cbv` unfolds definitions using their {tech}[equational lemmas] and applies similar theorems that are automatically proved for {tech}[matcher functions], producing propositional equality proofs at each step.
Because the unfolding is propositional rather than definitional, {tactic}`cbv` can reduce functions defined via {ref "well-founded-recursion"}[well-founded recursion] or {ref "partial-fixpoint"}[partial fixpoints].
In general, these functions are not definitionally equal to their unfoldings, so the kernel's definitional reduction does not reduce their recursive calls.

The proofs produced by {tactic}`cbv` only use the three standard axioms ({name}`propext`, {name}`Quot.sound`, and {name}`Classical.choice`).
In particular, they do not require trust in the correctness of the code generator, unlike {tactic}`native_decide`.

Because {tactic}`cbv` rewrites subterms via {name}`congrArg` and {name}`congrFun`, it cannot rewrite subterms that appear in dependent positions.
Rewriting the argument of a dependent function would change the type of subsequent arguments, and even with heterogeneous equality there are no suitable congruence lemmas for arbitrary dependent functions.

:::paragraph
When reducing constant applications, {tactic}`cbv` tries the following strategies in order:

 1. Custom {attr}`cbv_eval` rewrite rules
 2. {tech}[Equational lemmas] (e.g., `foo.eq_1`, `foo.eq_2`)
 3. Unfolding equations
 4. Kernel matcher reduction

Declarations marked with {attr}`cbv_opaque` are never unfolded unless a matching {attr}`cbv_eval` rewrite rule is provided.
:::

:::syntax tactic (title := "Call-by-Value Evaluation")
```grammar
cbv $[at $[$h]*]?
```
:::

:::tactic Lean.Parser.Tactic.cbv (show := "cbv")
:::

```lean -show
-- The `cbv` tactic is presently experimental, and a warning is issued when it is used.
-- This option disables the warning:
set_option cbv.warning false
```

:::example "Reducing Well-Founded Recursive Functions"
The function {lean}`countdown` is defined using well-founded recursion, so it is not definitionally equal to its unfolding.
Ordinary {tactic}`rfl` cannot close the goal:
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean +error (name := countdownRfl)
example : countdown 3 = [3, 2, 1, 0] := by rfl
```
```leanOutput countdownRfl
Tactic `rfl` failed: The left-hand side
  countdown 3
is not definitionally equal to the right-hand side
  [3, 2, 1, 0]

⊢ countdown 3 = [3, 2, 1, 0]
```
The {tactic}`cbv` tactic can reduce {lean}`countdown 3` via propositional rewriting and then close the equation goal via {tactic}`rfl`:
```lean
example : countdown 3 = [3, 2, 1, 0] := by
  cbv
```
:::

:::example "Reducing Hypotheses"
The {tactic}`cbv` tactic supports the standard `at` location syntax.
When used with `at h`, it reduces the type of hypothesis `h`.
When used with `at *`, it reduces all non-dependent propositional
hypotheses and the goal target.
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean
example (x : List Nat) (h : x = countdown 2) :
    x = [2, 1, 0] := by
  cbv at h
  exact h
```
:::

:::example "`cbv` as a Non-Finishing Tactic"
Unlike {tactic}`decide`, {tactic}`cbv` is not a terminal tactic.
It simplifies the goal as much as possible but may leave a goal that requires further reasoning.
Here, {tactic}`cbv` reduces the call to {lean}`countdown` but leaves the membership goal:
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean +error (name := cbvNonFinishing)
example : 1 ∈ countdown 2 := by
  cbv
```
```leanOutput cbvNonFinishing
unsolved goals
⊢ List.Mem 1 [2, 1, 0]
```
:::

:::example "Dependent Positions"
```imports -show
import Std.Data.DTreeMap
import Std.Data.TreeMap
```

The function {name}`wfLength` is a version of {name}`List.length` that is defined via {tech}[well-founded recursion] instead of {ref "structural-recursion"}[structural recursion].
As a result, it is {tech}[irreducible]:
```lean
def wfLength : List Nat → Nat
  | [] => 0
  | _ :: xs => wfLength xs + 1
termination_by xs => xs
```
```lean -show
set_option cbv.warning false
```

In a non-dependent {name}`Std.TreeMap`, {tactic}`cbv` can reduce the computed key {lean}`wfLength [1, 2]`:
```lean
def myTreeMap : Std.TreeMap Nat Nat :=
  .empty |>.insert (wfLength [1, 2]) 42

example : myTreeMap.toList = [⟨2, 42⟩] := by
  cbv
```
However, consider a dependent tree map {lean}`FinMap` that maps each key `n` to a value of type `Fin (n + 1)`:
```lean
abbrev FinMap :=
  Std.DTreeMap Nat (fun n => Fin (n + 1))
```
Here {tactic}`cbv` gets stuck because the value type `Fin (n + 1)` depends on the key:
```lean +error (name := depPosition)
example :
    let m : FinMap :=
      .empty |>.insert (wfLength [1, 2])
        ⟨0, by decide_cbv⟩
    m.toList = [⟨2, ⟨0, by omega⟩⟩] := by
  cbv
```
```leanOutput depPosition
unsolved goals
⊢ [⟨wfLength [1, 2], ⟨0, ⋯⟩⟩] = [⟨2, ⟨0, ⋯⟩⟩]
```
:::

## {tactic}`decide_cbv`

:::tactic Lean.Parser.Tactic.decide_cbv (show := "decide_cbv")
:::

:::example "`decide_cbv`"
The {tactic}`decide_cbv` tactic closes goals that are decidable propositions by reducing the {name}`Decidable` instance via {tech}[call-by-value evaluation]:
```lean
example : 2 + 3 = 5 ∧ 10 < 20 := by
  decide_cbv
```
Unlike {tactic}`native_decide`, {tactic}`decide_cbv` does not require trust in the code generator.
Unlike {tactic}`decide`, which uses definitional reduction, {tactic}`decide_cbv` can handle functions defined by {ref "well-founded-recursion"}[well-founded recursion]:
```lean
def isAllPositive : List Int → Bool
  | [] => true
  | x :: xs => x > 0 && isAllPositive xs
termination_by xs => xs

example : isAllPositive [1, 2, 3] = true := by
  decide_cbv
```
:::

::::example "Prime Power Testing with `decide_cbv`"
Because {tactic}`decide_cbv` uses propositional unfolding, it can evaluate complex decision procedures involving {ref "well-founded-recursion"}[well-founded recursive] functions.
Here, {lean}`Nat.minFac` finds the smallest divisor of a number, while the helper {lean}`minFacAux` searches for the smallest odd divisor:
```lean
def minFacAux (n k : Nat) : Nat :=
  if h : n < k * k then n
  else
    if h' : k ∣ n then k
    else
      have : k ≤ n := by
        have := Nat.le_mul_self k; grind
      minFacAux n (k + 2)
termination_by n + 2 - k

def Nat.minFac (n : Nat) : Nat :=
  if 2 ∣ n then 2 else minFacAux n 3
```
:::leanSection
```lean -show
variable {b n : Nat}
```
{lean}`Nat.log b n` computes the floor of the base-{lean}`b` logarithm of {lean}`n` by repeated squaring:
:::
```lean
def Nat.log (b n : Nat) : Nat :=
  if b ≤ 1 then 0 else (go b n).2 where
  go : Nat → Nat → Nat × Nat
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then
        (q, 2 * e)
      else
        (q / b, 2 * e + 1)
```
Here, {tactic}`decide_cbv` can reduce the result of the decision procedure even though there is a free variable `k`:
```lean
example : ¬∃ k,
    k ≤ Nat.log 2 15151515151515 ∧
    0 < k ∧
    15151515151515 =
      Nat.minFac 15151515151515 ^ k := by
  decide_cbv

```
::::

## Controlling {tactic}`cbv` Behavior

:::syntax attr (title := "Custom `cbv` Rewrite Rules")
The {attr}`cbv_eval` attribute registers a theorem as a custom rewrite rule that {tactic}`cbv` applies before trying {tech}[equational lemmas].
The theorem must be an unconditional equality; one side (generally the left-hand side) must be an application of a constant.

```grammar
cbv_eval
```

The `←` modifier instructs {tactic}`cbv` to apply the rule from right to left:
```grammar
cbv_eval ←
```
:::

:::example "`cbv_eval`"
Custom rewrite rules can be used to control how {tactic}`cbv` evaluates specific functions.
For instance, the naïve definition of reversal, {lean}`slowReverse`, has quadratic complexity due to repeated use of {name}`List.append`.
By providing a tail-recursive characterization via {lean}`fastReverse`, {tactic}`cbv` can evaluate {lean}`slowReverse` efficiently:
```lean
def slowReverse : List Nat → List Nat
  | [] => []
  | x :: xs => slowReverse xs ++ [x]

def fastReverse (xs : List Nat) : List Nat :=
  go [] xs
where
  go (acc : List Nat) : List Nat → List Nat
  | [] => acc
  | x :: xs => go (x :: acc) xs

theorem reverse_spec_aux (xs acc : List Nat) :
    fastReverse.go acc xs =
      slowReverse xs ++ acc := by
  fun_induction fastReverse.go
    <;> grind [slowReverse]

@[cbv_eval] theorem slowReverse_cbv
    (xs : List Nat) :
    slowReverse xs = fastReverse xs := by
  simp [fastReverse, reverse_spec_aux]
```
```lean
example : slowReverse [1, 2, 3, 4, 5] = [5, 4, 3, 2, 1] := by
  cbv
```
:::

:::syntax attr (title := "Opaque Declarations for `cbv`")
The {attr}`cbv_opaque` attribute prevents {tactic}`cbv` from unfolding a declaration using its {tech}[equational lemmas] or unfold theorems.
However, {attr}`cbv_eval` rewrite rules always take priority over {attr}`cbv_opaque`: if a matching {attr}`cbv_eval` rule exists for a declaration, it will be applied even if the declaration is marked {attr}`cbv_opaque`.
This allows replacing the default unfolding behavior with a controlled set of evaluation rules.

```grammar
cbv_opaque
```
:::

::::example "Opaque Definitions with `@[cbv_opaque]`"
Marking {lean}`countdown` as {attr}`cbv_opaque` prevents {tactic}`cbv` from unfolding it, so the goal that was previously closed by {tactic}`cbv` now remains unsolved:
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean
attribute [cbv_opaque] countdown
```
```lean +error (name := opaqueError)
example : countdown 3 = [3, 2, 1, 0] := by
  cbv
```
```leanOutput opaqueError
unsolved goals
⊢ countdown 3 = [3, 2, 1, 0]
```
::::

### Custom Simplification Procedures

:::paragraph
A {deftech}[cbv simplification procedure] ({tactic}`cbv` simproc) is a user-defined metaprogram that {tactic}`cbv` invokes on subexpressions matching a given pattern.
While {attr}`cbv_eval` rules are limited to static equality, {tactic}`cbv` simprocs can perform arbitrary computation to decide how to rewrite a subexpression.
Common use cases include defining procedures for evaluating functions on literal values or short-circuiting control flow.

The simprocs used by {tactic}`cbv` have type {name}`Lean.Meta.Sym.Simp.Simproc`, which is distinct from the {name}`Lean.Meta.Simp.Simproc` type used by the {tactic}`simp` tactic.
The two systems are independent: registering a {tactic}`cbv` simproc has no effect on {tactic}`simp`, and vice versa.
:::

:::syntax command (title := "Custom `cbv` Simplification Procedures")
```lean -show
open Lean Lean.Meta.Sym.Simp
```
The body must have type {name}`Simproc` (that is, {lean}`Expr → SimpM Result`).
The pattern is an expression with holes (`_`) that determines which subexpressions trigger the procedure.
Patterns are matched agains subexpressions structurally after unfolding reducible definitions and applying {tech (key := "β")}[β]-, {tech (key := "η-equivalence")}[η]-, and {tech (key := "ζ")}[ζ]-reduction to both sides.
Matching is modulo α-equivalence (bound variable names are ignored), and proof and instance arguments in the pattern are treated as wildcards.
An optional phase specifier controls when the procedure fires during normalization.
When no phase is specified, the default is `↑` (post).

: `↓` (pre)

   Fires on each subexpression _before_ {tactic}`cbv` reduces it. The arguments are still unreduced. Use this phase to override {tactic}`cbv`'s default call-by-value evaluation order. A typical use case would be to evaluate arguments lazily or to short-circuit evaluation (as the built-in {name}`ite` and {name}`Or` procedures do).

: `cbv_eval` (eval)

  Fires _after_ arguments have been reduced to values, but _before_ the function is unfolded. Use this phase to provide efficient ground evaluation procedures.

: `↑` (post, default)

  Fires _after_ {tactic}`cbv` has attempted standard reduction (equation lemmas, unfolding, kernel matching). Use this phase when standard reduction should be tried first.

```grammar
cbv_simproc name (pattern) := body
```

An optional phase specifier can be placed before the name:

```grammar
cbv_simproc ↓ name (pattern) := body
```

```grammar
cbv_simproc cbv_eval name (pattern) := body
```

The `cbv_simproc_decl` variant declares the procedure without activating it.
It can be activated later with {attr}`cbv_simproc`.

```grammar
cbv_simproc_decl name (pattern) := body
```
:::

:::syntax attr (title := "Simplification Procedure Attribute for `cbv`")
The {attr}`cbv_simproc` attribute activates a previously declared simplification procedure (defined with `cbv_simproc_decl`) for use by {tactic}`cbv`.
An optional phase specifier controls when the procedure fires during normalization.

```grammar
cbv_simproc
```

Phase specifiers control when the procedure fires:

```grammar
cbv_simproc ↓
```

```grammar
cbv_simproc ↑
```

```grammar
cbv_simproc cbv_eval
```
:::


::::example "Declaring a `cbv_simproc`"

```imports -show
import Lean.Meta.Tactic.Cbv.CbvSimproc
```

A simplification procedure is declared by providing a pattern and a body of type {name}`Lean.Meta.Sym.Simp.Simproc`.
The pattern is an expression with holes (`_`) that determines which subexpressions trigger the procedure.
Here, the pattern is (`myConst _`), which matches any application of {name}`myConst`.
The procedure ({lean (type := "Simproc")}`fun _e => do return .rfl`) ignores the expression, returning a result that indicates that no rewriting is to be performed.

```lean
opaque myConst : Nat → Nat

open Lean Meta Sym.Simp in
cbv_simproc evalMyConst (myConst _) := fun _e => do
  -- A real simproc would inspect `e`, compute a result,
  -- and return `.step result proof`.
  return .rfl
```

The {keywordOf Lean.Parser.«command_Cbv_simproc_decl_(_):=_»}`cbv_simproc_decl` variant declares the procedure without activating it.
The {attr}`cbv_simproc` attribute can be used to activate it later, optionally at a specific phase:

```lean
open Lean Meta Sym.Simp in
cbv_simproc_decl evalMyConst2 (myConst _) := fun _e =>
  return .rfl

attribute [cbv_simproc cbv_eval] evalMyConst2
```

::::

::::example "Lazy evaluation of a head of the list"
```imports -show
import Lean.Meta.Sym.Simp
```
```lean -show
open Lean Meta Sym.Simp
variable (α : Type)
variable (a : α)
variable (as : List α)
```

This is an example of a pre-phase simplification procedure that breaks the conventional call-by-value order of evaluation to achieve laziness.
The `↓` modifier ensures that {name}`evalListHead` fires before the arguments to {name}`List.head?` are evaluated.
It rewrites {lean}`List.head? (a :: as)` to {lean}`some a` using {name}`List.head?_cons`, discarding the tail {lean}`as` without evaluating it.
Only the head element {lean}`a` is subsequently reduced by {tactic}`cbv`.

```lean
cbv_simproc ↓ evalListHead (List.head? _) := fun e => do
  let_expr List.head? α listExpr := e | return .rfl
  let_expr List.cons _ a as := listExpr | return .rfl
  let Level.succ u ← Sym.getLevel α | return .rfl
  let result ← Sym.share <| mkApp2 (mkConst ``Option.some [u]) α a
  let proof := mkApp3 (mkConst ``List.head?_cons [u]) α a as
  return .step result proof

theorem cbv_simproc_test : [5 + 5,6].head? = .some 10 := by cbv
```
Inspecting the proof term confirms that the simplification procedure fired: {name}`List.head?_cons` appears directly in the proof, showing that {tactic}`cbv` used the simproc's rewrite rather than reducing {name}`List.head?` by unfolding its definition.

```lean -show (name := cbvSimprocTest)
#print cbv_simproc_test
```
```leanOutput cbvSimprocTest
theorem cbv_simproc_test : [5 + 5, 6].head? = some 10 :=
of_eq_true
  (Eq.trans (congrFun' (congrArg Eq (Eq.trans List.head?_cons (congrArg some (Eq.refl 10)))) (some 10))
    (eq_self (some 10)))
```

::::

:::paragraph
Lean includes a number of built-in simplification procedures for {tactic}`cbv`.
These handle control flow (`ite`, `dite`, `cond`, `Decidable.decide`, `Decidable.rec`), logical connectives (`Or`, `And`), and data structure operations (array indexing, string operations).
The control flow procedures use the `↓` (pre) phase to enable short-circuit evaluation, while the array and string procedures use the `cbv_eval` phase to reduce ground applications directly.
:::

## Options

{optionDocs cbv.maxSteps}

{optionDocs cbv.warning}

# Controlling Reduction
%%%
tag := "tactic-reducibility"
%%%

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic "with_unfolding_all"
:::

:::tactic "with_unfolding_none"
:::


# Control Flow
%%%
tag := "tactic-ref-control"
%%%


:::tactic "skip"
:::


:::tactic Lean.Parser.Tactic.guardHyp
:::

:::tactic Lean.Parser.Tactic.guardTarget
:::

:::tactic Lean.Parser.Tactic.guardExpr
:::

:::tactic "done"
:::

:::tactic "sleep"
:::

:::tactic "stop"
:::


# Term Elaboration Backends
%%%
tag := "tactic-ref-term-helpers"
%%%


These tactics are used during elaboration of terms to satisfy obligations that arise.

:::tactic tacticDecreasing_with_
:::

:::tactic "get_elem_tactic"
:::

:::tactic "get_elem_tactic_trivial"
:::


# Debugging Utilities
%%%
tag := "tactic-ref-debug"
%%%


:::tactic "sorry"
:::

:::tactic "admit"
:::

:::tactic "dbg_trace"
:::

:::tactic Lean.Parser.Tactic.traceState
:::

:::tactic Lean.Parser.Tactic.traceMessage
:::

# Suggestions

:::tactic "∎"
:::

:::tactic "suggestions"
:::


# Other
%%%
tag := "tactic-ref-other"
%%%

The {tactic}`trivial` tactic tries a short list of simple tactics, including {tactic}`rfl`, {tactic}`assumption`, and {lean}`True.intro`, to close the goal.

:::tactic "trivial"
:::

:::example "Closing Easy Goals"
The {tactic}`trivial` tactic can close goals that are trivial from the point of view of propositional logic.
```lean
example : True := by trivial
```
```lean
example (h : P) : P := by trivial
```
:::

:::tactic "solve"
:::

:::tactic "and_intros"
:::

:::tactic "infer_instance"
:::

:::tactic "expose_names"
:::

:::tactic Lean.Parser.Tactic.tacticUnhygienic_
:::

:::tactic Lean.Parser.Tactic.runTac
:::

# Verification Condition Generation
%%%
tag := "tactic-ref-mvcgen"
%%%

:::tactic "mvcgen"
:::

## Tactics for Stateful Goals in `Std.Do.SPred`
%%%
tag := "tactic-ref-spred"
%%%

### Starting and Stopping the Proof Mode

:::tactic "mstart"
:::

:::tactic "mstop"
:::

:::tactic "mleave"
:::

### Proving a Stateful Goal

:::tactic "mspec"
:::

:::tactic Lean.Parser.Tactic.mintroMacro
:::

:::tactic "mexact"
:::

:::tactic "massumption"
:::

:::tactic "mrefine"
:::

:::tactic "mconstructor"
:::

:::tactic "mleft"
:::

:::tactic "mright"
:::

:::tactic "mexists"
:::

:::tactic "mpure_intro"
:::

:::tactic "mexfalso"
:::

### Manipulating Stateful Hypotheses

:::tactic "mclear"
:::

:::tactic "mdup"
:::

:::tactic "mhave"
:::

:::tactic "mreplace"
:::

:::tactic "mspecialize"
:::

:::tactic "mspecialize_pure"
:::

:::tactic "mcases"
:::

:::tactic "mrename_i"
:::

:::tactic "mpure"
:::

:::tactic "mframe"
:::
