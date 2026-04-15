/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Różowski
-/

import VersoManual

import Manual.Meta
import Manual.RecursiveDefs.CoinductivePredicates.CoinductiveSyntax
import Manual.RecursiveDefs.CoinductivePredicates.Theory

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

set_option maxRecDepth 600


#doc (Manual) "Coinductive and Inductive Predicates" =>
%%%
tag := "coinductive-predicates"
%%%

Lean's type theory does not support coinductive types directly.
However, {deftech (key := "lattice-theoretic coinductive predicate")}[coinductive predicates], that is, recursive definitions valued in {lean}`Prop`, can be defined using the complete lattice structure on propositions.
These predicates provide a coinductive reasoning principle, in which a universally quantified instance of a predicate is shown to be true by demonstrating that its truth for a larger structure implies its truth for smaller structures.
This is the opposite of inductive reasoning, in which the truth of a predicate for smaller values is shown to guarantee its truth for larger values.
Coinductive predicates allow infinite domains to be specified and reasoned about.
Dually, {deftech (key := "lattice-theoretic inductive predicate")}[inductive predicates] can also be defined via least fixpoints using the same machinery.
Because it uses the same underlying mechanisms, this alternative to ordinary {tech}[inductive types] is compatible with mixed inductive-coinductive mutual blocks.

::::::example "Infinite Sequences" (open := true)

::::leanSection
```lean -show
variable {R : α → α → Prop} (x y : α) {pred : α → Prop}
```
:::paragraph
Given a relation {lean}`R` on {lean}`α` (that is, with type {lean}`α → α → Prop`), there is an infinite sequence of values in {lean}`α` starting at {lean}`x` if:

 * there exists some {lean}`y` such that {lean}`R x y`, and
 * there exists an infinite sequence from {lean}`y`.

This is a quintessential coinductive predicate: it describes a potentially infinite behavior that can be presented as a single inference rule with no base cases.
:::
::::

This recursive specification is well-defined, but it cannot be defined as an ordinary recursive function because the recursive part of the definition does not decrease.
However, it is a perfectly sensible coinductive definition:
```lean
coinductive InfSeq (R : α → α → Prop) : α → Prop where
  | step (y : α) : R x y →  InfSeq R y → InfSeq R x
```

:::leanSection
```lean -show
variable {R : α → α → Prop} (a : α) {pred : α → Prop}
```

The coinductive reasoning principle takes a predicate {lean}`pred`.
To prove that {lean}`a` is the start of an infinite {lean}`R`-sequence, it suffices to show that {lean}`R` relates each element that satisfies {lean}`pred` to some other such element.
In other words, it that the presence of an infinite sequence can be demonstrated by providing one:
```signature
InfSeq.coinduct (R : α → α → Prop) (pred : α → Prop) :
  (∀ (a : α), pred a → ∃ y, R a y ∧ pred y) →
  ∀ (a : α), pred a → InfSeq R a
```
:::
::::::




There are two ways to define coinductive predicates in Lean:

 1. Using the {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` termination clause on a recursive {keywordOf Lean.Parser.Command.declaration}`def` valued in {lean}`Prop`, which takes the greatest fixpoint. Equivalently, the {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` clause defines inductive predicates as least fixpoints.

 2. Using the {keywordOf Lean.Parser.Command.coinductive}`coinductive` command, which provides a declarative syntax mirroring {keywordOf Lean.Parser.Command.inductive}`inductive` declarations.


# Fixpoint Termination Clauses
%%%
tag := "fixpoint-clauses"
%%%

A recursive {lean}`Prop`-valued function can be defined as a fixpoint by annotating it with {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` for coinductive definitions (greatest fixpoint) or {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` for inductive definitions (least fixpoint).
These termination clauses play the same role as {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` but use the {ref "lattice-prop"}[complete lattice structure on `Prop`] to compute the appropriate fixpoint.

## Coinductive Fixpoint
%%%
tag := "coinductive-fixpoint-clause"
%%%

:::leanSection
```lean -show
variable {P Q : ReverseImplicationOrder}
```
The {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` clause defines a predicate as the greatest fixpoint of its defining equation.
The function must be monotone with respect to {name}`Lean.Order.ReverseImplicationOrder`, in which {lean}`P ⊑ Q` means {lean}`Q → P`.
:::

:::leanSection
```lean -show
variable {P Q : α → ReverseImplicationOrder}
example : (P ⊑ Q) = (∀ x, P x ⊑ Q x) := rfl
example : (∀ x, P x ⊑ Q x) = (∀ x, Q x → P x) := rfl
```
This ordering is extended pointwise over the predicate's domain.
Given predicates {lean}`P` and {lean}`Q` over {lean}`α`, {lean}`P ⊑ Q` means {lean}`∀ x : α, P x ⊑ Q x` (that is, {lean}`∀ x, Q x → P x`).
:::

::::example "Monotonicity of Infinite Sequences"
```lean -show
variable (R : α → α → Prop) {a : α}
```
The proposition {lean}`InfSeq R a` is true when there exists an infinite chain of {lean}`R`-related elements starting from {lean}`a`.
This can be written using {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint`:

```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

During elaboration, the first step is to abstract this recursive definition over the recursive calls, yielding a definition equivalent to {lean}`F`:
```lean
def F (R : α → α → Prop) (a : α) (P : α → Prop) : Prop :=
  ∃ b, R a b ∧ P b
```

:::leanSection
```lean -show
variable (P Q : α → Prop) (R : α → α → Prop)
```
For this function to be monotone with respect to reverse implication, it must preserve the reverse implication ordering between {lean}`P` and {lean}`Q`.
That is, {lean}`∀ (x : α), Q x → P x` must imply {lean}`∀ (x : α), F R x Q → F R x P`:
:::
```lean
theorem F_monotone
    (h : ∀ (x : α), Q x → P x) :
    ∀ (x : α), F R x Q → F R x P := by
  grind [F]
```
::::

:::example "Failure of Monotonicity"

An element is accessible in a relation if there is no infinite chain leading to the element.
This property is inductively defined as {name}`Acc` in the standard library.
This attempt to define it coinductively fails:
```lean +error (name := nonmono)
def NoInfChain (R : α → α → Prop) (x : α) : Prop :=
  ∀ y, R x y → ¬NoInfChain R y
coinductive_fixpoint
```

```leanOutput nonmono
Could not prove 'NoInfChain' to be monotone in its recursive calls:
  Cannot eliminate recursive call in
    NoInfChain R y✝
```

The corresponding function is:
```lean
def F (R : α → α → Prop) (x : α) (P : α → Prop) : Prop :=
  ∀ y, R x y → ¬P y
```

Lean failed to prove this function monotone because it is not, in fact, monotone:
```lean
theorem F_nonmonotone :
    ¬(∀ α R P Q,
      (∀ (x : α), Q x → P x) →
      (∀ (x : α), F R x Q → F R x P)) := by
  suffices ∃ α R P Q,
      ¬((∀ (x : α), Q x → P x) →
        (∀ (x : α), F R x Q → F R x P)) by
    simpa
  -- α = PUnit, R always true
  refine ⟨PUnit, fun _ _ => True, ?_⟩
  -- P is trivially true, Q is always false
  refine ⟨fun _ => True, fun _ => False, ?_⟩
  simp [F]
```
:::

:::example "Non-Predicates"

An infinite conjunction of some proposition can be defined as a coinductive fixpoint:
```lean
def InfConj (p : Prop) : Prop := p ∧ InfConj p
coinductive_fixpoint
```

This cannot be used to define an infinite product, however:
```lean +error (name := nonprop)
def InfProd (α : Type) : Prop := α × InfProd α
coinductive_fixpoint
```
The error message indicates that a proposition was expected:
```leanOutput nonprop
Application type mismatch: The argument
  InfProd α
has type
  Prop
of sort `Type` but is expected to have type
  Type ?u.6
of sort `Type (?u.6 + 1)` in the application
  α × InfProd α
```

:::

Just as with definitions via partial fixpoints, the coinductive predicate's defining equations do not hold definitionally.
However, the elaborator proves equational lemmas that allow the predicate to be rewritten to its unfolding.

:::example "Definitional Equality and Coinductive Predicates"
{lean}`InfSeq` is the coinductive statement that an relation starts an infinite chain:
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

Because it is defined using {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint`, it is not definitionally equal to its unfolding:
```lean +error (name := nondefeq)
example (R : α → α → Prop) (a : α) :
    InfSeq R a = ∃ b, R a b ∧ InfSeq R b := by
  rfl
```
```leanOutput nondefeq
Tactic `rfl` failed: The left-hand side
  InfSeq R a
is not definitionally equal to the right-hand side
  ∃ b, R a b ∧ InfSeq R b

α : Sort u_1
R : α → α → Prop
a : α
⊢ InfSeq R a = ∃ b, R a b ∧ InfSeq R b
```

However, it is equipped with equational lemmas that allow it to be rewritten to its unfolding:
```lean
example (R : α → α → Prop) (a : α) :
    InfSeq R a = ∃ b, R a b ∧ InfSeq R b := by
  rw [InfSeq]
```

:::

In addition to equational lemmas, Lean generates a {deftech}[coinduction principle].
The coinduction principle states that the coinductive predicate can be proved by exhibiting some other predicate that is a post-fixpoint of the monotone function.

::::example "Coinduction Principles for Infinite Sequences"
{lean}`InfSeq` is the coinductive statement that an relation starts an infinite chain:
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

The corresponding monotone function is:
```lean
def F (R : α → α → Prop) (a : α) (P : α → Prop) : Prop :=
  ∃ b, R a b ∧ P b
```

:::leanSection
```lean -show
variable {R : α → α → Prop} {a : α} {P : α → Prop}
```
Because {lean}`InfSeq` is the _greatest_ fixpoint of {lean}`F`, the existence of _any_ predicate that is less than its image in {lean}`F` suffices to show that every element that satisfies the predicate also satisfies {lean}`InfSeq`.
In other words, to prove {lean}`InfSeq R a`, it suffices to demonstrate a predicate {lean}`P` such that {lean}`∀ (a : α), P a → F R a P`, or {lean}`∀ (a : α), P a → ∃ b, R a b ∧ P b`, and then show {lean}`P a`.
:::
This coinduction principle is named {lean}`InfSeq.coinduct`:
```signature
InfSeq.coinduct {α} (R : α → α → Prop) (pred : α → Prop) :
  (∀ (a : α), pred a → ∃ b, R a b ∧ pred b) →
  ∀ (a : α), pred a → InfSeq R a
```
::::

::::example "Simple Proof by Coinduction"
{lean}`InfSeq` states that there is an infinite sequence of elements in a relation, with a given starting point:
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

:::leanSection
```lean -show
variable {R : α → α → Prop} {a : α}
```
If {lean}`R a a` holds, then there is a trivial infinite chain that loops at {lean}`a`:

```lean
theorem cycle_InfSeq {R : α → α → Prop} (a : α) :
    R a a → InfSeq R a := by
  apply InfSeq.coinduct (pred := fun m => R m m)
  intro x h
  exact ⟨x, h, h⟩
```
:::
::::

:::example "Infinite Chains of Less-Than"
{lean}`InfSeq` states that there is an infinite sequence of elements in a relation, with a given starting point:
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

There is an infinite chain of natural numbers related by {lean (type := "Nat → Nat → Prop")}`(· < ·)`.
All natural numbers start such a chain, so the predicate can be trivial:
```lean
theorem lt_InfSeq {n : Nat} : InfSeq (· < ·) n := by
  apply InfSeq.coinduct (pred := fun x => True)
  . intro k _
    refine ⟨k + 1, ?_⟩
    simp
  . trivial
```
:::

::::example "DFA Language Equivalence"
Coinductive predicates naturally capture bisimulation-like notions.

:::leanSection
```lean -show
variable {Q : Type} {A : Type} {q : Q}
```
A deterministic finite automaton is given by a set of states {lean}`Q`, an alphabet {lean}`A`, a start state {lean}`q` in {lean}`Q`, a subset of {lean}`Q` the define accepting states, and a transition function that takes a state and an element of the alphabet to a new state:
:::
```lean
structure DFA (Q : Type) (A : Type) : Type where
  q₀ : Q
  δ : Q → A → Q
  accepting : Q → Bool
```

Two automata over the same alphabet have equivalent languages from a given pair of states when they agree as to whether these states are accepting and they furthermore have equivalent languages from all successor states according to their transition functions:
```lean
def languageEquivalent (M : DFA Q A) (M' : DFA Q' A)
    (q : Q) (q' : Q') : Prop :=
  M.accepting q = M'.accepting q' ∧
    ∀ (a : A), languageEquivalent M M' (M.δ q a) (M'.δ q' a)
coinductive_fixpoint
```

The coinduction principle captures the standard notion of bisimulation of deterministic automata:
```signature
languageEquivalent.coinduct  {Q A Q' : Type} (M : DFA Q A) (M' : DFA Q' A) (pred : Q → Q' → Prop) :
  (∀ (q : Q) (q' : Q'), pred q q' → M.accepting q = M'.accepting q' ∧ ∀ (a : A), pred (M.δ q a) (M'.δ q' a)) →
    ∀ (q : Q) (q' : Q'), pred q q' → languageEquivalent M M' q q'
```

It can be used to prove that these two DFAs have equivalent languages
```diagram
open Illuminate in
let cfg : StateDiagramConfig := {}
cfg.start 0 |>.atop
(cfg.accept 0 "ok") |>.atop
(cfg.state 1 "fail") |>.atop
(cfg.loop 0 "a") |>.atop
(cfg.loop 1 "a, b") |>.atop
(cfg.edge 0 1 "b")
```

```diagram
open Illuminate in
let cfg : StateDiagramConfig := {}
cfg.start 0 |>.atop
(cfg.accept 0 "start") |>.atop
(cfg.accept 1 "ok") |>.atop
(cfg.state 2 "fail") |>.atop
(cfg.arc 0 1 "a" 30) |>.atop
(cfg.arc 1 0 "a" (-30)) |>.atop
(cfg.edge 1 2 "b") |>.atop
(cfg.arc 0 2 "b" (-140)) |>.atop
(cfg.loop 2 "a, b")
```

These DFAs can be represented using the following definitions:
```lean
inductive Alphabet where | a | b

inductive Q1 where | ok | fail

def loop : DFA Q1 Alphabet where
  q₀ := .ok
  δ
    | .ok, .a => .ok
    | _, _ => .fail
  accepting
    | .ok => True
    | _ => False

inductive Q2 where | start | ok | fail

def cycle : DFA Q2 Alphabet where
  q₀ := .start
  δ
    | .start, .a => .ok
    | .ok, .a => .start
    | _, _ => .fail
  accepting
    | .start | .ok => True
    | .fail => False
```

To prove that they are equivalent, the first step is to define a relation that captures their equivalent states.
Then, coinduction lifts the demonstration that they actually are equivalent in this relation to language equivalence:
```lean
theorem loop_equiv_cycle :
    languageEquivalent loop cycle loop.q₀ cycle.q₀ := by
  let r : Q1 → Q2 → Prop
  | .ok, .start
  | .ok, .ok
  | .fail, .fail => True
  | _, _ => False
  apply languageEquivalent.coinduct (pred := r)
  . intro q q'
    cases q <;> cases q' <;>
    simp only [loop, cycle] <;>
    grind
  . simp [r, loop, cycle]
```
::::

## Inductive Fixpoint
%%%
tag := "inductive-fixpoint-clause"
%%%

The {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` clause defines a predicate as the least fixpoint of its defining equation.
The function must be monotone with respect to {name}`Lean.Order.ImplicationOrder`, the order on {lean}`Prop` where `P ⊑ Q` means `P → Q`.
This provides an alternative to ordinary {keywordOf Lean.Parser.Command.declaration}`inductive` type declarations for predicates, and is the dual of {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint`.

In most cases, an ordinary inductive type declaration is more convenient.
However, inductive fixpoint definitions have two key advantages over ordinary inductive type declarations that make them more suitable for certain specialized use cases:
 * Ordinary inductive type declarations have a _syntactic_ positivity condition, where recursive occurrences of the inductive type cannot occur in negative positions. Inductive fixpoints instead require monotonicity, which is a _semantic_ condition.
 * Inductive fixpoints can be defined mutually with coinductive fixpoints, allowing mixed inductive-codinductive predicates.

For each inductive fixpoint definition, an induction principle is automatically proven.
This induction principle has the same logical strength as the corresponding induction principle that would be generated for an inductive type declaration, but it is formulated somewhat differently and must be explicitly applied.

Just as with coinductive fixpoints, inductive fixpoint definitions do not definitionally reduce.
They can be unfolded using their generated equational lemmas, and their induction principles allow them to be used in proofs.

:::example "Reflexive Transitive Closures as Inductive Fixpoints"
The reflexive transitive closure of a relation can be defined as an inductive predicate:
```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```

The same predicate can be defined as a least fixpoint.
```lean
def StarInd (tr : α → α → Prop) (q₁ q₂ : α) : Prop :=
  q₁ = q₂ ∨ ∃ (z : α), (tr q₁ z ∧ StarInd tr z q₂)
inductive_fixpoint
```

An induction principle is generated:
```signature
StarInd.induct (tr : α → α → Prop) (q₂ : α) (pred : α → Prop)
  (hyp : ∀ (q₁ : α), (q₁ = q₂ ∨ ∃ z, tr q₁ z ∧ pred z) → pred q₁) (q₁ : α) :
  StarInd tr q₁ q₂ → pred q₁
```

The induction principle can be used to prove that the two formulations are equivalent:
```lean -keep
theorem star_implies_starInd (R : α → α → Prop) :
    ∀ a b : α, Star R a b = StarInd R a b := by
  intro a b
  ext
  constructor
  . intro h
    induction h <;> grind [StarInd]
  . apply StarInd.induct R b (Star R · b) ?_ a
    grind [Star]
```
:::

## Mixed Inductive-Coinductive Predicates in Mutual Blocks
%%%
tag := "mixed-mutual-fixpoint"
%%%

A {tech}[mutual block] can mix {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` and {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` clauses.
Every definition in the block must use one of these two clauses.
The construction uses two {ref "lattice-prop"}[lattice structures on `Prop`]: {name}`Lean.Order.ImplicationOrder` for inductive definitions and {name}`Lean.Order.ReverseImplicationOrder` for coinductive definitions.
In both cases, the least fixpoint of the corresponding lattice is computed; using the reverse implication order, the least fixpoint coincides with the greatest fixpoint in the standard order.
This is possible because {ref "coinductive-monotonicity"}[monotonicity] lemmas flip between the two orders when negation or implication is encountered.

:::example "Mixed Inductive-Coinductive Mutual Block"
```lean
mutual
  def tick : Prop :=
    ¬tock
  coinductive_fixpoint

  def tock : Prop :=
    ¬tick
  inductive_fixpoint
end
```

A mutual induction principle is generated for the first definition in the mutual block:
```signature
tick.mutual_induct (pred_1 pred_2 : Prop) :
  (pred_1 → pred_2 → False) → ((pred_1 → False) → pred_2) →
  (pred_1 → tick) ∧ (tock → pred_2)
```
:::


# Examples
%%%
tag := "coinductive-predicate-examples"
%%%

```lean -show
namespace ProofTechniques
```

:::example "Infinite Chains from Universal Reachability"
If every state reachable from `a` via the reflexive transitive closure has a successor, then there is an infinite chain from `a`:

```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```

```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

```lean
def allSeqInf (R : α → α → Prop) (x : α) : Prop :=
  ∀ y : α, Star R x y → ∃ z, R y z

theorem infSeq_of_allSeqInf (R : α → α → Prop) :
    ∀ x, allSeqInf R x → InfSeq R x := by
  apply InfSeq.coinduct
  intro x H
  unfold allSeqInf at H
  have H' := H x (.refl x)
  obtain ⟨y, Rxy⟩ := H'
  exact ⟨y, Rxy,
    fun y' Ryy' =>
      H y' (.step x y y' Rxy Ryy')⟩
```
:::


:::example "Coinduction Up-To Transitive Closure"
A strengthened coinduction principle allows the coinduction hypothesis to be applied up to transitive closure.
Given a predicate {lean}`X` such that every {lean}`X`-state leads via one-or-more {lean}`R`-steps to another {lean}`X`-state, then every {lean}`X`-state satisfies {lean}`InfSeq R`:

```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```

```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

```lean
variable {α : Sort _} {R : α → α → Prop}

inductive plus (R : α → α → Prop) :
    α → α → Prop where
  | left : ∀ a b c,
      R a b → Star R b c → plus R a c

theorem plusStar (a b : α) :
    plus R a b → Star R a b := by
  intro h; cases h
  case left _ h₂ h₃ =>
    exact Star.step _ _ _ h₂ h₃

theorem plusStarTrans (a b c : α) :
    Star R a b → plus R b c →
    plus R a c := by
  intro s p; induction s
  case refl => exact p
  case step d e _ rel _ ih =>
    exact plus.left _ _ _ rel
      (plusStar _ _ (ih p))

variable (X : α → Prop)

theorem infSeqCoinductionUpTo :
    (∀ (a : α), X a →
      ∃ b, plus R a b ∧ X b) →
    ∀ (a : α), X a → InfSeq R a := by
  intro h₁ a rel
  apply @InfSeq.coinduct _ _
    (fun a => ∃ b, Star R a b ∧ X b)
  case x =>
    obtain ⟨a', h₁, h₂⟩ := h₁ a rel
    exact ⟨a', plusStar _ _ h₁, h₂⟩
  case hyp =>
    intro a0 ⟨a1, h₃, h₄⟩
    obtain ⟨mid, h₅, h₆⟩ := h₁ a1 h₄
    have t := plusStarTrans a0 a1 mid h₃ h₅
    cases t
    case left mid2 rel2 s =>
      exact ⟨mid2, rel2, mid, s, h₆⟩
```
:::

```lean -show
end ProofTechniques
```


{include 0 Manual.RecursiveDefs.CoinductivePredicates.CoinductiveSyntax}

{include 0 Manual.RecursiveDefs.CoinductivePredicates.Theory}
