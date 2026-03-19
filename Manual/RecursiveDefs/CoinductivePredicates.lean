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
However, {tech (key := "lattice-theoretic coinductive predicate")}[coinductive predicates], that is, recursive definitions valued in {lean}`Prop`, can be defined using the complete lattice structure on propositions.
Dually, {tech (key := "lattice-theoretic inductive predicate")}[inductive predicates] can also be defined via least fixpoints using the same machinery, providing an alternative to ordinary {tech}[inductive types] that is compatible with mixed inductive-coinductive mutual blocks.

The key idea is that {lean}`Prop` carries a {ref "complete-lattices"}[complete lattice] structure ordered by implication (`P ⊑ Q` when `P → Q`), and any monotone endofunction on a complete lattice has both a least and a greatest fixpoint by the Knaster-Tarski theorem.
Coinductive predicates use the {ref "lattice-prop"}[reverse implication order] (`P ⊑ Q` when `Q → P`), so that the least fixpoint in this reversed order is the greatest fixpoint in the standard order.
For predicates of the form `α → Prop`, the pointwise lifting of this lattice structure to function types provides the necessary setting.
For mutual blocks, the product of complete lattices is again a complete lattice.
This construction shares its internals with the {ref "partial-fixpoint"}[partial fixpoint] machinery.

There are two ways to define coinductive predicates in Lean:

 1. Using the {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` termination clause on a recursive {keywordOf Lean.Parser.Command.declaration}`def` valued in {lean}`Prop`, which takes the greatest fixpoint. Equivalently, the {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` clause defines inductive predicates as least fixpoints.

 2. Using the {keywordOf Lean.Parser.Command.declaration}`coinductive` command, which provides a declarative syntax mirroring {keywordOf Lean.Parser.Command.declaration}`inductive` declarations.


# Running Example: Infinite Sequences
%%%
tag := "infseq-running-example"
%%%

Throughout this section, the predicate `infSeq` serves as a running example.
Given a relation `R : α → α → Prop`, the predicate `infSeq R a` asserts that there exists an infinite chain of `R`-related elements starting from `a`.
This is a quintessential coinductive predicate: it describes a potentially infinite behavior that can be presented as a single inference rule with no base cases.


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

The {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` clause defines a predicate as the greatest fixpoint of its defining equation.
The function must be monotone with respect to {name}`Lean.Order.ReverseImplicationOrder`.

The predicate `infSeq R a` holds when there exists an infinite chain of `R`-related elements starting from `a`.

```lean
def infSeq (R : α → α → Prop) : α → Prop :=
  fun a => ∃ b, R a b ∧ infSeq R b
coinductive_fixpoint
```

The defining equation can be used as a rewrite rule:
```lean
theorem infSeq.unfold_example
    (R : α → α → Prop) (a : α) :
    infSeq R a = ∃ b, R a b ∧ infSeq R b := by
  rw [infSeq]
```

Lean generates a coinduction principle.
To prove `infSeq R a`, it suffices to exhibit a predicate `pred` such that `pred a` holds and `pred` is a post-fixpoint: whenever `pred x` holds, there exists a `y` with `R x y` and `pred y`.

```lean (name := checkInfSeqCoinductDef)
#check @infSeq.coinduct
```
```leanOutput checkInfSeqCoinductDef
@infSeq.coinduct : ∀ {α : Sort u_1} (R : α → α → Prop) (pred : α → Prop),
  (∀ (a : α), pred a → ∃ b, R a b ∧ pred b) → ∀ (a : α), pred a → infSeq R a
```

:::example "Simple Proof by Coinduction"
If `R a a` holds, then there is a trivial infinite chain that loops at `a`:

```lean -keep
theorem cycleInfSeq {R : α → α → Prop} (a : α) :
    R a a → infSeq R a := by
  apply infSeq.coinduct (pred := fun m => R m m)
  intro x _
  exact ⟨x, ‹_›, ‹_›⟩
```
:::

:::example "DFA Language Equivalence"
Coinductive predicates naturally capture bisimulation-like notions.
The following defines language equivalence for deterministic finite automata:

```lean
def DFA (Q : Type) (A : Type) : Type :=
  Q → (Bool × (A → Q))

def languageEquivalent (automaton : DFA Q A)
    (q₁ q₂ : Q) : Prop :=
  let ⟨o₁, t₁⟩ := automaton q₁
  let ⟨o₂, t₂⟩ := automaton q₂
  o₁ = o₂ ∧ (∀ a : A,
    languageEquivalent automaton (t₁ a) (t₂ a))
coinductive_fixpoint
```

The coinduction principle captures the standard notion of bisimulation of deterministic automata:
```lean (name := checkLangEquiv)
#check @languageEquivalent.coinduct
```
```leanOutput checkLangEquiv
@languageEquivalent.coinduct : ∀ {Q A : Type} (automaton : DFA Q A) (pred : Q → Q → Prop),
  (∀ (q₁ q₂ : Q),
      pred q₁ q₂ →
        (automaton q₁).fst = (automaton q₂).fst ∧ ∀ (a : A), pred ((automaton q₁).snd a) ((automaton q₂).snd a)) →
    ∀ (q₁ q₂ : Q), pred q₁ q₂ → languageEquivalent automaton q₁ q₂
```
:::

## Inductive Fixpoint
%%%
tag := "inductive-fixpoint-clause"
%%%

The {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` clause defines a predicate as the least fixpoint of its defining equation.
The function must be monotone with respect to {name}`Lean.Order.ImplicationOrder`, the order on {lean}`Prop` where `P ⊑ Q` means `P → Q`.
This provides an alternative to ordinary {keywordOf Lean.Parser.Command.declaration}`inductive` types for predicates, and is the dual of {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint`.

The reflexive transitive closure of a relation can be defined as an inductive predicate:

```lean
inductive star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, star R x x
  | step : ∀ x y z, R x y → star R y z → star R x z
```

:::example "Reflexive Transitive Closure via `inductive_fixpoint`"
The same predicate can be defined as a least fixpoint:

```lean
def starInd (tr : α → α → Prop) (q₁ q₂ : α) : Prop :=
  ∃ (z : α), q₁ = q₂ ∨ (tr q₁ z ∧ starInd tr z q₂)
inductive_fixpoint
```

An induction principle is generated:
```lean (name := checkStarInduct)
#check @starInd.induct
```
```leanOutput checkStarInduct
@starInd.induct : ∀ {α : Sort u_1} (tr : α → α → Prop) (q₂ : α) (pred : α → Prop),
  (∀ (q₁ : α), (∃ z, q₁ = q₂ ∨ tr q₁ z ∧ pred z) → pred q₁) → ∀ (q₁ : α), (fun q₁ => starInd tr q₁ q₂) q₁ → pred q₁
```

One can prove the correspondence between the two formulations:
```lean -keep
theorem star_implies_starInd (R : α → α → Prop) :
    ∀ a b : α, star R a b → starInd R a b := by
  intro a b s
  induction s
  case refl x =>
    unfold starInd
    exact ⟨x, Or.inl rfl⟩
  case step x y z rel _ ih =>
    unfold starInd
    exact ⟨y, Or.inr ⟨rel, ih⟩⟩
```
:::

## Mixed Mutual Blocks
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
namespace MixedExample
mutual
  def tick : Prop :=
    ¬tock
  coinductive_fixpoint

  def tock : Prop :=
    ¬tick
  inductive_fixpoint
end
end MixedExample
```

A mutual induction principle is generated:
```lean (name := checkMixed)
#check @MixedExample.tick.mutual_induct
```
```leanOutput checkMixed
MixedExample.tick.mutual_induct : ∀ (pred_1 pred_2 : Prop),
  (pred_1 → pred_2 → False) → ((pred_1 → False) → pred_2) → (pred_1 → MixedExample.tick) ∧ (MixedExample.tock → pred_2)
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

```lean -keep
def allSeqInf (R : α → α → Prop) (x : α) : Prop :=
  ∀ y : α, star R x y → ∃ z, R y z

theorem infSeq_of_allSeqInf (R : α → α → Prop) :
    ∀ x, allSeqInf R x → infSeq R x := by
  apply infSeq.coinduct
  intro x H
  unfold allSeqInf at H
  have H' := H x (star.refl x)
  obtain ⟨y, Rxy⟩ := H'
  exact ⟨y, Rxy,
    fun y' Ryy' =>
      H y' (star.step x y y' Rxy Ryy')⟩
```
:::


:::example "Coinduction Up-To Transitive Closure"
A strengthened coinduction principle allows the coinduction hypothesis to be applied up to transitive closure.
Given a predicate `X` such that every `X`-state leads via one-or-more `R`-steps to another `X`-state, then every `X`-state satisfies `infSeq R`:

```lean -keep
variable {α : Sort _} {R : α → α → Prop}

inductive plus (R : α → α → Prop) :
    α → α → Prop where
  | left : ∀ a b c,
      R a b → star R b c → plus R a c

theorem plusStar (a b : α) :
    plus R a b → star R a b := by
  intro h; cases h
  case left _ h₂ h₃ =>
    exact star.step _ _ _ h₂ h₃

theorem plusStarTrans (a b c : α) :
    star R a b → plus R b c →
    plus R a c := by
  intro s p; induction s
  case refl => exact p
  case step d e _ rel _ ih =>
    exact plus.left _ _ _ rel
      (plusStar _ _ (ih p))

theorem infSeqCoinductionUpTo :
    ∀ (X : α → Prop),
    (∀ (a : α), X a →
      ∃ b, plus R a b ∧ X b) →
    ∀ (a : α), X a → infSeq R a := by
  intro X h₁ a rel
  apply @infSeq.coinduct _ _
    (fun a => ∃ b, star R a b ∧ X b)
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
