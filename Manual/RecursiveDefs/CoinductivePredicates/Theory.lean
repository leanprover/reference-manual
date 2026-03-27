/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Różowski
-/

import VersoManual

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order


#doc (Manual) "Theory and Construction" =>
%%%
tag := "coinductive-theory"
%%%

The construction of coinductive and inductive predicates builds on the Knaster-Tarski fixpoint theorem for complete lattices.
While {ref "partial-fixpoint-theory"}[partial fixpoint recursion] relies on chain-complete partial orders ({name}`Lean.Order.CCPO`), coinductive and inductive predicates use the stronger notion of a {deftech}_complete lattice_.

# Complete Lattices
%%%
tag := "complete-lattices"
%%%

A {tech}[complete lattice] is a partial order where every subset has a least upper bound, not just every chain.

{docstring Lean.Order.CompleteLattice +allowMissing}

Every complete lattice gives rise to a CCPO, since every chain is in particular a subset, but the converse does not hold in general.
For instance, the flat order on an inhabited type (used by {ref "partial-fixpoint"}[partial fixpoints] for tail-recursive functions) is a CCPO but not a complete lattice.

In a complete lattice, the least fixpoint of a monotone function can be constructed directly as the infimum of all pre-fixpoints, following the Knaster-Tarski theorem:

{docstring Lean.Order.lfp +allowMissing}

{docstring Lean.Order.lfp_fix +allowMissing}

The corresponding induction principle is Park induction: to show that a property holds for all elements of the least fixpoint, it suffices to show that the property is preserved by one application of the defining function.

{docstring Lean.Order.lfp_le_of_le_monotone +allowMissing}

# Lattice Structure on Propositions
%%%
tag := "lattice-prop"
%%%

The type {lean}`Prop` admits two natural complete lattice structures, each giving rise to a different kind of fixpoint:

:::paragraph

 * {name}`Lean.Order.ImplicationOrder` orders propositions by implication: `P ⊑ Q` means `P → Q`.
   The least fixpoint in this order yields the smallest predicate closed under the defining rules, corresponding to an {deftech (key := "lattice-theoretic inductive predicate")}_inductive predicate_.
   This is the order used by {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint`.

 * {name}`Lean.Order.ReverseImplicationOrder` orders propositions by reverse implication: `P ⊑ Q` means `Q → P`.
   The least fixpoint in this _reversed_ order is the _greatest_ fixpoint in the standard order, yielding the largest predicate consistent with the defining rules.
   This corresponds to a {deftech (key := "lattice-theoretic coinductive predicate")}_coinductive predicate_.
   This is the order used by {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint`.

:::

Arrow types into a complete lattice inherit a complete lattice structure, and products of complete lattices are complete lattices.
These closure properties allow extending the construction to predicates of arbitrary arity and to mutual blocks.

# Monotonicity
%%%
tag := "coinductive-monotonicity"
%%%

Defining a predicate as a fixpoint requires the defining equation to be monotone with respect to the appropriate order.

For the {keywordOf Lean.Parser.Command.declaration}`coinductive` command, monotonicity is guaranteed by construction: the kernel's strict positivity check on the underlying {ref "coinductive-elaboration"}[flat inductive] ensures that every accepted definition is monotone.
Users do not need to concern themselves with monotonicity when using this syntax.

For the {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` and {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` termination clauses, the monotonicity requirement is semantic rather than syntactic.
The {tactic}`monotonicity` tactic proves monotonicity by composing lemmas registered with the {attr}`partial_fixpoint_monotone` attribute.
This approach is more permissive than strict positivity.
For example, negation and implication are handled correctly by flipping the order between {name}`Lean.Order.ImplicationOrder` and {name}`Lean.Order.ReverseImplicationOrder`.
This is what allows mixing inductive and coinductive fixpoints in the same {tech}[mutual block].

The set of constructs handled by the {tactic}`monotonicity` tactic is extensible: registering additional {attr}`partial_fixpoint_monotone` lemmas teaches the tactic to handle new logical connectives or higher-order functions.
Alternatively, an explicit monotonicity proof term can be provided.

See the {ref "partial-fixpoint-theory"}[theory section of partial fixpoints] for the full list of registered monotonicity lemmas and for more detail on the monotonicity tactic.
