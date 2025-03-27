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

set_option pp.rawOnError true

set_option linter.unusedVariables false

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

:::tactic Lean.Parser.Tactic.assumption
:::

:::tactic "apply_assumption"
:::

# Quantifiers
%%%
tag := "tactic-ref-quantifiers"
%%%

:::tactic "exists"
:::

:::tactic "intro"
:::


:::tactic "intros"
:::

:::tactic Lean.Parser.Tactic.introMatch (show := "intro | ... => ... | ... => ...")
:::

:::tactic "rintro"
:::


# Relations
%%%
tag := "tactic-ref-relations"
%%%

:::tactic "rfl"
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

:::tactic "symm"
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

:::tactic "calc"
:::

{docstring Trans}

## Equality
%%%
tag := "tactic-ref-equality"
%%%

:::tactic "subst"
:::

:::tactic "subst_eqs"
:::

:::tactic "subst_vars"
:::

:::tactic "congr"
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

:::tactic "exact"
:::

:::tactic "apply"
:::

:::tactic "refine"
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

:::tactic "exfalso"
:::

:::tactic "contradiction"
:::

:::tactic Lean.Parser.Tactic.falseOrByContra
:::


# Goal Management
%%%
tag := "tactic-ref-goals"
%%%

:::tactic "suffices"
:::

:::tactic "change"
:::

:::tactic Lean.Parser.Tactic.changeWith show:="change ... with ..."
:::

:::tactic "generalize"
:::

:::tactic "specialize"
:::

:::tactic "obtain"
:::

:::tactic "show"
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

# Extensionality
%%%
tag := "tactic-ref-ext"
%%%

:::tactic "ext"
:::

:::tactic Lean.Elab.Tactic.Ext.tacticExt1___
:::

:::tactic Lean.Elab.Tactic.Ext.applyExtTheorem
:::

:::tactic "funext"
:::

{include 0 Manual.Tactics.Reference.Simp}

# Rewriting
%%%
tag := "tactic-ref-rw"
%%%

:::tactic "rw"
:::

:::tactic "rewrite"
:::

:::tactic "erw"
:::

:::tactic Lean.Parser.Tactic.tacticRwa__
:::

{docstring Lean.Meta.Rewrite.Config (allowMissing := true)}

{docstring Lean.Meta.Occurrences (allowMissing := true)}

{docstring Lean.Meta.TransparencyMode (allowMissing := true)}

{docstring Lean.Meta.Rewrite.NewGoals (allowMissing := true)}


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

:::tactic "constructor"
:::


:::tactic "injection"
:::

:::tactic "injections"
:::

:::tactic "left"
:::

:::tactic "right"
:::

## Elimination
%%%
tag := "tactic-ref-inductive-elim"
%%%

:::planned 48

Description of the `@[induction_eliminator]` and `@[cases_eliminator]` attributes

:::

:::tactic "cases"
:::

:::tactic "rcases"
:::

:::tactic "fun_cases"
:::

:::tactic "induction"
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
{goal show:=false}`∀ (i j k : Nat), i < j → j < k → i < k`
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
Try this: exact Nat.lt_trans h1 h2
```

```post (show := false)

```
:::


:::tactic "rw?"
:::

# Case Analysis
%%%
tag := "tactic-ref-cases"
%%%


:::tactic "split"
:::

:::tactic "by_cases"
:::

# Decision Procedures
%%%
tag := "tactic-ref-decision"
%%%


:::tactic Lean.Parser.Tactic.decide show:="decide"
:::

:::tactic Lean.Parser.Tactic.nativeDecide show:="native_decide"
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

:::tactic Lean.Parser.Tactic.bvTrace
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


# Other
%%%
tag := "tactic-ref-other"
%%%

:::tactic "trivial"
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
