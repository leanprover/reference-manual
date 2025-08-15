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

# SMT-Inspired Automation
:::tactic "grind"
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

{docstring Lean.Meta.Occurrences}

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

Elimination tactics use {ref "recursors"}[recursors] and the automatically-derived {ref "recursor-elaboration-helpers"}[`casesOn` helper] to implement induction and case splitting.
The {tech}[subgoals] that result from these tactics are determined by the types of the minor premises of the eliminators, and using different eliminators with the {keyword}`using` option results in different subgoals.

:::::leanSection
```lean (show := false)
variable {n : Nat}
```
::::example "Choosing Eliminators"

:::tacticExample
```setup
intro n i
```
{goal show:= false}`∀(n : Nat) (i : Fin (n + 1)), 0 + i = i`

```pre (show := false)
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
{goal show:= false}`∀(n : Nat) (i : Fin (n + 1)), 0 + i = i`

```pre (show := false)
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

The {attr}`induction_eliminator` attribute registers an eliminator for use by the {tactic}`cases` tactic.
```grammar
cases_eliminator
```
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

# Controlling Reduction
%%%
tag := "tactic-reducibility"
%%%

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic Lean.Parser.Tactic.withUnfoldingAll
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

:::TODO
Next release:
```
:::tactic "mleave"
:::
```
:::

### Proving a Stateful Goal

:::tactic "mspec"
:::

:::tactic "mintro"
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

:::TODO
Next release:
```
:::tactic "mrename_i"
:::
```
:::

:::tactic "mpure"
:::

:::tactic "mframe"
:::
