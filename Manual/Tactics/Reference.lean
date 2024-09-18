import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Tactic Reference" =>


# Assumptions


:::tactic Lean.Parser.Tactic.assumption
:::


:::tactic Lean.Parser.Tactic.applyAssumption
:::

# Quantifiers

:::tactic "exists"
:::

# Relations

:::tactic "rfl"
:::

:::tactic Lean.Parser.Tactic.applyRfl
:::

:::tactic Lean.Parser.Tactic.tacticRfl
:::

:::tactic "symm"
:::

:::tactic "calc"
:::


## Equality

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

# Lemmas

:::tactic "exact"
:::

:::tactic "apply"
:::

:::tactic "refine"
:::

:::tactic "refine'"
:::


# Falsehood

:::tactic "exfalso"
:::

:::tactic "contradiction"
:::

:::tactic Lean.Parser.Tactic.falseOrByContra
:::


# Goal Management

:::tactic "suffices"
:::

:::tactic "change"
:::

:::tactic Lean.Parser.Tactic.changeWith
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

:::tactic Lean.Parser.Tactic.pushCast
:::

:::tactic Lean.Parser.Tactic.normCast0
:::

:::tactic Lean.Parser.Tactic.tacticNorm_cast_
:::

:::tactic Lean.Parser.Tactic.tacticExact_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticApply_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticRw_mod_cast___
:::

:::tactic Lean.Parser.Tactic.tacticAssumption_mod_cast
:::




# Extensionality


:::tactic "ext"
:::

:::tactic Lean.Elab.Tactic.Ext.tacticExt1___
:::

:::tactic Lean.Elab.Tactic.Ext.applyExtTheorem
:::

:::tactic "funext"
:::

# Simplification

The simplifier is described in greater detail in {ref "the-simplifier"}[its dedicated chapter].

:::tactic "simp"
:::

:::tactic "simp?"
:::

:::tactic "simp?!"
:::

:::tactic "simp_arith"
:::

:::tactic Lean.Parser.Tactic.simpArithAutoUnfold
:::

:::tactic "dsimp"
:::

:::tactic "dsimp?"
:::

:::tactic "dsimp?!"
:::

:::tactic "dsimp!"
:::

:::tactic "simp_all"
:::

:::tactic "simp_all?"
:::

:::tactic "simp_all?!"
:::


:::tactic "simp_all_arith"
:::

:::tactic "simpa"
:::

:::tactic "simpa?"
:::

:::tactic "simpa!"
:::

:::tactic "simpa?!"
:::


# Rewriting

:::tactic "rw"
:::

:::tactic "rewrite"
:::

:::tactic "erw"
:::

:::tactic Lean.Parser.Tactic.tacticRwa__
:::

:::tactic "unfold"

Implemented by {name}`Lean.Elab.Tactic.evalUnfold`.
:::

:::tactic "replace"
:::

:::tactic "delta"
:::


# Inductive Types

:::tactic "constructor"
:::

:::tactic "cases"
:::

:::tactic "rcases"
:::

:::tactic "induction"
:::

:::tactic "nofun"
:::

:::tactic "nomatch"
:::


:::tactic "injection"
:::

:::tactic "injections"
:::

:::tactic "left"
:::

:::tactic "right"
:::


# Library Search

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

:::tactic "split"
:::

:::tactic "by_cases"
:::

# Decision Procedures

:::tactic "omega"
:::

:::tactic Lean.Parser.Tactic.decide show:="decide"
:::


:::tactic Lean.Parser.Tactic.nativeDecide show:="native_decide"
:::

## SAT Solver Integration

:::tactic "bv_omega"
:::

:::tactic "bv_decide"
:::

:::tactic "bv_normalize"
:::

:::tactic "bv_check"
:::

:::tactic Lean.Parser.Tactic.bvTrace
:::

# Control Flow

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


:::tactic "checkpoint"
:::

:::tactic "save"
:::

:::tactic "stop"
:::


# Term Elaboration Backends

These tactics are used during elaboration of terms to satisfy obligations that arise.

:::tactic "decreasing_tactic"
:::

:::tactic "decreasing_trivial"
:::

:::tactic "decreasing_trivial_pre_omega"
:::

:::tactic "get_elem_tactic"
:::

:::tactic "get_elem_tactic_trivial"
:::

:::tactic "array_get_dec"
:::

:::tactic tacticDecreasing_with_
:::

# Debugging Utilities

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

:::tactic "trivial"
:::

:::tactic "solve"
:::

:::tactic "solve_by_elim"
:::


:::tactic "infer_instance"
:::
:::tactic Lean.Parser.Tactic.tacticUnhygienic_
:::
