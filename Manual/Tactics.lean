import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Tactic Proofs" =>

The tactic language is a special-purpose programming language for constructing proofs.
In Lean, statements are represented by types, and proofs are terms that inhabit these types.
While terms are designed to make it convenient to indicate a specific inhabitant of a type, tactics are designed to make it convenient to demonstrate that a type is inhabited.
This distinction exists because it's important that definitions pick out the precise objects of interest and that programs return the intended results, but proof irrelevance means that there's no _technical_ reason to prefer one proof term over another.
For example, given two assumptions of a given type, a program must be carefully written to use the correct one, while a proof may use either without consequence.

Tactics are imperative programs that modify a {deftech}_proof state_.{index}[proof state]
A proof state consists of an ordered sequence of {deftech}_goals_, which are contexts of local assumptions together with types to be inhabited; a tactic may either _succeed_ with a possibly-empty sequence of further goals or _fail_ if it cannot make progress.
If tactic succeeds with no further goals, then the proof is complete.
If it succeeds with one or more further goals, then its goal or goals will be proved when those further goals have been proved.
While most tactics affect only the first goal in the sequence, operators such as {tactic}`<;>` and {tactic}`all_goals` can be used to apply a tactic to many goals, and operators such as bullets, {tactic}`next` or {tactic}`case` can narrow the focus of subsequent tactics to only a single goal in the proof state.

Behind the scenes, tactics construct {deftech}[proof terms].
Proof terms are independently checkable evidence of a theorem's truth, written in Lean's core type theory.
Each proof is checked in the {tech}[kernel], and can be verified with independently-implemented external checkers, so the worst outcome from a bug in a tactic is a confusing error message, rather than an incorrect proof.
Each goal in a tactic proof corresponds to an incomplete portion of a proof term.

# Running Tactics

:::syntax Lean.Parser.Term.byTactic
Tactics are included in terms using {keywordOf Lean.Parser.Term.byTactic}`by`, which is followed by a sequence of tactics in which each has the same indentation:
```grammar
by
$t
```

Alternatively, explicit brackets and semicolons may be used:
```grammar
by { $t* }
```
:::

Tactics are invoked using the {keywordOf Lean.Parser.Term.byTactic}`by` term.
When the elaborator encounters {keywordOf Lean.Parser.Term.byTactic}`by`, it invokes the tactic interpreter to construct the resulting term.
Tactic proofs may be embedded via {keywordOf Lean.Parser.Term.byTactic}`by` in any context in which a term can occur.

# Tactic Overview

## Assumptions

:::TODO
Create a tactic documentation command that does what both of the following do, using the infrastructure from https://github.com/leanprover/lean4/pull/4490
:::

:::tactic Lean.Parser.Tactic.assumption
:::

:::tactic "rename"
:::

:::tactic "rename_i"
:::

:::tactic "have"
:::

:::tactic Lean.Parser.Tactic.«tacticHave'_:=_»
:::

:::tactic Lean.Parser.Tactic.tacticHaveI_
:::

:::tactic Lean.Parser.Tactic.tacticHave'_
:::

:::tactic "revert"
:::

:::tactic "clear"
:::

## Quantifiers

:::TODO
Work around Markdown headers in `intro`, `intros` docs
:::

:::tactic Lean.Parser.Tactic.introMatch
:::


:::tactic "rintro"
:::

:::tactic "exists"
:::


Here is {tactic}`rintro` and Here is {tactic}`induction`

:::tacticExample
The goal is {goal}`∀(n : Nat), n = n`.
```setup
intro
```
After some tactics, it ends up being:
```pre
n✝ : Nat
⊢ n✝ = n✝
```
Running {tacticStep}`skip` leaves
```post
n✝ : Nat
⊢ n✝ = n✝
```
:::

:::tacticExample
The goal is {goal}`∀(n : Nat), n = n`.
```setup
intro n; induction n
```
After some tactics, it ends up being:
```pre
case zero
⊢ 0 = 0

case succ
n✝ : Nat
a✝ : n✝ = n✝
⊢ n✝ + 1 = n✝ + 1
```
Running {tacticStep}`skip` leaves
```post
case zero
⊢ 0 = 0

case succ
n✝ : Nat
a✝ : n✝ = n✝
⊢ n✝ + 1 = n✝ + 1
```
:::

## Lemmas

:::tactic "exact"
:::

:::tactic "apply"
:::

:::tactic "refine"
:::

:::tactic "refine'"
:::


## Falsehood

:::tactic "exfalso"
:::

:::tactic "contradiction"
:::

:::tactic Lean.Parser.Tactic.falseOrByContra
:::


## Goal Management

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


### Goal Selection

:::tactic Lean.cdot
:::

:::tactic "case"
:::

:::tactic "case'"
:::

:::tactic "next"
:::

:::tactic "all_goals"
:::

:::tactic "any_goals"
:::

:::tactic "focus"
:::

:::tactic Lean.Parser.Tactic.rotateLeft
:::

:::tactic Lean.Parser.Tactic.rotateRight
:::


## Cast Management

:::tactic Lean.Parser.Tactic.pushCast
:::

## Relations

:::tactic "rfl"
:::

:::tactic "rfl'"
:::

:::tactic "symm"
:::

:::tactic "calc"
:::


### Equality

:::tactic "subst"
:::

:::tactic "subst_eqs"
:::

:::tactic "congr"
:::

:::tactic "eq_refl"
:::


## Extensionality


:::tactic "ext"
:::

:::tactic Lean.Elab.Tactic.Ext.applyExtTheorem
:::

:::tactic "funext"
:::

## Simplification

:::tactic "simp"
:::

:::tactic "simp?"
:::

:::tactic "simp?!"
:::

:::tactic "simp_arith"
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


## Rewriting

:::tactic "rw"
:::

:::tactic "rewrite"
:::

:::tactic "erw"
:::

:::tactic "unfold"
:::

:::tactic "replace"
:::

:::tactic "delta"
:::


## Inductive Types

:::tactic "constructor"
:::

:::tactic "cases"
:::

:::tactic "rcases"
:::

:::tactic "induction"
:::

:::tactic "injection"
:::

:::tactic "injections"
:::

:::tactic "left"
:::

:::tactic "right"
:::


## Library Search

:::tactic "exact?"
:::

:::tactic "apply?"
:::

:::tactic "rw?"
:::

## Case Analysis

:::tactic "split"
:::

:::tactic "by_cases"
:::

## Decision Procedures

:::tactic "omega"
:::

:::TODO
`decide`
:::

:::tactic Lean.Parser.Tactic.nativeDecide
:::

### SAT Solver Integration

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

## Control Flow

:::tactic "skip"
:::

:::tactic "<;>"
:::

:::tactic "try"
:::

:::tactic "first"
:::

:::tactic Lean.Parser.Tactic.tacIfThenElse
:::

:::tactic Lean.Parser.Tactic.tacDepIfThenElse
:::

:::tactic Lean.Parser.Tactic.match
:::

:::tactic "nofun"
:::

:::tactic "nomatch"
:::

:::tactic "iterate"
:::

:::tactic "repeat"
:::

:::tactic "repeat'"
:::

:::tactic "repeat1'"
:::


:::tactic "fail"
:::

:::tactic "fail_if_success"
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

:::tactic "let"
:::

:::tactic Lean.Parser.Tactic.tacticLet_
:::

:::tactic Lean.Parser.Tactic.tacticLetI_
:::


:::tactic "checkpoint"
:::

:::tactic "save"
:::

:::tactic "stop"
:::



## Namespace and Option Management

:::tactic Lean.Parser.Tactic.set_option
:::

:::tactic Lean.Parser.Tactic.open
:::

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withUnfoldingAll
:::


## Term Elaboration Backends

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

## Conv

:::tactic "conv"
:::

## Debugging Utilities

:::tactic "sorry"
:::

:::tactic "admit"
:::

:::tactic "dbg_trace"
:::


## Other

:::tactic "trivial"
:::

:::tactic Lean.Parser.Tactic.tacticUnhygienic_
:::
