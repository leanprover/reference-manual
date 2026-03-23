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

:::tactic "false_or_by_contra"
:::


# Goal Management
%%%
tag := "tactic-ref-goals"
%%%

:::tactic "suffices"
:::

:::tactic "change"
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

:::tactic "rw"
:::

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


:::tactic "split"
:::

:::tactic "by_cases"
:::

# Decision Procedures
%%%
tag := "tactic-ref-decision"
%%%


:::tactic Lean.Parser.Tactic.decide (show := "decide")
:::

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

Declarations marked with {attr}`cbv_opaque` are never unfolded.
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
However, {attrs}`@[cbv_eval]` rewrite rules are still applied to {attrs}`@[cbv_opaque]` declarations.
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
Patterns are matched agains subexpressions structurally after unfolding reducible definitions and applying beta, eta, and zeta reduction to both sides.
Matching is modulo alpha-equivalence (bound variable names are ignored), and proof and instance arguments in the pattern are trated as wildcards.
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
