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

open Lean Lean.Grind Lean.Meta.Grind


#doc (Manual) "Constraint Propagation" =>
%%%
tag := "grind-propagation"
%%%

{deftech}[Constraint propagation] works on the {lean}`True` and {lean}`False` buckets of the whiteboard.
Whenever a term is added to one of those buckets, {tactic}`grind` fires dozens of small {deftech}_forward rules_ that derive further information from its logical consequences:

: Boolean connectives

  ::::leanSection
  ```lean (show := false)
  variable {A B : Prop}
  ```
  :::paragraph
  The truth tables of the Boolean connectives can be used to derive further true and false facts.
  For example:
   * If {lean}`A` is {lean}`True`, then {lean}`A ∨ B` becomes {lean}`True`.
   * If {lean}`A ∧ B` is {lean}`True`, then both {lean}`A` and {lean}`B` become {lean}`True`.
   * If {lean}`A ∧ B` is {lean}`False`, at least one of {lean}`A`, {lean}`B` becomes {lean}`False`.
  :::
  ::::

: Inductive Types

  If terms formed by applications of two different constructors of the same {tech}[inductive type] (e.g. {name}`none` and {name}`some`) are placed in the same equivalence class, a contradiction is derived.
  If two terms formed by applications of the same constructor are placed in the same equivalence class, then their arguments are also made equal.

: Projections
  :::leanSection
  ```lean (show := false)
  variable {x x' : α} {y y' : β} {h : (x, y) = (x', y')} {a : α}
  ```

  From {typed}`h : (x, y) = (x', y')` we derive {lean}`x = x'` and {lean}`y = y'`.
  :::

: Casts

  :::leanSection
  ```lean (show := false)
  variable {h : α = β} {a : α}
  ```
  Any term {typed}`cast h a : β` is equated with {typed}`a : α` immediately (using {tech}[heterogeneous equality]).
  :::

: Definitional equality, including {tech key:="η-equivalence"}[η-equality]

  :::leanSection
  ```lean (show := false)
  variable {α : Type u} {β : Type v} {a : α} {b : β}
  structure S α β where
    x : α
    y : β
  variable {p : S α β}

  -- Check that it works!
  example : p = ⟨p.1, p.2⟩ := by grind
  ```
  Definitional reduction is propagated, so {lean}`(a, b).1` is equated with {lean}`a`.
  Additionally, if {lean}`p` is an instance of a {tech}[structure] with two fields, then {lean}`p` is equated with {lean type:="S α β"}`⟨p.1, p.2⟩`.
  :::

:::paragraph
Below is a _representative slice_ of the propagators that demonstrates their overall style.
Each follows the same skeleton.

1. It inspect the truth value of sub‑expressions.

2. If further facts can be derived, it either equates terms (connecting them on the metaphorical whiteboard) using ({lean}`pushEq`), or it indicates truth values using ({lean}`pushEqTrue` / {lean}`pushEqFalse`).
   These steps produce proof terms using internal helper lemmas such as {name}`Grind.and_eq_of_eq_true_left`.

3. If a contradiction arises, the goal is closed using ({lean}`closeGoal`).

{deftech}_Upward propagation_ derives facts about a term from facts about sub-terms, while {deftech}_downward propagation_ derives facts about sub-terms from facts about a term.
:::

```lean (show := false)
namespace ExamplePropagators
```
```lean (keep := false)

/-- Propagate equalities *upwards* for conjunctions. -/
builtin_grind_propagator propagateAndUp ↑And := fun e => do
  let_expr And a b := e | return ()
  if (← isEqTrue a) then
    -- a = True  ⇒  (a ∧ b) = b
    pushEq e b <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_left)
        a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    -- b = True  ⇒  (a ∧ b) = a
    pushEq e a <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_right)
        a b (← mkEqTrueProof b)
  else if (← isEqFalse a) then
    -- a = False  ⇒  (a ∧ b) = False
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_left)
        a b (← mkEqFalseProof a)
  else if (← isEqFalse b) then
    -- b = False  ⇒  (a ∧ b) = False
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_right)
        a b (← mkEqFalseProof b)

/--
Truth flows *down* when the whole `And` is proven `True`.
-/
builtin_grind_propagator propagateAndDown ↓And :=
  fun e => do
  if (← isEqTrue e) then
    let_expr And a b := e | return ()
    let h ← mkEqTrueProof e
    -- (a ∧ b) = True  ⇒  a = True
    pushEqTrue a <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_left) a b h
    -- (a ∧ b) = True  ⇒  B = True
    pushEqTrue b <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_right) a b h
```
```lean (show := false)
end ExamplePropagators
```



Other frequently‑triggered propagators follow the same pattern:

::::leanSection
```lean (show := false)
variable {A B : Prop} {a b : α}
```

:::table (header := true)
*
  * Propagator
  * Handles
  * Notes
*
  * {lean}`propagateOrUp` / {lean}`propagateOrDown`
  * {lean}`A ∨ B`
  * Uses the truth table for disjunction to derive further truth values
*
  * {lean}`propagateNotUp` / {lean}`propagateNotDown`
  * {lean}`¬ A`
  * Ensures that {lean}`¬ A` and {lean}`A` have opposite truth values
*
  * {lean}`propagateEqUp` / {lean}`propagateEqDown`
  * `a = b`
  * Bridges Booleans, detects constructor clash {TODO}[What does 'bridges booleans' mean? Find out]
*
  * {lean}`propagateIte` / {lean}`propagateDIte`
  * {name}`ite` / {name}`dite`
  * Equates the term with the chosen branch once the condition's truth value is known
*
  * `propagateEtaStruct`
  * Values of structures tagged `[grind ext]`
  * Generates η‑expansion `a = ⟨a.1, …⟩`
:::
::::

:::comment
TODO (@kim-em): we don't add the `{lean}` literal type to `propagateEtaStruct` above because it is private.
:::

Many specialized variants for {lean}`Bool` mirror these rules exactly (e.g. {lean}`propagateBoolAndUp`).

# Propagation‑Only Examples

These goals are closed *purely* by constraint propagation—no case splits, no theory solvers:

```lean
-- Boolean connective: a && !a is always false.
example (a : Bool) : (a && !a) = false := by
  grind

-- Conditional (ite):
-- once the condition is true, ite picks the 'then' branch.
example (c : Bool) (t e : Nat) (h : c = true) :
    (if c then t else e) = t := by
  grind

-- Negation propagates truth downwards.
example (a : Bool) (h : (!a) = true) : a = false := by
  grind
```

These snippets run instantly because the relevant propagators ({lean}`propagateBoolAndUp`, {lean}`propagateIte`, {lean}`propagateBoolNotDown`) fire as soon as the hypotheses are internalized.
Setting the option {option}`trace.grind.eqc` to {lean}`true` causes {tactic}`grind` to print a line every time two equivalence classes merge, which is handy for seeing propagation in action.


:::TODO

This section should be uncommented when the command is implemented:

```lean (show := false)
-- Test to ensure that this section is uncommented when the command is implemented
/--
error: elaboration function for 'Lean.Parser.«command_Grind_propagator___(_):=_»' has not been implemented
-/
#guard_msgs in
grind_propagator ↑x(y) := _
```

{tactic}`grind` is still under active development, and its implementation is likely to change.
Until the API has stabilized we recommend _refraining from writing custom elaborators or satellite solvers_.
If a project-local custom propagator is really needed, then it should be defined using the {keywordOf «command_Grind_propagator___(_):=_»}`grind_propagator` command, rather than {keywordOf «command_Builtin_grind_propagator____:=_»}`builtin_grind_propagator` (the latter is reserved for Lean’s own code).
When adding new propagators, keep them *small and orthogonal*—they should fire in ≤1 µs and either push one fact or close the goal.
This keeps the propagation phase predictable and easy to debug.
:::

The set of propagation rules is expanded and refined over time, so the InfoView will show increasingly rich {lean}`True` and {lean}`False` buckets.
The full equivalence classes are displayed automatically _only when {tactic}`grind` fails_, and only for the first subgoal that it could not close—use this output to inspect missing facts and understand why the subgoal remains open.

:::example "Identifying Missing Facts"
In this example, {tactic}`grind` fails:

```lean (error := true) (name := missing)
example :
    x = y ∧ y = z →
    w = x ∨ w = v →
    w = z := by
  grind
```
The resulting error message includes the identified equivalence classes along with the true and false propositions:
```leanOutput missing (expandTrace := eqc)
`grind` failed
case grind
α : Sort u_1
x y z w v : α
left : x = y
right : y = z
h_1 : w = x ∨ w = v
h_2 : ¬w = z
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] w = x ∨ w = v
    [prop] w = v
  [eqc] False propositions
    [prop] w = x
    [prop] w = z
  [eqc] Equivalence classes
    [eqc] {x, y, z}
    [eqc] {w, v}
```
Both `x = y` and `y = z` were discovered by constraint propagation from the `x = y ∧ y = z` premise.
In this proof, {tactic}`grind` performed a case split on `w = x ∨ w = v`.
In the second branch, it could not place `w` and `z` in the same equivalence class.
:::
