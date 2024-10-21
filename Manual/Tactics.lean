/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

import Manual.Tactics.Reference
import Manual.Tactics.Conv
import Manual.Tactics.Custom

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic

#doc (Manual) "Tactic Proofs" =>
%%%
tag := "tactics"
%%%

The tactic language is a special-purpose programming language for constructing proofs.
In Lean, {tech}[propositions] are represented by types, and proofs are terms that inhabit these types.
{margin}[The {ref "propositions"}[section on propositions] describes propositions in more detail.]
While terms are designed to make it convenient to indicate a specific inhabitant of a type, tactics are designed to make it convenient to demonstrate that a type is inhabited.
This distinction exists because it's important that definitions pick out the precise objects of interest and that programs return the intended results, but proof irrelevance means that there's no _technical_ reason to prefer one proof term over another.
For example, given two assumptions of a given type, a program must be carefully written to use the correct one, while a proof may use either without consequence.

Tactics are imperative programs that modify a {deftech}_proof state_.{index}[proof state]
A proof state consists of an ordered sequence of {deftech}_goals_, which are contexts of local assumptions together with types to be inhabited; a tactic may either _succeed_ with a possibly-empty sequence of further goals (called {deftech}_subgoals_) or _fail_ if it cannot make progress.
If tactic succeeds with no subgoals, then the proof is complete.
If it succeeds with one or more subgoals, then its goal or goals will be proved when those subgoals have been proved.
The first goal in the proof state is called the {deftech}_main goal_.{index subterm:="main"}[goal]{index}[main goal]
While most tactics affect only the main goal, operators such as {tactic}`<;>` and {tactic}`all_goals` can be used to apply a tactic to many goals, and operators such as bullets, {tactic}`next` or {tactic}`case` can narrow the focus of subsequent tactics to only a single goal in the proof state.

Behind the scenes, tactics construct {deftech}[proof terms].
Proof terms are independently checkable evidence of a theorem's truth, written in Lean's type theory.
Each proof is checked in the {tech}[kernel], and can be verified with independently-implemented external checkers, so the worst outcome from a bug in a tactic is a confusing error message, rather than an incorrect proof.
Each goal in a tactic proof corresponds to an incomplete portion of a proof term.

# Running Tactics

:::TODO
The syntax of `by` is showing with commas instead of semicolons below
:::

:::syntax Lean.Parser.Term.byTactic
Tactics are included in terms using {keywordOf Lean.Parser.Term.byTactic}`by`, which is followed by a sequence of tactics in which each has the same indentation:
```grammar
by
$t
```

Alternatively, explicit braces and semicolons may be used:
```grammar
by { $t* }
```
:::

Tactics are invoked using the {keywordOf Lean.Parser.Term.byTactic}`by` term.
When the elaborator encounters {keywordOf Lean.Parser.Term.byTactic}`by`, it invokes the tactic interpreter to construct the resulting term.
Tactic proofs may be embedded via {keywordOf Lean.Parser.Term.byTactic}`by` in any context in which a term can occur.

# Reading Proof States

The goals in a proof state are displayed in order, with the main goal on top.
Goals may be either named or anonymous.
Named goals are indicated with `case` at the top (called a {deftech}_case label_), while anonymous goals have no such indicator.
Tactics assign goal names, typically on the basis of constructor names, parameter names, structure field names, or the nature of the reasoning step implemented by the tactic.

::::example "Named goals"
```CSS
#lawful-option-cases .goal-name { background-color: var(--lean-compl-yellow); }
```

This proof state contains four goals, all of which are named.
This is part of a proof that the {lean}`Monad Option` instance is lawful (that is, to provide the {lean}`LawfulMonad Option` instance), and the case names (highlighted below) come from the names of the fields of {name}`LawfulMonad`.

```proofState tag:="lawful-option-cases"
LawfulMonad Option := by
constructor
intro α β f x
rotate_right
intro α β γ x f g
rotate_right
intro α β x f
rotate_right
intro α β f x
rotate_right
```
::::


::::example "Anonymous Goals"
This proof state contains a single anonymous goal.

```proofState
∀ (n k : Nat), n + k = k + n := by
intro n k
```
::::

The {tactic}`case` and {tactic}`case'` tactics can be used to select a new main goal using the desired  goal's name.
When names are assigned in the context of a goal which itself has a name, the new goals's names are appended to the main goal's name with a dot (`'.', Unicode FULL STOP (0x2e)`) between them.

::::example "Hierarchical Goal Names"

:::tacticExample
```setup
intro n k
induction n
```


In the course of an attempt to prove {goal}`∀ (n k : Nat), n + k = k + n`, this proof state can occur:
```pre
case zero
k : Nat
⊢ 0 + k = k + 0

case succ
k n✝ : Nat
a✝ : n✝ + k = k + n✝
⊢ n✝ + 1 + k = k + (n✝ + 1)
```

After {tacticStep}`induction k`, the two new cases' names have `zero` as a prefix, because they were created in a goal named `zero`:

```CSS
#hierarchical-case-names .goal:not(:last-child) .goal-name { background-color: var(--lean-compl-yellow); }
```

```post tag:="hierarchical-case-names"
case zero.zero
⊢ 0 + 0 = 0 + 0

case zero.succ
n✝ : Nat
a✝ : 0 + n✝ = n✝ + 0
⊢ 0 + (n✝ + 1) = n✝ + 1 + 0

case succ
k n✝ : Nat
a✝ : n✝ + k = k + n✝
⊢ n✝ + 1 + k = k + (n✝ + 1)
```
:::
::::


Each goal consists of a sequence of assumptions and a desired conclusion.
Each assumption has a name and a type; the conclusion is a type.
Assumptions are either arbitrary elements of some type or statements that are presumed true.

::::example "Assumption Names and Conclusion"

```CSS
#ex-assumption-names .hypothesis .name { background-color: var(--lean-compl-yellow); }
```

This goal has four assumptions:

```proofState tag:="ex-assumption-names"
∀ (α) (xs : List α), xs ++ [] = xs := by
intro α xs
induction xs
sorry
rename_i x xs ih
```

:::keepEnv
```lean show:=false
axiom α : Type
axiom x : α
axiom xs : List α
axiom ih : xs ++ [] = xs
```

They are:

 * {lean}`α`, an arbitrary type
 * {lean}`x`, an arbitrary {lean}`α`
 * {lean}`xs`, an arbitrary {lean}`List α`
 * {lean}`ih`, an induction hypothesis that asserts that appending the empty list to {lean}`xs` is equal to {lean}`xs`.

The conclusion is the statement that prepending `x` to both sides of the equality in the induction hypothesis results in equal lists.
:::

::::

Some assumptions are {deftech}_inaccessible_, {index}[inaccessible] {index subterm:="inaccessible"}[assumption] which means that they cannot be referred to explicitly by name.
Inaccessible assumptions occur when an assumption is created without a specified name or when the assumption's name is shadowed by a later assumption.
Inaccessible assumptions should be regarded as anonymous; they are presented as if they had names because they may be referred to in later assumptions or in the conclusion, and displaying a name allows these references to be distinguished from one another.
In particular, inaccessible assumptions are presented with daggers (`†`) after their names.


::::example "Accessible Assumption Names"
```CSS
#option-cases-accessible .hypothesis .name { background-color: var(--lean-compl-yellow); }
```

In this proof state, all assumptions are accessible.

```proofState tag:="option-cases-accessible"
LawfulMonad Option := by
constructor
intro α β f x
rotate_right
sorry
rotate_right
sorry
rotate_right
sorry
rotate_right
```
::::


::::example "Inaccessible Assumption Names"
```CSS
#option-cases-inaccessible .hypotheses .hypothesis:nth-child(even) .name { background-color: var(--lean-compl-yellow); }
```

In this proof state, only the first and third assumptions are accessible.
The second and fourth are inaccessible, and their names include a dagger to indicate that they cannot be referenced.

```proofState tag:="option-cases-inaccessible"
LawfulMonad Option := by
constructor
intro α _ f _
rotate_right
sorry
rotate_right
sorry
rotate_right
sorry
rotate_right
```
::::


Inaccessible assumptions can still be used.
Tactics such as {tactic}`assumption` or {tactic}`simp` can scan the entire list of assumptions, finding one that is useful, and {tactic}`contradiction` can eliminate the current goal by finding an impossible assumption without naming it.
Other tactics, such as {tactic}`rename_i` and {tactic}`next`, can be used to name inaccessible assumptions, making them accessible.
Additionally, assumptions can be referred to by their type, by writing the type in single guillemets.

::::syntax term
Single guillemets around a term represent a reference to some term in scope with that type.

```grammar
‹$t›
```

This can be used to refer to local lemmas by their theorem statement rather than by name, or to refer to assumptions regardless of whether they have explicit names.
::::

::::example "Assumptions by Type"

In the following proof, {tactic}`cases` is repeatedly used to analyze a number.
At the beginning of the proof, the number is named `x`, but {tactic}`cases` generates an inaccessible name for subsequent numbers.
Rather than providing names, the proof takes advantage of the fact that there is a single assumption of type {lean}`Nat` at any given time and uses {lean}`‹Nat›` to refer to it.
After the iteration, there is an assumption that `n + 3 < 3`, which {tactic}`contradiction` can use to remove the goal from consideration.
```lean
example : x < 3 → x ∈ [0, 1, 2] := by
  intros
  iterate 3
    cases ‹Nat›
    . decide
  contradiction
```
::::

::::example "Assumptions by Type, Outside Proofs"

Single-guillemet syntax also works outside of proofs:

```lean name:=evalGuillemets
#eval
  let x := 1
  let y := 2
  ‹Nat›
```
```leanOutput evalGuillemets
2
```

This is generally not a good idea for non-propositions, however—when it matters _which_ element of a type is selected, it's better to select it explicitly.
::::

## Hiding Proofs and Large Terms

Terms in proof states can be quite big, and there may be many assumptions.
Because of definitional proof irrelevance, proof terms typically give little useful information.
By default, they are not shown in goals in proof states unless they are {deftech}_atomic_, meaning that they contain no subterms.
Hiding proofs is controlled by two options: {option}`pp.proofs` turns the feature on and off, while {option}`pp.proofs.threshold` determines a size threshold for proof hiding.

:::example "Hiding Proof Terms"
In this proof state, the proof that `0 < n` is hidden.

```proofState
∀ (n : Nat) (i : Fin n), i.val > 5 → (⟨0, by cases i; omega⟩ : Fin n) < i := by
  intro n i gt
/--
n : Nat
i : Fin n
gt : ↑i > 5
⊢ ⟨0, ⋯⟩ < i
-/

```
:::



{optionDocs pp.proofs}

{optionDocs pp.proofs.threshold}


Additionally, non-proof terms may be hidden when they are too large.
In particular, Lean will hide terms that are below a configurable depth threshold, and it will hide the remainder of a term once a certain amount in total has been printed.
Showing deep terms can enabled or disabled with the option {option}`pp.deepTerms`, and the depth threshold can be configured with the option {option}`pp.deepTerms.threshold`.
The maximum number of pretty-printer steps can be configured with the option {option}`pp.maxSteps`.
Printing very large terms can lead to slowdowns or even stack overflows in tooling; please be conservative when adjusting these options' values.

{optionDocs pp.deepTerms}

{optionDocs pp.deepTerms.threshold}

{optionDocs pp.maxSteps}

## Metavariables

Terms that begin with a question mark are _metavariables_ that correspond to an unknown value.
They may stand for either {tech}[universe] levels or for terms.
Some metavariables arise as part of Lean's elaboration process, when not enough information is yet available to determine a value.
These metavariables' names have a numeric component at the end, such as `?m.392` or `?u.498`.
Other metavariables come into existence as a result of tactics or {tech}[named holes].
These metavariables' names do not have a numeric component.
Metavariables that result from tactics frequently appear as goals whose {tech}[case labels] match the name of the metavariable.


::::example "Universe Level Metavariables"
In this proof state, the universe level of `α` is unknown:
```proofState
∀ (α : _) (x : α) (xs : List α), x ∈ xs → xs.length > 0 := by
  intros α x xs elem
/--
α : Type ?u.783
x : α
xs : List α
elem : x ∈ xs
⊢ xs.length > 0
-/
```
::::

::::example "Type Metavariables"
In this proof state, the type of list elements is unknown.
The metavariable is repeated because the unknown type must be the same in both positions.
```proofState
∀ (x : _) (xs : List _), x ∈ xs → xs.length > 0 := by
  intros x xs elem
/--
x : ?m.902
xs : List ?m.902
elem : x ∈ xs
⊢ xs.length > 0
-/

```
::::


::::example "Metavariables in Proofs"

:::tacticExample

{goal show:=false}`∀ (i j k  : Nat), i < j → j < k → i < k`

```setup
  intros i j k h1 h2
```

In this proof state,
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```
applying the tactic {tacticStep}`apply Nat.lt_trans` results in the following proof state, in which the middle value of the transitivity step `?m` is unknown:
```post
case h₁
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < ?m

case a
i j k : Nat
h1 : i < j
h2 : j < k
⊢ ?m < k

case m
i j k : Nat
h1 : i < j
h2 : j < k
⊢ Nat
```
:::
::::

::::example "Explicitly-Created Metavariables"
:::tacticExample
{goal show:=false}`∀ (i j k  : Nat), i < j → j < k → i < k`

```setup
  intros i j k h1 h2
```

Explicit named holes are represented by metavariables, and additionally give rise to proof goals.
In this proof state,
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```
applying the tactic {tacticStep}`apply @Nat.lt_trans i ?middle k ?p1 ?p2` results in the following proof state, in which the middle value of the transitivity step `?middle` is unknown and goals have been created for each of the named holes in the term:
```post
case middle
i j k : Nat
h1 : i < j
h2 : j < k
⊢ Nat

case p1
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < ?middle

case p2
i j k : Nat
h1 : i < j
h2 : j < k
⊢ ?middle < k
```
:::
::::

The display of metavariable numbers can be disabled using the {option}`pp.mvars`.
This can be useful when using features such as {keywordOf Lean.guardMsgsCmd}`#guard_msgs` that match Lean's output against a desired string, which is very useful when writing tests for custom tactics.

{optionDocs pp.mvars}


:::planned 68
Demonstrate and explain diff labels that show the difference between the steps of a proof state.
:::

# The Tactic Language

A tactic script consists of a sequence of tactics, separated either by semicolons or newlines.
When separated by newlines, tactics must be indented to the same level.
Explicit curly braces and semicolons may be used instead of indentation.
Tactic sequences may be grouped by parentheses.
This allows a sequence of tactics to be used in a position where a single tactic would otherwise be grammatically expected.

Generally, execution proceeds from top to bottom, with each tactic running in the proof state left behind by the prior tactic.
The tactic language contains a number of control structures that can modify this flow.

Each tactic is a syntax extension in the `tactic` category.
This means that tactics are free to define their own concrete syntax and parsing rules.
However, with a few exceptions, the majority of tactics can be identified by a leading keyword; the exceptions are typically frequently-used built-in control structures such as {tactic}`<;>`.

## Control Structures

### Success and Failure

When run in a proof state, every tactic either succeeds or fails.
Tactic failure is akin to exceptions: failures typically "bubble up" until handled.
Unlike exceptions, there is no operator to distinguish between reasons for failure; {tactic}`first` simply takes the first branch that succeeds.

::: tactic "fail"
:::

:::tactic "fail_if_success"
:::

:::tactic "try"
:::

:::tactic "first"
:::


### Branching

Tactic proofs may use pattern matching and conditionals.
However, their meaning is not quite the same as it is in terms.
While terms are expected to be executed once the values of their variables are known, proofs are executed with their variables left abstract and should consider _all_ cases simultaneously.
Thus, when `if` and `match` are used in tactics, their meaning is reasoning by cases rather than selection of a concrete branch.
All of their branches are executed, and the condition or pattern match is used to refine the main goal with more information in each branch, rather than to select a single branch.

:::tactic Lean.Parser.Tactic.tacIfThenElse show := "if ... then ... else ..."

:::

:::tactic Lean.Parser.Tactic.tacDepIfThenElse show:= "if h : ... then ... else ..."
:::

:::example "Reasoning by cases with `if`"
In each branch of the {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if`, an assumption is added that reflects whether `n = 0`.

```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  if n = 0 then
    simp [*]
  else
    simp only [↓reduceIte, gt_iff_lt, *]
    omega
```
:::

:::tactic Lean.Parser.Tactic.match show := "match"

When pattern matching, instances of the scrutinee in the goal are replaced with the patterns that match them in each branch.
Each branch must then prove the refined goal.
Compared to the `cases` tactic, using `match` can allow a greater degree of flexibility in the cases analysis being performed, but the requirement that each branch solve its goal completely makes it more difficult to incorporate into larger automation scripts.
:::

:::example "Reasoning by cases with `match`"
In each branch of the {keywordOf Lean.Parser.Tactic.match}`match`, the scrutinee `n` has been replaced by either `0` or `k + 1`.
```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  match n with
  | 0 =>
    simp
  | k + 1 =>
    simp
```
:::

### Goal Selection

Most tactics affect the {tech}[main goal].
Goal selection tactics provide a way to treat a different goal as the main one, rearranging the sequence of goals in the proof state.


:::tactic "case"
:::

:::tactic "case'"
:::


:::tactic "rotate_left"
:::

:::tactic "rotate_right"
:::

#### Sequencing

In addition to running tactics one after the other, each being used to solve the main goal, the tactic language supports sequencing tactics according to the way in which goals are produced.
The {tactic}`<;>` tactic combinator allows a tactic to be applied to _every_ {tech}[subgoal] produced by some other tactic.
If no new goals are produced, then the second tactic is not run.

:::tactic "<;>"

If the tactic fails on any of the {tech}[subgoals], then the whole {tactic}`<;>` tactic fails.
:::

::::example "Subgoal Sequencing"
:::tacticExample

```setup
  intro x h
```

{goal show := false}`∀x, x = 1 ∨ x = 2 → x < 3`

In a this proof state:
```pre
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```
the tactic {tacticStep}`cases h` yields the following two goals:
```post
case inl
x : Nat
h✝ : x = 1
⊢ x < 3

case inr
x : Nat
h✝ : x = 2
⊢ x < 3
```

:::
:::tacticExample

```setup
  intro x h
```

{goal show := false}`∀x, x = 1 ∨ x = 2 → x < 3`

```pre (show := false)
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```

Running {tacticStep}`cases h ; simp [*]` causes {tactic}`simp` to solve the first goal, leaving the second behind:
```post
case inr
x : Nat
h✝ : x = 2
⊢ x < 3
```

:::

:::tacticExample

```setup
  intro x h
```

{goal show := false}`∀x, x = 1 ∨ x = 2 → x < 3`

```pre (show := false)
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```

Replacing the `;` with {tactic}`<;>` and running {tacticStep}`cases h <;> simp [*]` solves *both* of the new goals with {tactic}`simp`:

```post

```

:::

::::

#### Working on Multiple Goals

The tactics {tactic}`all_goals` and {tactic}`any_goals` allow a tactic to be applied to every goal in the proof state.
The difference between them is that if the tactic fails for in any of the goals, {tactic}`all_goals` itself fails, while {tactic}`any_goals` fails only if the tactic fails in all of the goals.

:::tactic "all_goals"
:::

:::tactic "any_goals"
:::


### Focusing


Focusing tactics remove some subset of the proof goals (typically leaving only the main goal) from the consideration of some further tactics.
In addition to the tactics described here, the {tactic}`case` and {tactic}`case'` tactics focus on the selected goal.

:::tactic Lean.cdot show:="·"

It is generally considered good Lean style to use bullets whenever a tactic line results in more than one new subgoal.
This makes it easier to read and maintain proofs, because the connections between steps of reasoning are more clear and any change in the number of subgoals while editing the proof will have a localized effect.
:::

:::tactic "next"
:::


:::tactic "focus"
:::

### Repetition and Iteration

:::tactic "iterate"
:::

:::tactic "repeat"
:::

:::tactic "repeat'"
:::

:::tactic "repeat1'"
:::


## Names and Hygiene


Behind the scenes, tactics generate proof terms.
These proof terms exist in a local context, because assumptions in proof states correspond to local binders in terms.
Uses of assumptions correspond to variable references.
It is very important that the naming of assumptions be predictable; otherwise, small changes to the internal implementation of a tactic could either lead to variable capture or to a broken reference if they cause different names to be selected.

Lean's tactic language is _hygienic_. {index subterm := "in tactics"}[hygiene]
This means that the tactic language respects lexical scope: names that occur in a tactic refer to the enclosing binding in the source code, rather than being determined by the generated code, and the tactic framework is responsible for maintaining this property.
Variable references in tactic scripts refer either to names that were in scope at the beginning of the script or to bindings that were explicitly introduced as part of the tactics, rather than to the names chosen for use in the proof term behind the scenes.

A consequence of hygienic tactics is that the only way to refer to an assumption is to explicitly name it.
Tactics cannot assign assumption names themselves, but must rather accept names from users; users are correspondingly obligated to provide names for assumptions that they wish to refer to.
When an assumption does not have a user-provided name, it is shown in the proof state with a dagger (`'†', DAGGER	0x2020`).
The dagger indicates that the name is _inaccessible_ and cannot be explicitly referred to.

Hygiene can be disabled by setting the option {option}`tactic.hygienic` to `false`.
This is not recommended, as many tactics rely on the hygiene system to prevent capture and thus do not incur the overhead of careful manual name selection.

{optionDocs tactic.hygienic}

::::example "Tactic hygiene: inaccessible assumptions"
:::tacticExample

```setup
skip
```
When proving that {goal}`∀ (n : Nat), 0 + n = n`, the initial proof state is:

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

The tactic {tacticStep}`intro` results in a proof state with an inaccessible  assumption:

```post
n✝ : Nat
⊢ 0 + n✝ = n✝
```
:::
::::

::::example "Tactic hygiene: accessible assumptions"
:::tacticExample

```setup
skip
```
When proving that {goal}`∀ (n : Nat), 0 + n = n`, the initial proof state is:

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

The tactic {tacticStep}`intro n`, with the explicit name `n`, results in a proof state with an accessibly-named assumption:

```post
n : Nat
⊢ 0 + n = n
```
:::
::::

### Accessing Assumptions

Many tactics provide a means of specifying names for the assumptions that they introduce.
For example, {tactic}`intro` and {tactic}`intros` take assumption names as arguments, and {tactic}`induction`'s {keywordOf Lean.Parser.Tactic.induction}`with`-form allows simultaneous case selection, assumption naming, and focusing.
When an assumption does not have a name, one can be assigned using {tactic}`next`, {tactic}`case`, or {tactic}`rename_i`.

:::tactic "rename_i"
:::

## Assumption Management

Larger proofs can benefit from management of proof states, removing irrelevant assumptions and making their names easier to understand.
Along with these operators, {tactic}`rename_i` allows inaccessible assumptions to be renamed, and {tactic}`intro`, {tactic}`intros` and {tactic}`rintro` convert goals that are implications or universal quantification into goals with additional assumptions.

:::tactic "rename"
:::

:::tactic "revert"
:::

:::tactic "clear"
:::


## Local Definitions and Proofs

{tactic}`have` and {tactic}`let` both create local assumptions.
Generally speaking, {tactic}`have` should be used when proving an intermediate lemma; {tactic}`let` should be reserved for local definitions.

:::tactic "have"
:::

:::tactic Lean.Parser.Tactic.tacticHaveI_
:::

:::tactic Lean.Parser.Tactic.tacticHave'_
:::

:::tactic Lean.Parser.Tactic.tacticLet_ show:="let"
:::

:::tactic Lean.Parser.Tactic.letrec show:="let rec"
:::

:::tactic Lean.Parser.Tactic.tacticLetI_
:::

:::tactic Lean.Parser.Tactic.tacticLet'_
:::

## Namespace and Option Management

Namespaces and options can be adjusted in tactic scripts using the same syntax as in terms.

:::tactic Lean.Parser.Tactic.set_option show:="set_option"
:::

:::tactic Lean.Parser.Tactic.open show:="open"
:::

### Controlling Unfolding

By default, only definitions marked reducible are unfolded, except when checking definitional equality.
These operators allow this default to be adjusted for some part of a tactic script.

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withUnfoldingAll
:::


# Options

These options affect the meaning of tactics.

{optionDocs tactic.dbg_cache}

{optionDocs tactic.customEliminators}

{optionDocs tactic.skipAssignedInstances}

{optionDocs tactic.simp.trace}


{include 0 Manual.Tactics.Reference}

{include 0 Manual.Tactics.Conv}

{include 0 Manual.Tactics.Custom}
