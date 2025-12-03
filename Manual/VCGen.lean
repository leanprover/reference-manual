/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual

import Manual.Meta
import Manual.Papers
import Manual.VCGen.Tutorial

import Std.Tactic.Do

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External (lit)

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

set_option mvcgen.warning false

open Manual (comment)

open Std.Do

#doc (Manual) "The `mvcgen` tactic" =>
%%%
tag := "mvcgen-tactic"
htmlSplit := .never
%%%

The {tactic}`mvcgen` tactic implements a _monadic verification condition generator_:
It breaks down a goal involving a program written using Lean's imperative {keywordOf Lean.Parser.Term.do}`do` notation into a number of pure {deftech}_verification conditions_ ({deftech}[VCs]) that discharge said goal.
A verification condition is a sub-goal that does not mention the monad underlying the `do` block.

In order to use the {tactic}`mvcgen` tactic, {module}`Std.Tactic.Do` must be imported and the namespace {namespace}`Std.Do` must be opened.

{include 0 Manual.VCGen.Tutorial}

# Overview

The workflow of {tactic}`mvcgen` consists of the following:
1. Monadic programs are re-interpreted according to a predicate transformer semantics.{TODO}[def and link]
   An instance of {name}`WP` determines the monad's interpretation.
   Each program is interpreted as a mapping from arbitrary postconditions to the {tech}[weakest precondition] that would ensure the postcondition.
2. Programs are composed from smaller programs.
   Each statement in a {keywordOf Lean.Parser.Term.do}`do`-block is associated with a predicate transformer, and there are general-purpose rules for combining these statements with sequencing and control-flow operators.
   A statement with its pre- and postconditions is called a {deftech}_Hoare triple_.{TODO}[cite]
   In this framework, the postcondition of each statement should suffice to prove the precondition of the next one, and loops require a specified {deftech}_loop invariant_, which is a statement that must be true at the beginning of the loop and at the end of each iteration.
   Designated {deftech}_specification lemmas_ associate a function with a Hoare triple.
3. Applying the weakest-precondition semantics of a monadic program to a desired proof goal results in the precondition that must hold in order to prove the goal along with any missing steps such as loop invariants or proofs that a statement's precondition implies its postcondition.
   These missing steps are the _verification conditions_.
   The {tactic}`mvcgen` tactic performs this transformation, replacing the goal with its verification conditions.
   During this transformation, {tactic}`mvcgen` uses specification lemmas to discharge proofs about individual statements.
4. After supplying loop invariants, many verification conditions can in practice be discharged automatically.
   Those that cannot can be proven using either a {ref "tactic-ref-spred"}[special proof mode] or ordinary Lean tactics.


# Predicate Transformers

## Stateful Predicates

The predicate transformer semantics of monadic programs is based on a logic in which propositions may mention the program's state.
Here, “state” refers not only to mutable state, but also to read-only values such as those that are provided via {name}`ReaderT`.
Different monads have different state types available, but each individual state always has a type.
Given a list of state types, {name}`SPred` is a type of predicates over these states.

{docstring Std.Do.SPred}

::::leanSection
```lean -show
variable {P : Prop} {σ : List (Type u)}
```
Ordinary propositions that do not mention the state can be used as stateful predicates by adding a trivial universal quantification.
This is written with the syntax {lean (type := "SPred σ")}`⌜P⌝`.
:::syntax term (title := "Notation for `SPred`") (namespace := Std.Do)
```grammar
⌜$_:term⌝
```
{includeDocstring Std.Do.«term⌜_⌝»}
:::
::::

{docstring SPred.pure}

### Entailment

Stateful predicates are related by _entailment_.
Entailment of stateful predicates is defined as universally-quantified implication: if $`P` and $`Q` are predicates over a state $`\sigma`, then $`P` entails $`Q` (written $`P \vdash_s Q`) when $`∀ s : \sigma, P(s) → Q(s)`.

{docstring Std.Do.SPred.entails}

{docstring Std.Do.SPred.bientails}

:::syntax term (title := "Notation for `SPred`") (namespace := Std.Do)
```grammar
$_:term ⊢ₛ $_:term
```
{includeDocstring Std.Do.«term_⊢ₛ_»}

```grammar
⊢ₛ $_:term
```
{includeDocstring Std.Do.«term⊢ₛ_»}

```grammar
$_:term ⊣⊢ₛ $_:term
```

{includeDocstring Std.Do.«term_⊣⊢ₛ_»}
:::

:::leanSection
```lean -show
variable {σ : List (Type u)} {P Q : SPred σ}
```
The logic of stateful predicates includes an implication connective.
The difference between entailment and implication is that entailment is a statement in Lean's logic, while implication is internal to the stateful logic.
Given stateful predicates {lean}`P` and {lean}`Q` for state {lean}`σ`, {lean (type := "Prop")}`P ⊢ₛ Q` is a {lean}`Prop` while {lean (type := "SPred σ")}`spred(P → Q)` is an {lean}`SPred σ`.
:::

### Notation

The syntax of stateful predicates overlaps with that of ordinary Lean terms.
In particular, stateful predicates use the usual syntax for logical connectives and quantifiers.
The syntax associated with stateful predicates is automatically enabled in contexts such as pre- and postconditions where they are clearly intended; other contexts must explicitly opt in to the syntax using {keywordOf Std.Do.«termSpred(_)»}`spred`.
The usual meanings of these operators can be recovered by using the {keywordOf Std.Do.«termTerm(_)»}`term` operator.

:::syntax term (title := "Predicate Terms") (namespace := Std.Do)
{keywordOf Std.Do.«termSpred(_)»}`spred` indicates that logical connectives and quantifiers should be understood as those pertaining to stateful predicates, while {keywordOf Std.Do.«termTerm(_)»}`term` indicates that they should have the usual meaning.
```grammar
spred($t)
```
```grammar
term($t)
```
:::

### Connectives and Quantifiers

:::syntax term (title := "Predicate Connectives") (namespace := Std.Do)
```grammar
spred($_ ∧ $_)
```
Syntactic sugar for {name}`SPred.and`.

```grammar
spred($_ ∨ $_)
```
Syntactic sugar for {name}`SPred.or`.

```grammar
spred(¬ $_)
```
Syntactic sugar for {name}`SPred.not`.

```grammar
spred($_ → $_)
```
Syntactic sugar for {name}`SPred.imp`.

```grammar
spred($_ ↔ $_)
```
Syntactic sugar for {name}`SPred.iff`.
:::


{docstring SPred.and}

{docstring SPred.conjunction}

{docstring SPred.or}

{docstring SPred.not}

{docstring SPred.imp}

{docstring SPred.iff}

:::syntax term (title := "Predicate Quantifiers") (namespace := Std.Do)
```grammar
spred(∀ $x:ident, $_)
```
```grammar
spred(∀ $x:ident : $ty,  $_)
```
```grammar
spred(∀ ($x:ident $_* : $ty),  $_)
```
```grammar
spred(∀ _, $_)
```
```grammar
spred(∀ _ : $ty,  $_)
```
```grammar
spred(∀ (_ $_* : $ty),  $_)
```
Each form of universal quantification is syntactic sugar for an invocation of {name}`SPred.forall` on a function that takes the quantified variable as a parameter.

```grammar
spred(∃ $x:ident, $_)
```
```grammar
spred(∃ $x:ident : $ty,  $_)
```
```grammar
spred(∃ ($x:ident $_* : $ty),  $_)
```
```grammar
spred(∃ _, $_)
```
```grammar
spred(∃ _ : $ty,  $_)
```
```grammar
spred(∃ (_ $_* : $ty),  $_)
```
Each form of existential quantification is syntactic sugar for an invocation of {name}`SPred.exists` on a function that takes the quantified variable as a parameter.
:::

{docstring SPred.forall}

{docstring SPred.exists}


## Assertions

The language of assertions about monadic programs is parameterized by a {deftech}_postcondition shape_, which describes the inputs to and outputs from a computation in a given monad.
Preconditions may mention the initial values of the monad's state, while postconditions may mention the returned value, the final values of the monad's state, and must furthermore account for any exceptions that could have been thrown.
The postcondition shape of a given monad determines the states and exceptions in the monad.
{name}`PostShape.pure` describes a monad in which assertions may not mention any states, {name}`PostShape.arg` describes a state value, and {name}`PostShape.except` describes a possible exception.
Because these constructors can be continually added, the postcondition shape of a monad transformer can be defined in terms of the postcondition shape of the transformed monad.

{docstring PostShape}

{docstring PostShape.args}

{docstring Assertion}

{docstring PostCond}

:::syntax term (title := "Postconditions")
```grammar
⇓ $_* => $_
```
Syntactic sugar for a nested sequence of product constructors, terminating in {lean}`()`, in which the first element is an assertion about non-exceptional return values and the remaining elements are assertions about the exceptional cases for a postcondition.
:::


{docstring ExceptConds}

:::syntax term (title := "Exception-Free Postconditions")
```grammar
⇓ $_* => $_
```
{includeDocstring PostCond.noThrow}
:::

{docstring PostCond.noThrow}

:::syntax term (title := "Partial Postconditions")
```grammar
⇓? $_* => $_
```
{includeDocstring PostCond.mayThrow}
:::

{docstring PostCond.mayThrow}

:::syntax term (title := "Postcondition Entailment")
```grammar
$_ ⊢ₚ $_
```
Syntactic sugar for {name}`PostCond.entails`
:::

{docstring PostCond.entails}


:::syntax term (title := "Postcondition Conjunction")
```grammar
$_ ∧ₚ $_
```
Syntactic sugar for {name}`PostCond.and`
:::

{docstring PostCond.and}

:::syntax term (title := "Postcondition Implication")
```grammar
$_ →ₚ $_
```
Syntactic sugar for {name}`PostCond.imp`
:::

{docstring PostCond.imp}


## Predicate Transformers

A predicate transformer is a function from postconditions for some postcondition state into assertions for that state.
The function must be {deftech}_conjunctive_, which means it must distribute over {name}`PostCond.and`.

{docstring PredTrans}

{docstring PredTrans.Conjunctive}

{docstring PredTrans.Monotonic}

:::leanSection
```lean -show
variable {σ : List (Type u)} {ps : PostShape} {x y : PredTrans ps α} {Q : Assertion ps}
```
The {inst}`LE PredTrans` instance is defined in terms of their logical strength; one transformer is stronger than another if the result of applying it always entails the result of applying the other.
In other words, {lean}`∀ Q, y Q ⊢ₛ x Q`, then {lean}`x ≤ y`.
This means that stronger predicate transformers are considered greater than weaker ones.
:::

The weakest precondition semantics of a monad are provided by the {name}`WP` type class.
Instances of {name}`WP` determine the monad's postcondition shape and provide the logical rules for interpreting the monad's operations as a predicate transformer in its postcondition shape.

{docstring WP}

:::syntax term (title := "Weakest Preconditions")
```grammar
wp⟦$_ $[: $_]?⟧
```
{includeDocstring Std.Do.«termWp⟦_:_⟧»}
:::

### Weakest Precondition Monad Morphisms

{docstring WPMonad}

### Adequacy Theorems

Monads that can be invoked from pure code typically provide a invocation operator that takes any required input state as a parameter and returns either a value paired with an output state or some kind of exceptional value.
Examples include {name}`StateT.run`, {name}`ExceptT.run`, and {name}`Id.run`.
Adequacy theorems provide a bridge between statements about invocations of monadic programs and those programs' {tech}[weakest precondition] semantics as given by their {name}`WP` instances.
They show that a property about the invocation is true if its weakest precondition is true.

{docstring Id.of_wp_run_eq}

{docstring StateM.of_wp_run_eq}

{docstring StateM.of_wp_run'_eq}

{docstring StateM.of_wp_run'_eq}

{docstring ReaderM.of_wp_run_eq}

{docstring Except.of_wp}

{docstring EStateM.of_wp_run_eq}

## Hoare Triples

{docstring Triple}

::::syntax term (title := "Hoare Triples")
```grammar
⦃ $_ ⦄ $_ ⦃ $_ ⦄
```
:::leanSection
```lean -show
variable [WP m ps] {x : m α} {P : Assertion ps} {Q : PostCond α ps}
```
{lean}`⦃P⦄ x ⦃Q⦄` is syntactic sugar for {lean}`Triple x P Q`.
:::
::::

{docstring SVal}

{docstring Triple.and}

{docstring Triple.mp}

## Specification Lemmas

Specification lemmas associate Hoare triples with functions.
When {tactic}`mvcgen` encounters a function, it checks whether there are any registered specification lemmas and attempts to use them to discharge intermediate {tech}[verification conditions].
If there is no applicable specification lemma, then the connection between the statement's pre- and postconditions will become a verification condition.
Specification lemmas allow compositional reasoning about libraries of monadic code.

When applied to a theorem whose statement is a Hoare triple, the {attr}`spec` attribute registers the theorem as a specification lemma.
These lemmas are used in order of priority.
For theorems, the {keywordOf simpPre}`↑`, {keywordOf simpPost}`↑`, and {keyword}`←` specifiers are ignored.

The {attr}`spec` attribute may also be applied to definitions.
On definitions, it indicates that the definition should be simplified during verification condition generation.
For definitions, {attr}`spec` uses the {keywordOf simpPre}`↑`, {keywordOf simpPost}`↑`, and {keyword}`←` specifiers in the same manner as {tactic}`simp`.

:::syntax attr (title := "Specification Lemmas")
```grammar
spec $_? $_? $[$_:prio]?
```
{includeDocstring Lean.Parser.Attr.spec}
:::


## Specification Helpers

These types are used to make it easier to write invariants.

{docstring List.Cursor}

{docstring List.Cursor.at}

{docstring List.Cursor.pos}

{docstring List.Cursor.current}

{docstring List.Cursor.tail}

{docstring List.Cursor.begin}

{docstring List.Cursor.end}

{docstring Invariant}

{docstring Invariant.withEarlyReturn}

# Verification Conditions

The {tactic}`mvcgen` tactic converts a goal that's expressed in terms of {name}`SPred` and weakest preconditions to a set of invariants and verification conditions that, together, suffice to prove the original goal.
In particular, {tech}[Hoare triples] are defined in terms of weakest preconditions


# Proof Mode

Stateful goals can be proven using a special _proof mode_ in which goals are rendered with two contexts of hypotheses: the ordinary Lean context, which contains Lean variables, and a special stateful context, which contains assumptions about the monadic state.
In the proof mode, the goal is an {name}`SPred`, rather than a {lean}`Prop`, and the entire goal is equivalent to an entailment relation ({name}`SPred.entails`) from the conjunction of the hypotheses to the conclusion.

:::syntax Std.Tactic.Do.mgoalStx (title := "Proof Mode Goals")
Proof mode goals are rendered as a series of named hypotheses, one per line, followed by {keywordOf Std.Tactic.Do.mgoalStx}`⊢ₛ` and a goal.
```grammar
$[$_:ident : $t:term]*
⊢ₛ $_:term
```
:::

In the proof mode, special tactics manipulate the stateful context.
These tactics are described in {ref "tactic-ref-spred"}[their own section in the tactic reference].

When working with concrete monads, {tactic}`mvcgen` typically does not result in stateful proof goals—they are simplified away.
However, monad-polymorphic theorems can lead to stateful goals remaining.

:::example "Stateful Proofs"
```imports
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```
The function {name}`bump` increments its state by the indicated amount and returns the resulting value.
```lean
variable [Monad m] [WPMonad m ps]
def bump (n : Nat) : StateT Nat m Nat := do
  modifyThe Nat (· + n)
  getThe Nat
```

This specification lemma for {name}`bump` is proved in an intentionally low-level manner to demonstrate the intermediate proof states:
```lean
theorem bump_correct : ⦃ fun n => ⌜n = k⌝ ⦄ bump (m := m) i ⦃ ⇓ r n => ⌜r = n ∧ n = k + i⌝  ⦄ := by
  mvcgen
  unfold bump
  unfold modifyThe
  mspec
  mspec
  mpure_intro
  constructor
  . trivial
  . simp_all
```

The lemma can also be proved using only the simplifier:
```lean
theorem bump_correct' : ⦃ fun n => ⌜n = k⌝ ⦄ bump (m := m) i ⦃ ⇓ r n => ⌜r = n ∧ n = k + i⌝  ⦄ := by
  mvcgen
  simp_all [bump]
```
:::
