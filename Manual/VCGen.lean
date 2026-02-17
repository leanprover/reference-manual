/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual

import Manual.Meta
import Manual.Papers

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
%%%

:::tutorials
 * {ref "mvcgen-tactic-tutorial" (remote := "tutorials")}[Verifying Imperative Programs Using `mvcgen`]
:::

The {tactic}`mvcgen` tactic implements a _monadic verification condition generator_:
It breaks down a goal involving a program written using Lean's imperative {keywordOf Lean.Parser.Term.do}`do` notation into a number of smaller {tech}_verification conditions_ ({deftech}[VCs]) that are sufficient to prove the goal.
In addition to a reference that describes the use of {tactic}`mvcgen`, this chapter includes a {ref "mvcgen-tactic-tutorial" (remote := "tutorials")}[tutorial] that can be read independently of the reference.

In order to use the {tactic}`mvcgen` tactic, {module}`Std.Tactic.Do` must be imported and the namespace {namespace}`Std.Do` must be opened.


# Overview



The workflow of {tactic}`mvcgen` consists of the following:

1. Monadic programs are re-interpreted according to a {tech}[predicate transformer semantics].
   An instance of {name}`WP` determines the monad's interpretation.
   Each program is interpreted as a mapping from arbitrary {tech}[postconditions] to the {tech}[weakest precondition] that would ensure the postcondition.
   This step is invisible to most users, but library authors who want to enable their monads to work with {tactic}`mvcgen` need to understand it.
2. Programs are composed from smaller programs.
   Each statement in a {keywordOf Lean.Parser.Term.do}`do`-block is associated with a predicate transformer, and there are general-purpose rules for combining these statements with sequencing and control-flow operators.
   A statement with its pre- and postconditions is called a {tech}_Hoare triple_.
   In a program, the postcondition of each statement should suffice to prove the precondition of the next one, and loops require a specified {deftech}_loop invariant_, which is a statement that must be true at the beginning of the loop and at the end of each iteration.
   Designated {tech}_specification lemmas_ associate functions with Hoare triples that specify them.
3. Applying the weakest-precondition semantics of a monadic program to a desired proof goal results in the precondition that must hold in order to prove the goal.
   Any missing steps such as loop invariants or proofs that a statement's precondition implies its postcondition become new subgoals.
   These missing steps are called the {deftech}_verification conditions_.
   The {tactic}`mvcgen` tactic performs this transformation, replacing the goal with its verification conditions.
   During this transformation, {tactic}`mvcgen` uses specification lemmas to discharge proofs about individual statements.
4. After supplying loop invariants, many verification conditions can in practice be discharged automatically.
   Those that cannot can be proven using either a {ref "tactic-ref-spred"}[special proof mode] or ordinary Lean tactics, depending on whether they are expressed in the logic of program assertions or as ordinary propositions.


# Predicate Transformers

A {deftech}_predicate transformer semantics_ is an interpretation of programs as functions from predicates to predicates, rather than values to values.
A {deftech}_postcondition_ is an assertion that holds after running a program, while a {deftech}_precondition_ is an assertion that must hold prior to running the program in order for the postcondition to be guaranteed to hold.

The predicate transformer semantics used by {tactic}`mvcgen` transforms postconditions into the {deftech}_weakest preconditions_ under which the program will ensure the postcondition.
An assertion $`P` is weaker than $`P'` if, in all states, $`P'` suffices to prove $`P`, but $`P` does not suffice to prove $`P'`.
Logically equivalent assertions are considered to be equal.

The predicates in question are stateful: they can mention the program's current state.
Furthermore, postconditions can relate the return value and any exceptions thrown by the program to the final state.
{name}`SPred` is a type of predicates that is parameterized over a monadic state, expressed as a list of the types of the fields that make up the state.
The usual logical connectives and quantifiers are defined for {name}`SPred`.
Each monad that can be used with {tactic}`mvcgen` is assigned a state type by an instance of {name}`WP`, and {name}`Assertion` is the corresponding type of assertions for that monad, which is used for preconditions.
{name}`Assertion` is a wrapper around {name}`SPred`: while {name}`SPred` is parameterized by a list of states types, {name}`Assertion` is parameterized by a more informative type that it translates to a list of state types for {name}`SPred`.
A {name}`PostCond` pairs an {name}`Assertion` about a return value with assertions about potential exceptions; the available exceptions are also specified by the monad's {name}`WP` instance.


## Stateful Predicates

The predicate transformer semantics of monadic programs is based on a logic in which propositions may mention the program's state.
Here, “state” refers not only to mutable state, but also to read-only values such as those that are provided via {name}`ReaderT`.
Different monads have different state types available, but each individual state always has a type.
Given a list of state types, {name}`SPred` is a type of predicates over these states.

{name}`SPred` is not inherently tied to the monadic verification framework.
The related {name}`Assertion` computes a suitable {name}`SPred` for a monad's state as expressed via its {name}`WP` instance's {name}`PostShape` output parameter.

{docstring Std.Do.SPred}

::::leanSection
```lean -show
variable {P : Prop} {σ : List (Type u)}
```
Ordinary propositions that do not mention the state can be used as stateful predicates by adding a trivial universal quantification.
This is written with the syntax {lean (type := "SPred σ")}`⌜P⌝`, which is syntactic sugar for {name}`SPred.pure`.
:::syntax term (title := "Notation for `SPred`") (namespace := Std.Do)
```grammar
⌜$_:term⌝
```
{includeDocstring Std.Do.«term⌜_⌝»}
:::
::::

{docstring SPred.pure}

:::example "Stateful Predicates"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```
The predicate {name}`ItIsSecret` expresses that a state of type {name}`String` is {lean}`"secret"`:
```lean
def ItIsSecret : SPred [String] := fun s => ⌜s = "secret"⌝
```
:::

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

### Stateful Values

Just as {name}`SPred` represents predicate over states, {name}`SVal` represents a value that is derived from a state.

{docstring SVal}

{docstring SVal.getThe}

{docstring SVal.StateTuple}

{docstring SVal.curry}

{docstring SVal.uncurry}


## Assertions

The language of assertions about monadic programs is parameterized by a {deftech}_postcondition shape_, which describes the inputs to and outputs from a computation in a given monad.
Preconditions may mention the initial values of the monad's state, while postconditions may mention the returned value, the final values of the monad's state, and must furthermore account for any exceptions that could have been thrown.
The postcondition shape of a given monad determines the states and exceptions in the monad.
{name}`PostShape.pure` describes a monad in which assertions may not mention any states, {name}`PostShape.arg` describes a state value, and {name}`PostShape.except` describes a possible exception.
Because these constructors can be continually added, the postcondition shape of a monad transformer can be defined in terms of the postcondition shape of the underlying transformed monad.
Behind the scenes, an {name}`Assertion` is translated into an appropriate {name}`SPred` by translating the postcondition shape into a list of state types, discarding exceptions.

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

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {P : Assertion ps} {α  : Type u}  {prog : m α} {Q' : α → Assertion ps}
```
Postconditions for programs that might throw exceptions come in two varieties. The {deftech}_total correctness interpretation_ {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` asserts that, given {lean}`P` holds, then {lean}`prog` terminates _and_ {lean}`Q'` holds for the result. The {deftech}_partial correctness interpretation_ {lean}`⦃P⦄ prog ⦃⇓? r => Q' r⦄` asserts that, given {lean}`P` holds, and _if_ {lean}`prog` terminates _then_ {lean}`Q'` holds for the result.
:::


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

Predicate transformers form a monad.
The {name}`pure` operator is the identity transformer; it simply instantiates the postcondition with the its argument.
The {name}`bind` operator composes predicate transformers.

{docstring PredTrans.pure}

{docstring PredTrans.bind}

The helper operators {name}`PredTrans.pushArg`, {name}`PredTrans.pushExcept`, and {name}`PredTrans.pushOption` modify a predicate transformer by adding a standard side effect.
They are used to implement the {name}`WP` instances for transformers such as {name}`StateT`, {name}`ExceptT`, and {name}`OptionT`; they can also be used to implement monads that can be thought of in terms of one of these.
For example, {name}`PredTrans.pushArg` is typically used for state monads, but can also be used to implement a reader monad's instance, treating the reader's value as read-only state.

{docstring PredTrans.pushArg}

{docstring PredTrans.pushExcept}

{docstring PredTrans.pushOption}

### Weakest Preconditions

The {tech}[weakest precondition] semantics of a monad are provided by the {name}`WP` type class.
Instances of {name}`WP` determine the monad's postcondition shape and provide the logical rules for interpreting the monad's operations as a predicate transformer in its postcondition shape.

{docstring WP}

:::syntax term (title := "Weakest Preconditions")
```grammar
wp⟦$_ $[: $_]?⟧
```
{includeDocstring Std.Do.«termWp⟦_:_⟧»}
:::

### Weakest Precondition Monad Morphisms

Most of the built-in specification lemmas for {tactic}`mvcgen` relies on the presence of a {name}`WPMonad` instance, in addition to the {name}`WP` instance.
In addition to being lawful, weakest preconditions of the monad's implementations of {name}`pure` and {name}`bind` should correspond to the {name}`pure` and {name}`bind` operators for the predicate transformer monad.
Without a {name}`WPMonad` instance, {tactic}`mvcgen` typically returns the original proof goal unchanged.

{docstring WPMonad}

:::example "Missing `WPMonad` Instance"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

This reimplementation of {name}`Id` has a {name}`WP` instance, but no {name}`WPMonad` instance:
```lean
def Identity (α : Type u) : Type u := α

variable {α : Type u}

def Identity.run (act : Identity α) : α := act

instance : Monad Identity where
  pure x := x
  bind x f := f x

instance : WP Identity .pure where
  wp x := PredTrans.pure x

theorem Identity.of_wp_run_eq {x : α} {prog : Identity α}
    (h : Identity.run prog = x) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a => ⟨P a⟩)) → P x := by
  intro h'
  simpa [← h] using h'
```

```lean -show
instance : LawfulMonad Identity :=
  LawfulMonad.mk' Identity
    (id_map := fun _ => rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)
```

The missing instance prevents {tactic}`mvcgen` from using its specifications for {name}`pure` and {name}`bind`.
This tends to show up as a verification condition that's equal to the original goal.
This function that reverses a list:
```lean
def rev (xs : List α) : Identity (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out
```
It is correct if it is equal to {name}`List.reverse`.
However, {tactic}`mvcgen` does not make the goal easier to prove:
```lean +error -keep (name := noInst)
theorem rev_correct :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_wp_run_eq h
  mvcgen [rev]
```
```leanOutput noInst
unsolved goals
case vc1.a
α✝ : Type u_1
xs x : List α✝
h : (rev xs).run = x
out✝ : List α✝ := []
⊢ (wp⟦do
      let r ←
        forIn xs out✝ fun x r => do
            pure PUnit.unit
            pure (ForInStep.yield (x :: r))
      pure r⟧
    (PostCond.noThrow fun a => { down := a = xs.reverse })).down
```
When the verification condition is just the original problem, without even any simplification of {name}`bind`, the problem is usually a missing {name}`WPMonad` instance.
The issue can be resolved by adding a suitable instance:
```lean
instance : WPMonad Identity .pure where
  wp_pure _ := rfl
  wp_bind _ _ := rfl
```
With this instance, and a suitable invariant, {tactic}`mvcgen` and {tactic}`grind` can prove the theorem.
```lean
theorem rev_correct :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_wp_run_eq h
  simp only [rev]
  mvcgen invariants
  · ⇓⟨xs, out⟩ =>
    ⌜out = xs.prefix.reverse⌝
  with grind
```
:::

### Adequacy Lemmas
%%%
tag := "mvcgen-adequacy"
%%%

Monads that can be invoked from pure code typically provide a invocation operator that takes any required input state as a parameter and returns either a value paired with an output state or some kind of exceptional value.
Examples include {name}`StateT.run`, {name}`ExceptT.run`, and {name}`Id.run`.
{deftech}_Adequacy lemmas_ provide a bridge between statements about invocations of monadic programs and those programs' {tech}[weakest precondition] semantics as given by their {name}`WP` instances.
They show that a property about the invocation is true if its weakest precondition is true.

{docstring Id.of_wp_run_eq}

{docstring StateM.of_wp_run_eq}

{docstring StateM.of_wp_run'_eq}

{docstring ReaderM.of_wp_run_eq}

{docstring Except.of_wp_eq}

{docstring EStateM.of_wp_run_eq}

## Hoare Triples

A {deftech}_Hoare triple_{citep hoare69}[] consists of a precondition, a program, and a postcondition.
Running the program in a state for which the precondition is true results in a state where the postcondition is true.

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

{docstring Triple.and}

{docstring Triple.mp}

## Specification Lemmas

{deftech}_Specification lemmas_ are designated theorems that associate Hoare triples with functions.
When {tactic}`mvcgen` encounters a function, it checks whether there are any registered specification lemmas and attempts to use them to discharge intermediate {tech}[verification conditions].
If there is no applicable specification lemma, then the connection between the statement's pre- and postconditions will become a verification condition.
Specification lemmas allow compositional reasoning about libraries of monadic code.

When applied to a theorem whose statement is a Hoare triple, the {attr}`spec` attribute registers the theorem as a specification lemma.
These lemmas are used in order of priority.

The {attr}`spec` attribute may also be applied to definitions.
On definitions, it indicates that the definition should be unfolded during verification condition generation.

:::syntax attr (title := "Specification Lemmas")
```grammar
spec $[$_:prio]?
```
{includeDocstring Lean.Parser.Attr.spec}
:::

Universally-quantified variables in specification lemmas can be used to relate input states to output states and return values.
These variables are referred to as {deftech}_schematic variables_.

:::example "Schematic Variables"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

The function {name}`double` doubles the value of a {name}`Nat` state:
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
Its specification should _relate_ the initial and final states, but it cannot know their precise values.
The specification uses a schematic variable to stand for the initial state:
```lean
theorem double_spec :
    ⦃ fun s => ⌜s = n⌝ ⦄ double ⦃ ⇓ () s => ⌜s = 2 * n⌝ ⦄ := by
  simp [double]
  mvcgen with grind
```

The assertion in the precondition is a function because the {name}`PostShape` of {lean}`StateM Nat` is {lean (type := "PostShape.{0}")}`.arg Nat .pure`, and {lean}`Assertion (.arg Nat .pure)` is {lean}`SPred [Nat]`.

:::
```lean -show -keep
-- Test preceding examples' claims
#synth WP (StateM Nat) (.arg Nat .pure : PostShape.{0})
example : Assertion (.arg Nat .pure) = SPred [Nat] := rfl
```

## Invariant Specifications

These types are used in invariants.
The {tech}[specification lemmas] for {name}`ForIn.forIn` and {name}`ForIn'.forIn'` take parameters of type {name}`Invariant`, and {tactic}`mvcgen` ensures that invariants are not accidentally generated by other automation.

{docstring Invariant}

{docstring Invariant.withEarlyReturn}

Invariants use lists to model the sequence of values in a {keywordOf Lean.Parser.Term.doFor}`for` loop.
The current position in the loop is tracked with a {name}`List.Cursor` that represents a position in a list as a combination of the elements to the left of the position and the elements to the right.
This type is not a traditional zipper, in which the prefix is reversed for efficient movement: it is intended for use in specifications and proofs, not in run-time code, so the prefix is in the original order.

{docstring List.Cursor}

{docstring List.Cursor.at}

{docstring List.Cursor.pos}

{docstring List.Cursor.current}

{docstring List.Cursor.tail}

{docstring List.Cursor.begin}

{docstring List.Cursor.end}


# Verification Conditions

The {tactic}`mvcgen` tactic converts a goal that's expressed in terms of {name}`SPred` and weakest preconditions to a set of invariants and verification conditions that, together, suffice to prove the original goal.
In particular, {tech}[Hoare triples] are defined in terms of weakest preconditions, so {tactic}`mvcgen` can be used to prove them.

:::leanSection
```lean -show
variable [Monad m] [WPMonad m ps] {e : m α} {P : Assertion ps} {Q : PostCond α ps}
```
The verification conditions for a goal are generated as follows:
1. A number of simplifications and rewrites are applied.
2. The goal should now be of the form {lean}`P ⊢ₛ wp⟦e⟧ Q` (that is, an entailment from some set of stateful assumptions to the weakest precondition that implies a desired postcondition).
3. {tech}[Reducible] constants and definitions marked {attrs}`@[spec]` in the expression {lean}`e` are unfolded.
4. If the expression is an application of an {tech}[auxiliary matching function] or a conditional ({name}`ite` or {name}`dite`), then it is first simplified.
   The {tech (key := "match discriminant")}[discriminant] of each matcher is simplified, and the entire term is reduced in an attempt to eliminate the matcher or conditional.
   If this fails, then a new goal is generated for each branch.
5. If the expression is an application of a constant, then the applicable lemmas marked {attrs}`@[spec]` are attempted in priority order.
   Lean includes specification lemmas for constants such as {name Bind.bind}`bind`, {name Pure.pure}`pure`, and {name}`ForIn.forIn` that result from desugaring {keywordOf Lean.Parser.Term.do}`do`-notation.
   Instantiating the lemma will sometimes discharge its premises, in particular schematic variables due to definitional equalities with the goal.
   Assumptions of type {name}`Invariant` are never instantiated this way, however.
   If the spec lemma's precondition or postcondition do not exactly match those of the goal, then new metavariables are created that prove the necessary entailments.
   If these cannot be immediately discharged using simple automation that attempts to use local assumptions and decomposes conjunctions in postconditions, then they remain as verification conditions.
6. Each remaining goal created by this process is recursively processed for verification conditions if it has the form {lean}`P ⊢ₛ wp⟦e⟧ Q`. If not, it is added to the set of invariants or verification conditions.
7. The resulting subgoals for invariants and verification conditions are assigned suitable names in the proof state.
8. Depending on the tactic's configuration parameters, {tactic}`mvcgen_trivial` and {tactic}`mleave` are attempted in each verification condition.
:::

Verification condition generation can be improved by defining appropriate {tech}[specification lemmas] for a library.
The presence of good specification lemmas results in fewer generated verification conditions.
Additionally, ensuring that the {tech}[simp normal form] of terms is suitable for pattern matching, and that there are sufficient lemmas in the default simp set to reduce every possible term to that normal form, can lead to more conditionals and pattern matches being eliminated.

# Enabling `mvcgen` For Monads

If a monad is implemented in terms of {tech}[monad transformers] that are provided by the Lean standard library, such as {name}`ExceptT` and {name}`StateT`, then it should not require additional instances.
Other monads will require instances of {name}`WP`, {name}`LawfulMonad`, and {name}`WPMonad`.
The tactic has been designed to support monads that model single-threaded control with state that might be interrupted; in other words, the effects that are present in ordinary imperative programming.
More exotic effects have not yet been investigated.

Once the basic instances are provided, the next step is to prove an {ref "mvcgen-adequacy"}[adequacy lemma].
This lemma should show that the weakest precondition for running the monadic computation and asserting a desired predicate is in fact sufficient to prove the predicate.

In addition to the definition of the monad, typical libraries provide a set of primitive operators.
Each of these should be provided with a {tech}[specification lemma].
It may additionally be useful to make the internals of the state private, and export a carefully-designed set of assertion operators.

The specification lemmas for the library's primitive operators should ideally be precise specifications of the operators as predicate transformers.
While it's often easier to think in terms of how the operator transforms an input state into an output state, {tech}[verification condition] generation will work more reliably when postconditions are completely free.
This allows automation to instantiate the postcondition with the exact precondition of the next statement, rather than needing to show an entailment.
In other words, specifications that specify the precondition as a function of the postcondition work better in practice than specifications that merely relate the pre- and postconditions.

:::example "Schematic Postconditions"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

The function {name}`double` doubles a natural number state:
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
Thinking chronologically, a reasonable specification is that value of the output state is twice that of the input state.
This is expressed using a schematic variable that stands for the initial state:
```lean -keep
theorem double_spec :
    ⦃ fun s => ⌜s = n⌝ ⦄ double ⦃ ⇓ () s => ⌜s = 2 * n⌝ ⦄ := by
  simp [double]
  mvcgen with grind
```
However, an equivalent specification that treats the postcondition schematically will lead to smaller verification conditions when {name}`double` is used in other functions:
```lean
@[spec]
theorem better_double_spec {Q : PostCond Unit (.arg Nat .pure)} :
    ⦃ fun s => Q.1 () (2 * s) ⦄ double ⦃ Q ⦄ := by
  simp [double]
  mvcgen with grind
```
The first projection of the postcondition is its stateful assertion.
Now, the precondition merely states that the postcondition should hold for double the initial state.
:::

:::example "A Logging Monad"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

The monad {name}`LogM` maintains an append-only log during a computation:
```lean
structure LogM (β : Type u) (α : Type v) : Type (max u v) where
  log : Array β
  value : α

instance : Monad (LogM β) where
  pure x := ⟨#[], x⟩
  bind x f :=
    let { log, value } := f x.value
    { log := x.log ++ log, value }
```
It has a {name}`LawfulMonad` instance as well.
```lean -show
instance : LawfulMonad (LogM β) where
  map_const := rfl
  id_map x := rfl
  seqLeft_eq x y := rfl
  seqRight_eq x y := rfl
  pure_seq g x := by
    simp [pure, Seq.seq, Functor.map]
  bind_pure_comp f x := by
    simp [bind, Functor.map]
  bind_map f x := by
    simp [bind, Seq.seq]
  pure_bind x f := by
    simp [pure, bind]
  bind_assoc x f g := by
    simp [bind]
```

The log can be written to using {name}`log`, and a value and the associated log can be computed using {name}`LogM.run`.
```lean
def log (v : β) : LogM β Unit := { log := #[v], value := () }

def LogM.run (x : LogM β α) : α × Array β := (x.value, x.log)
```

Rather than writing it from scratch, the {name}`WP` instance uses {name}`PredTrans.pushArg`.
This operator was designed to model state monads, but {name}`LogM` can be seen as a state monad that can only append to the state.
This appending is visible in the body of the instance, where the initial state and the log that resulted from the action are appended:
```lean
instance : WP (LogM β) (.arg (Array β) .pure) where
  wp
    | { log, value } =>
      PredTrans.pushArg (fun s => PredTrans.pure (value, s ++ log))
```

The {name}`WPMonad` instance also benefits from the conceptual model as a state monad and admits very short proofs:
```lean
instance : WPMonad (LogM β) (.arg (Array β) .pure) where
  wp_pure x := by
    ext
    simp [wp]

  wp_bind _ _ := by
    ext
    simp [wp]
```

The adequacy lemma has one important detail: the result of the weakest precondition transformation is applied to the empty array.
This is necessary because the logging computation has been modeled as an append-only state, so there must be some initial state.
Semantically, the empty array is the correct choice so as to not place items in a log that don't come from the program; technically, it must also be a value that commutes with the append operator on arrays.
```lean
theorem LogM.of_wp_run_eq {x : α × Array β} {prog : LogM β α}
    (h : LogM.run prog = x) (P : α × Array β → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ v l => ⌜P (v, l)⌝) #[]) → P x := by
  rw [← h]
  intro h'
  simp [wp] at h'
  exact h'
```

Next, each operator in the library should be provided with a specification lemma.
There is only one: {name}`log`.
For new monads, these proofs must often break the abstraction boundaries of {tech}[Hoare triples] and weakest preconditions; the specifications that they provide can then be used abstractly by clients of the library.
```lean
theorem log_spec {x : β} :
    ⦃ fun s => ⌜s = s'⌝ ⦄ log x ⦃ ⇓ () s => ⌜s = s'.push x⌝ ⦄ := by
  simp [log, Triple, wp]
```

A better specification for {name}`log` uses a schematic postcondition:
```lean
variable {Q : PostCond Unit (.arg (Array β) .pure)}

@[spec]
theorem log_spec_better {x : β} :
    ⦃ fun s => Q.1 () (s.push x) ⦄ log x ⦃ Q ⦄ := by
  simp [log, Triple, wp]
```

A function {name}`logUntil` that logs all the natural numbers up to some bound will always result in a log whose length is equal to its argument:
```lean
def logUntil (n : Nat) : LogM Nat Unit := do
  for i in 0...n do
    log i

theorem logUntil_length : (logUntil n).run.2.size = n := by
  generalize h : (logUntil n).run = x
  unfold logUntil at h
  apply LogM.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, _⟩ s => ⌜xs.pos = s.size⌝
  with
    simp_all [List.Cursor.pos] <;>
    grind [Std.PRange.Nat.size_rco, Std.Rco.length_toList]
```
:::

# Proof Mode
%%%
tag := "mvcgen-proof-mode"
%%%

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
```imports -show
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
theorem bump_correct :
      ⦃ fun n => ⌜n = k⌝ ⦄
      bump (m := m) i
      ⦃ ⇓ r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  mintro n_eq_k
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
theorem bump_correct' :
    ⦃ fun n => ⌜n = k⌝ ⦄
    bump (m := m) i
    ⦃ ⇓ r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  mintro _
  simp_all [bump]
```
:::
