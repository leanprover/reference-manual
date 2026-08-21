/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Std.WP
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

open Std.WP Lean.Order

#doc (Manual) "The `vcgen` tactic" =>
%%%
tag := "vcgen-tactic"
%%%

:::tutorials
 * {ref "vcgen-tactic-tutorial" (remote := "tutorials")}[Verifying Imperative Programs Using `vcgen`]
:::

The {tactic}`vcgen` tactic implements a _monadic verification condition generator_:
It breaks down a goal involving a program written using Lean's imperative {keywordOf Lean.Parser.Term.do}`do` notation into a number of smaller {tech}_verification conditions_ ({deftech (key := "vcgen VCs")}[VCs]) that are sufficient to prove the goal.
In addition to a reference that describes the use of {tactic}`vcgen`, this chapter includes a {ref "vcgen-tactic-tutorial" (remote := "tutorials")}[tutorial] that can be read independently of the reference.

In order to use the {tactic}`vcgen` tactic, {module}`Std.WP` and {module}`Std.Tactic.Do` must be imported and the namespaces {namespace}`Std.WP` and {namespace}`Lean.Order` must be opened.


# Overview



The workflow of {tactic}`vcgen` consists of the following:

1. Monadic programs are re-interpreted according to a {tech}[predicate transformer semantics].
   An instance of {name}`WP` determines the monad's interpretation.
   Each program is interpreted as a mapping from arbitrary {tech}[postconditions] to the {tech}[weakest precondition] that would ensure the postcondition.
   This step is invisible to most users, but library authors who want to enable their monads to work with {tactic}`vcgen` need to understand it.
2. Programs are composed from smaller programs.
   Each statement in a {keywordOf Lean.Parser.Term.do}`do`-block is associated with a predicate transformer, and there are general-purpose rules for combining these statements with sequencing and control-flow operators.
   A statement with its pre- and postconditions is called a {tech}_Hoare triple_.
   In a program, the postcondition of each statement should suffice to prove the precondition of the next one, and loops require a specified {deftech (key := "vcgen loop invariant")}_loop invariant_, which is a statement that must be true at the beginning of the loop and at the end of each iteration.
   Designated {tech}_specification lemmas_ associate functions with Hoare triples that specify them.
3. Applying the weakest-precondition semantics of a monadic program to a desired proof goal results in the precondition that must hold in order to prove the goal.
   Any missing steps such as loop invariants or proofs that a statement's precondition implies its postcondition become new subgoals.
   These missing steps are called the {deftech (key := "vcgen verification conditions")}_verification conditions_.
   The {tactic}`vcgen` tactic performs this transformation, replacing the goal with its verification conditions.
   During this transformation, {tactic}`vcgen` uses specification lemmas to discharge proofs about individual statements.
4. After supplying loop invariants, many verification conditions can in practice be discharged automatically.
   Those that cannot are ordinary Lean goals, provable with ordinary Lean tactics or with the `grind`-mode step of the `with` clause.


# Predicate Transformers

A {deftech (key := "vcgen predicate transformer semantics")}_predicate transformer semantics_ is an interpretation of programs as functions from predicates to predicates, rather than values to values.
A {deftech (key := "vcgen postcondition")}_postcondition_ is an assertion that holds after running a program, while a {deftech (key := "vcgen precondition")}_precondition_ is an assertion that must hold prior to running the program in order for the postcondition to be guaranteed to hold.

The predicate transformer semantics used by {tactic}`vcgen` transforms postconditions into the {deftech (key := "vcgen weakest preconditions")}_weakest preconditions_ under which the program will ensure the postcondition.
An assertion $`P` is weaker than $`P'` if, in all states, $`P'` suffices to prove $`P`, but $`P` does not suffice to prove $`P'`.
Logically equivalent assertions are considered to be equal.

The predicates in question can be stateful: they can mention the program's current state.
Furthermore, postconditions can relate the return value and any exceptions thrown by the program to the final state.
Each monad that can be used with {tactic}`vcgen` is assigned an assertion type and an exception postcondition type by an instance of {name}`WP`.
An assertion type is a complete lattice; the type class {name}`Assertion` expresses this requirement.
For a state monad such as {lean}`StateM Nat`, an assertion is a predicate on the state, of type {lean}`Nat → Prop`.
A postcondition additionally takes the return value as its first argument, and the exception postcondition covers each exception that the monad can throw.


## Assertion Lattices

The predicate transformer semantics of monadic programs is based on a logic in which propositions may mention the program's state.
Here, “state” refers not only to mutable state, but also to read-only values such as those that are provided via {name}`ReaderT`.
Different monads have different assertion types, and the type class {name}`Assertion` captures what the framework requires of them: an assertion type is a complete lattice.

{docstring Assertion}

The lattice structure provides the logical vocabulary of assertions:

* The order {name Lean.Order.PartialOrder.rel}`⊑` is entailment.
* The meet {name Lean.Order.meet}`⊓` is conjunction and the join {name Lean.Order.join}`⊔` is disjunction.
* The top element {name Lean.Order.top}`⊤` is the trivial assertion and the bottom element {name Lean.Order.bot}`⊥` is the absurd assertion.
* The indexed supremum {name Lean.Order.iSup}`⨆` is existential quantification and the indexed infimum {name Lean.Order.iInf}`⨅` is universal quantification.
* The Heyting implication {name Lean.Order.himp}`⇨` is implication internal to the assertion language.

The difference between entailment and implication is that entailment is a statement in Lean's logic, while implication is internal to the assertion language: for assertions `P` and `Q`, `P ⊑ Q` is a {lean}`Prop` while `P ⇨ Q` is again an assertion.

The lattice operations on {lean}`Prop` coincide with the ordinary logical connectives, with entailment being implication.
The lattice operations on a function type such as {lean}`Nat → Prop` operate pointwise, so entailment of state predicates is universally-quantified implication.

::::leanSection
```lean -show
universe u
variable {P : Prop} {Pred : Type u} [Assertion Pred]
```
Ordinary propositions that do not mention the state can be embedded into any assertion lattice.
This is written with the syntax {lean (type := "Pred")}`⌜P⌝`, which is notation for {name}`Lean.Order.CompleteLattice.ofProp`.
:::syntax term (title := "Embedding Propositions") (namespace := Lean.Order)
```grammar
⌜$_:term⌝
```
{includeDocstring Lean.Order.CompleteLattice.ofProp}
:::
::::

{docstring Lean.Order.CompleteLattice.ofProp}

:::example "Assertions for State Monads"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option mvcgen.warning false

```
The predicate {name}`ItIsSecret` expresses that a state of type {name}`String` is {lean}`"secret"`:
```lean
def ItIsSecret : String → Prop := fun s => ⌜s = "secret"⌝
```
Entailment between such assertions is pointwise implication:
```lean
example : ItIsSecret ⊑ (⌜True⌝ : String → Prop) := by
  simp [ItIsSecret, PartialOrder.rel]
```
:::

### Reading Values from the State

An assertion frequently constrains the value that a function of the state evaluates to.
The type class {name}`Assertion.NondetFun` equips an assertion lattice with a notion of total nondeterministic functions, and {name}`Assertion.NondetFun.EvalsTo` relates such a function to its value inside the assertion lattice.
The specification lemmas for reader-like operations are stated in terms of {name}`Assertion.NondetFun.EvalsTo`.

{docstring Assertion.NondetFun}

{docstring Assertion.NondetFun.EvalsTo}


## Exception Postconditions

A postcondition for successful termination is a function from the return value to an assertion.
Programs that can throw exceptions additionally require an {deftech (key := "vcgen exception postcondition")}_exception postcondition_, an assertion that covers each exception that the monad can throw.
The exception postcondition type of a given monad is determined by its {name}`WP` instance.
A monad without exceptions uses {name}`EPost.Nil`, and each exception layer contributes one branch through {name}`EPost.Cons`.
Because these constructors can be continually added, the exception postcondition type of a monad transformer can be defined in terms of that of the underlying transformed monad.

{docstring EPost.Nil}

{docstring EPost.Cons}

{docstring EPost.Cons.head}

{docstring EPost.Cons.tail}

The notation `EPost⟨e₁, e₂, ...⟩` abbreviates the type of exception postconditions with branches `e₁, e₂, ...`, and the notation `epost⟨v₁, v₂, ...⟩` builds a value of such a type from the branch values.

Exception postconditions form assertion lattices themselves: {name}`EPost.Nil` carries the trivial lattice, and {name}`EPost.Cons` is ordered componentwise.

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {P : Pred} {α : Type u} {prog : m α} {Q' : α → Pred}
```
Triples for programs that might throw exceptions come in two varieties. The {deftech (key := "vcgen total correctness interpretation")}_total correctness interpretation_ {lean}`⦃P⦄ prog ⦃Q'⦄` asserts that, given {lean}`P` holds, then {lean}`prog` terminates normally _and_ {lean}`Q'` holds for the result. The {deftech (key := "vcgen partial correctness interpretation")}_partial correctness interpretation_ {lean}`⦃P⦄ prog ⦃Q'; ⊤⦄` asserts that, given {lean}`P` holds, and _if_ {lean}`prog` terminates normally _then_ {lean}`Q'` holds for the result.
A triple without an explicit exception postcondition carries the bottom assertion {lean}`(⊥ : EPred)` and thus has the total interpretation; between `⊥` and `⊤`, the exception postcondition expresses a spectrum of correctness properties.
:::


## Predicate Transformers

```lean -show
universe u v w
variable {Pred : Type u} {EPred : Type v} {α : Type w} [Assertion Pred] [Assertion EPred]
```

A predicate transformer maps a postcondition and an exception postcondition to an assertion.
{lean}`PredTrans Pred EPred α` wraps a function of type {lean}`(α → Pred) → EPred → Pred` for a program with results of type {lean}`α`.

{docstring Lean.Order.PredTrans}

{docstring Lean.Order.PredTrans.apply}

{docstring Lean.Order.PredTrans.monotone}

:::leanSection
```lean -show
variable {x y : PredTrans Pred EPred α} {post : α → Pred} {epost : EPred}
```
The partial order on predicate transformers is inherited pointwise from the assertion lattice: {lean}`x ⊑ y` when {lean}`x.apply post epost ⊑ y.apply post epost` for all {lean}`post` and {lean}`epost`.
:::

Predicate transformers form a monad.
The {name Pure.pure}`pure` operator is the identity transformer; it simply instantiates the postcondition with its argument.
The {name Bind.bind}`bind` operator composes predicate transformers.

{docstring Lean.Order.instMonadPredTrans}

The helper operators {name}`Lean.Order.pushArg`, {name}`PredTrans.pushExcept`, and {name}`PredTrans.pushOption` modify a predicate transformer by adding a standard side effect.
They are used to implement the {name}`WP` instances for transformers such as {name}`StateT`, {name}`ExceptT`, and {name}`OptionT`; they can also be used to implement monads that can be thought of in terms of one of these.
For example, {name}`Lean.Order.pushArg` is typically used for state monads, but can also be used to implement a reader monad's instance, treating the reader's value as read-only state.

{docstring Lean.Order.pushArg}

{docstring PredTrans.pushExcept}

{docstring PredTrans.pushOption}

### Weakest Preconditions

```lean -show
variable {Prog : Type u} {Value : Type v} [WP Prog Value Pred EPred] {x : Prog} {post : Value → Pred} {epost : EPred}
```

The {tech}[weakest precondition] semantics of a program type are provided by the {name}`WP` type class.
An instance {lean}`WP Prog Value Pred EPred` interprets programs of type {lean}`Prog` with results of type {lean}`Value` as monotone predicate transformers over the assertion type {lean}`Pred` and the exception postcondition type {lean}`EPred`.
The function {name}`wp` applies the interpretation: {lean}`wp x post epost` is the weakest precondition under which the program {lean}`x` establishes the postcondition {lean}`post` and the exception postcondition {lean}`epost`.

{docstring WP}

{docstring WP.wp}

A program that is {deftech (key := "vcgen conjunctive")}_conjunctive_ distributes over the meet of two weakest preconditions.
The type class {name}`WPConjunctive` captures this property, which the specification lemmas for `if` and `match` splitting rely on.

{docstring WPConjunctive}

### Weakest Precondition Monad Morphisms

Most of the built-in specification lemmas for {tactic}`vcgen` rely on the presence of a {name}`WPMonad` instance.
A {name}`WPMonad` instance carries the {name}`WP` interpretation for every result type and asserts that this interpretation is sound for the monad's implementations of {name Pure.pure}`pure` and {name Bind.bind}`bind`.
Without a {name}`WPMonad` instance, {tactic}`vcgen` reports that no specification applies to the program.

{docstring WPMonad}

:::example "Missing `WPMonad` Instance"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option mvcgen.warning false

```

The single-field structure {name}`Identity` acts like the identity monad {name}`Id`:
```lean
structure Identity (α : Type u) where
  run : α

variable {α : Type u}

instance : Monad Identity where
  pure x := ⟨x⟩
  bind x f := f x.run

def rev (xs : List α) : Identity (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out
```
{name}`rev` is correct if it is equal to {name}`List.reverse`.

```lean -show
instance : LawfulMonad Identity :=
  LawfulMonad.mk' Identity
    (id_map := fun _ => rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)
```

The {name}`WP` interpretation of {name}`Identity` is a plain definition marked {attr}`instance_reducible`, following the pattern of the interpretations in {module}`Std.WP`:
```lean
@[instance_reducible] def Identity.wpInst :
    WP (Identity α) α Prop EPost.Nil where
  wpTrans x := ⟨fun post _ => post x.run⟩
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x.run
```
This interpretation alone suffices to state weakest preconditions and to prove an adequacy lemma, but not to run {tactic}`vcgen`:
```lean -show
section OnlyWP

attribute [local instance] Identity.wpInst

theorem Identity.of_run_eq_wp' {x : α} {prog : Identity α}
    (h : Identity.run prog = x) (P : α → Prop)
    (hwp : wp prog P EPost.Nil.mk) : P x := by
  simp_all [wp, WP.wpTrans, ← h]
```
The specifications for {name Pure.pure}`pure` and {name Bind.bind}`bind` require a {name}`WPMonad` instance for {name}`Identity`, so {tactic}`vcgen` reports that it cannot take the program apart:
```lean +error (name := noInst)
theorem rev_correct_bad {xs : List α} :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_run_eq_wp' h
  vcgen [rev]
```
```leanOutput noInst
No spec applicable to program (forIn xs [] fun x __s => pure (ForInStep.yield (x :: __s))) >>=
  pure in monad Identity. Candidates were [SpecProof.global Std.WP.Spec.bind].
```
```lean -show
end OnlyWP
```
The issue can be resolved by defining a {name}`WPMonad` instance whose {name}`WPMonad.toWP` field carries the interpretation:
```lean
instance Identity.instWPMonad : WPMonad Identity Prop EPost.Nil where
  toWP _ := Identity.wpInst
  pure_le_wp_pure x post epost := PartialOrder.rel_refl
  bind_le_wp_bind x f post epost := PartialOrder.rel_refl

theorem Identity.of_run_eq_wp {x : α} {prog : Identity α}
    (h : Identity.run prog = x) (P : α → Prop)
    (hwp : wp prog P EPost.Nil.mk) : P x := by
  simp_all [wp, WP.wpTrans, ← h]
```
With this instance, and a suitable invariant, {tactic}`vcgen` and `grind` can prove the theorem.
```lean
theorem rev_correct {xs : List α} :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_run_eq_wp h
  simp only [rev]
  vcgen invariants
  · fun pref suff out => out = pref.reverse
  with finish
```
:::

### Adequacy Lemmas
%%%
tag := "vcgen-adequacy"
%%%

Monads that can be invoked from pure code typically provide a invocation operator that takes any required input state as a parameter and returns either a value paired with an output state or some kind of exceptional value.
Examples include {name}`StateT.run`, {name}`ExceptT.run`, and {name}`Id.run`.
{deftech (key := "vcgen Adequacy lemmas")}_Adequacy lemmas_ provide a bridge between statements about invocations of monadic programs and those programs' {tech}[weakest precondition] semantics as given by their {name}`WP` instances.
They show that a property about the invocation is true if its weakest precondition is true.

{docstring Id.of_run_eq_wp}

{docstring StateM.of_run_eq_wp}

{docstring StateM.of_run'_eq_wp}

{docstring ReaderM.of_run_eq_wp}

{docstring Except.of_eq_wp}

{docstring Option.of_eq_wp}

{docstring EStateM.of_run_eq_wp}

## Hoare Triples

A {deftech (key := "vcgen Hoare triple")}_Hoare triple_{citep hoare69}[] consists of a precondition, a program, and a postcondition.
Running the program in a state for which the precondition is true results in a state where the postcondition is true.

{docstring Triple}

::::syntax term (title := "Hoare Triples")
```grammar
⦃ $_ ⦄ $_ ⦃ $_ ⦄
```
```grammar
⦃ $_ ⦄ $_ ⦃ $_; $_ ⦄
```
```grammar
⦃ $_ ⦄ $_ ⦃ $x, $_ ⦄
```
:::leanSection
```lean -show
universe z
variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z} [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred] {x : Prog} {P : Pred} {Q : Value → Pred} {E : EPred}
```
{lean}`⦃ P ⦄ x ⦃ Q; E ⦄` is syntactic sugar for {lean}`Triple x P Q E`.
When the exception postcondition is omitted, as in {lean}`⦃ P ⦄ x ⦃ Q ⦄`, it defaults to the bottom assertion `⊥`, asserting that the program throws no exception.
The binder form `⦃ P ⦄ x ⦃ r, Q ⦄` binds the result value `r` in the postcondition `Q`.
:::
::::

{docstring Triple.and}

{docstring Triple.mp}

## Specification Lemmas

{deftech (key := "vcgen Specification lemmas")}_Specification lemmas_ are designated theorems that associate Hoare triples with functions.
When {tactic}`vcgen` encounters a function, it checks whether there are any registered specification lemmas and attempts to use them to discharge intermediate {tech}[verification conditions].
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
These variables are referred to as {deftech (key := "vcgen schematic variables")}_schematic variables_.

:::example "Schematic Variables"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

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
theorem double_spec {n : Nat} :
    ⦃ fun s => s = n ⦄ double ⦃ fun _ s => s = 2 * n ⦄ := by
  simp [double]
  vcgen with finish
```

The assertion in the precondition is a function because the assertion type of {lean}`StateM Nat` is {lean}`Nat → Prop`.

:::
```lean -show -keep
-- Test preceding examples' claims
#synth WP (StateM Nat Unit) Unit (Nat → Prop) EPost.Nil
```

## Invariant Specifications

These types are used in invariants.
The {tech}[specification lemmas] for {name}`ForIn.forIn` and {name}`ForIn'.forIn'` take parameters of type {name}`Invariant`, and {tactic}`vcgen` ensures that invariants are not accidentally generated by other automation.

{docstring Invariant}

Invariants use lists to model the sequence of values in a {keywordOf Lean.Parser.Term.doFor}`for` loop.
An invariant is a function of the list of elements that the loop has already consumed, the list of elements that remain, and the current accumulator state.

{docstring Invariant.withEarlyReturnNewDo}

{docstring RepeatInvariant.ofInvariantAndBreak}


# Verification Conditions

The {tactic}`vcgen` tactic converts a goal that's expressed in terms of weakest preconditions to a set of invariants and verification conditions that, together, suffice to prove the original goal.
In particular, {tech}[Hoare triples] are defined in terms of weakest preconditions, so {tactic}`vcgen` can be used to prove them.

:::leanSection
```lean -show
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type u} {e : m α} {P : Pred} {Q : α → Pred} {E : EPred}
```
The verification conditions for a goal are generated as follows:
1. A number of simplifications and rewrites are applied, and the goal context is internalized into `grind`'s E-graph.
2. The goal should now be of the form {lean}`P ⊑ wp e Q E` (that is, an entailment from some assertion to the weakest precondition that implies a desired postcondition).
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
6. Each remaining goal created by this process is recursively processed for verification conditions if it has the form {lean}`P ⊑ wp e Q E`. If not, it is added to the set of invariants or verification conditions.
7. The resulting subgoals for invariants and verification conditions are assigned the names `vc1`, `vc2`, … in the order in which they arise.
8. An `until` clause stops VC generation at the first program that matches the given pattern.
   A `with` clause runs the given `grind`-mode step on every remaining verification condition inside the internalized context.
:::

Verification condition generation can be improved by defining appropriate {tech}[specification lemmas] for a library.
The presence of good specification lemmas results in fewer generated verification conditions.
Additionally, ensuring that the {tech}[simp normal form] of terms is suitable for pattern matching, and that there are sufficient lemmas in the default simp set to reduce every possible term to that normal form, can lead to more conditionals and pattern matches being eliminated.

# Enabling `vcgen` For Monads

If a monad is implemented in terms of {tech}[monad transformers] that are provided by the Lean standard library, such as {name}`ExceptT` and {name}`StateT`, then it should not require additional instances.
Other monads will require instances of {name}`LawfulMonad` and {name}`WPMonad`.
The tactic has been designed to support monads that model single-threaded control with state that might be interrupted; in other words, the effects that are present in ordinary imperative programming.
More exotic effects have not yet been investigated.

Once the basic instances are provided, the next step is to prove an {ref "vcgen-adequacy"}[adequacy lemma].
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
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

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
theorem double_spec {n : Nat} :
    ⦃ fun s => s = n ⦄ double ⦃ fun _ s => s = 2 * n ⦄ := by
  simp [double]
  vcgen with finish
```
However, an equivalent specification that treats the postcondition schematically will lead to smaller verification conditions when {name}`double` is used in other functions:
```lean
@[spec]
theorem better_double_spec {Q : Unit → Nat → Prop} :
    ⦃ fun s => Q () (2 * s) ⦄ double ⦃ Q ⦄ := by
  simp [double]
  vcgen with finish
```
Now, the precondition merely states that the postcondition should hold for double the initial state.
:::

:::example "A Logging Monad"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

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
    simp [pure, bind, Functor.map]
  bind_map f x := by
    simp [bind, Seq.seq, Functor.map]
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

Rather than writing it from scratch, the {name}`WP` interpretation inside the {name}`WPMonad` instance uses {name}`Lean.Order.pushArg`.
This operator was designed to model state monads, but {name}`LogM` can be seen as a state monad that can only append to the state.
This appending is visible in the body of the instance, where the initial state and the log that resulted from the action are appended:
```lean
instance : WPMonad (LogM β) (Array β → Prop) EPost.Nil where
  toWP α := {
    wpTrans x := pushArg fun s => pure (x.value, s ++ x.log)
    wp_trans_monotone x := fun _ _ _ _ _ hpost s =>
      hpost x.value (s ++ x.log)
  }
  pure_le_wp_pure x post epost := by
    simp [wp, WP.wpTrans, pure, PartialOrder.rel]
  bind_le_wp_bind x f post epost := by
    simp [wp, WP.wpTrans, bind, PartialOrder.rel, pushArg]
```

The adequacy lemma has one important detail: the weakest precondition is applied to the empty array.
This is necessary because the logging computation has been modeled as an append-only state, so there must be some initial state.
Semantically, the empty array is the correct choice so as to not place items in a log that don't come from the program; technically, it must also be a value that commutes with the append operator on arrays.
```lean
theorem LogM.of_run_eq_wp {α : Type u} {β : Type v}
    {x : α × Array β} {prog : LogM β α}
    (h : LogM.run prog = x) (P : α × Array β → Prop)
    (hwp : wp prog (fun v l => P (v, l)) EPost.Nil.mk #[]) : P x := by
  rw [← h]
  simp [wp, WP.wpTrans, pushArg, LogM.run] at hwp ⊢
  exact hwp
```

Next, each operator in the library should be provided with a specification lemma.
There is only one: {name}`log`.
For new monads, these proofs must often break the abstraction boundaries of {tech}[Hoare triples] and weakest preconditions; the specifications that they provide can then be used abstractly by clients of the library.
```lean
theorem log_spec {x : β} {s' : Array β} :
    ⦃ fun s => s = s' ⦄ log x ⦃ fun _ s => s = s'.push x ⦄ := by
  constructor
  simp [log, wp, WP.wpTrans, pushArg, PartialOrder.rel]
```

A better specification for {name}`log` uses a schematic postcondition:
```lean
@[spec]
theorem log_spec_better {x : β} {Q : Unit → Array β → Prop} :
    ⦃ fun s => Q () (s.push x) ⦄ log x ⦃ Q ⦄ := by
  constructor
  simp [log, wp, WP.wpTrans, pushArg, PartialOrder.rel]
```

A function {name}`logUntil` that logs all the natural numbers up to some bound will always result in a log whose length is equal to its argument:
```lean
def logUntil (n : Nat) : LogM Nat Unit := do
  for i in 0...n do
    log i

theorem logUntil_length {n : Nat} : (logUntil n).run.2.size = n := by
  generalize h : (logUntil n).run = x
  unfold logUntil at h
  apply LogM.of_run_eq_wp h
  vcgen invariants
  · fun pref suff _ s => pref.length = s.size
  all_goals simp_all [Std.Internal.ForIn.toList_rco]
  all_goals grind
```
:::

# Discharging Verification Conditions
%%%
tag := "vcgen-proof-mode"
%%%

The verification conditions that {tactic}`vcgen` produces are ordinary Lean goals, so any tactic can discharge them.
The `with` clause runs a single `grind`-mode step, typically `finish`, on every remaining verification condition.
The step runs inside the goal context that {tactic}`vcgen` internalized into `grind`'s E-graph during generation, so the context is not re-internalized for every verification condition.

When working with concrete monads, the verification conditions speak directly about result values and states.
Monad-polymorphic theorems instead lead to goals over an abstract assertion lattice; `grind`'s lattice reasoning discharges these as well.

:::example "Monad-Polymorphic Proofs"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option mvcgen.warning false

```
The function {name}`bump` increments its state by the indicated amount and returns the resulting value.
The underlying monad {lean}`m` and its assertion types stay abstract.
```lean
variable {m : Type → Type v} [Monad m]
variable {Pred EPred : Type}
variable [Assertion Pred] [Assertion EPred]
variable [WPMonad m Pred EPred]

def bump (n : Nat) : StateT Nat m Nat := do
  modifyThe Nat (· + n)
  getThe Nat
```

The specification lemma quantifies over the abstract assertion lattice, and its verification conditions are entailments in that lattice.
The `finish` step discharges them:
```lean
theorem bump_correct {k i : Nat} :
    ⦃ fun n => ⌜n = k⌝ ⦄
    bump (m := m) i
    ⦃ fun r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  vcgen [bump] with finish
```
:::
