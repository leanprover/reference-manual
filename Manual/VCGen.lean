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

set_option experimental.vcgen true

open Manual (comment)

open Std.WP Lean.Order

#doc (Manual) "The `vcgen` tactic" =>
%%%
tag := "vcgen-tactic"
%%%

:::tutorials
 * {ref "vcgen-tactic-tutorial" (remote := "tutorials")}[Verifying Imperative Programs Using `vcgen`]
:::

The {tactic}`vcgen` tactic implements a _verification condition generator_:
It breaks down a goal involving a program, for example one written using Lean's imperative {keywordOf Lean.Parser.Term.do}`do` notation, into a number of smaller {tech}_verification conditions_ ({deftech}[VCs]) that are sufficient to prove the goal.
In addition to a reference that describes the use of {tactic}`vcgen`, this chapter includes a {ref "vcgen-tactic-tutorial" (remote := "tutorials")}[tutorial] that can be read independently of the reference.

In order to use the {tactic}`vcgen` tactic, {module}`Std.WP` and {module}`Std.Tactic.Do` must be imported and the namespaces {namespace}`Std.WP` and {namespace}`Lean.Order` must be opened.
The dependency on {namespace}`Lean.Order` is a temporary measure: this namespace holds the {ref "partial-fixpoint-theory"}[order theory behind `partial_fixpoint`], which is yet to move into `Std`.


# Overview



The workflow of {tactic}`vcgen` consists of the following:

1. Programs are re-interpreted according to a {tech}[predicate transformer semantics].
   An instance of {name}`WP` for the program type determines the interpretation.
   The program type can be a monadic computation, such as a {keywordOf Lean.Parser.Term.do}`do`-block in {lean}`StateM Nat`, or any other type, for example the syntax trees of a small imperative language.
   Each program is interpreted as a mapping from arbitrary {tech}[postconditions] to the {tech}[weakest precondition] that would ensure the postcondition.
   This step is invisible to most users, but library authors who want to enable their program types to work with {tactic}`vcgen` need to understand it.
2. Programs are composed from smaller programs.
   Each part of a program, such as a statement in a {keywordOf Lean.Parser.Term.do}`do`-block, is associated with a predicate transformer, and there are general-purpose rules for combining these parts with sequencing and control-flow operators.
   A statement with its pre- and postconditions is called a {tech}_Hoare triple_.
   In a program, the postcondition of each statement should suffice to prove the precondition of the next one, and loops require a specified {deftech}_loop invariant_, which is a statement that must be true at the beginning of the loop and at the end of each iteration.
   Designated {tech}_specification lemmas_ associate functions with Hoare triples that specify them.
3. Applying the weakest-precondition semantics of a program to a desired proof goal results in the precondition that must hold in order to prove the goal.
   The remaining entailments between assertions, such as a proof that the postcondition of one statement implies the precondition of the next, contain no weakest preconditions and become new subgoals.
   These subgoals are called the {deftech}_verification conditions_.
   Loop invariants that the user supplies become separate subgoals.
   The {tactic}`vcgen` tactic performs this transformation, replacing the goal with its verification conditions.
   During this transformation, {tactic}`vcgen` uses specification lemmas to discharge proofs about individual statements.
4. After supplying loop invariants, many verification conditions can in practice be discharged automatically.
   Those that cannot are ordinary Lean goals, provable with ordinary Lean tactics or with the `grind`-mode step of the `with` clause.


# Predicate Transformers

A {deftech}_predicate transformer semantics_ is an interpretation of programs as functions from predicates to predicates, rather than values to values.
A {deftech}_postcondition_ is an assertion that holds after running a program, while a {deftech}_precondition_ is an assertion that must hold prior to running the program in order for the postcondition to be guaranteed to hold.

The predicate transformer semantics used by {tactic}`vcgen` transforms postconditions into the {deftech}_weakest preconditions_ under which the program will ensure the postcondition.
An assertion $`P` is weaker than $`P'` if, in all states, $`P'` suffices to prove $`P`, but $`P` does not suffice to prove $`P'`.
Logically equivalent assertions are considered to be equal.

The predicates in question can be stateful: they can mention the program's current state.
Furthermore, postconditions can relate the return value and any exceptions thrown by the program to the final state.
Each program type that can be used with {tactic}`vcgen` is assigned an assertion type and an exception postcondition type by an instance of {name}`WP`.
For a state monad such as {lean}`StateM Nat`, an assertion is a predicate on the state, of type {lean}`Nat → Prop`.
A postcondition additionally takes the return value as its first argument, and the exception postcondition covers each exception that the program can throw.


## Assertion Lattices

The predicate transformer semantics of programs is based on a logic in which propositions may mention the program's state.
Here, “state” refers not only to mutable state, but also to read-only values such as those that are provided via {name}`ReaderT`.
Different program types have different assertion types, which can be any complete lattice.
More specifically, assertion types instantiate {name}`Assertion`, which is a `class abbrev` over {name}`CompleteLattice` that is recognized by `vcgen`.

{docstring Assertion}

The lattice structure provides the logical vocabulary of assertions:

* The order relation {name Lean.Order.PartialOrder.rel}`⊑` is entailment.
* The meet {name Lean.Order.meet}`⊓` is conjunction and the join {name Lean.Order.join}`⊔` is disjunction.
* The top element {name Lean.Order.top}`⊤` is the trivial assertion and the bottom element {name Lean.Order.bot}`⊥` is the absurd assertion.
* The indexed supremum {name Lean.Order.iSup}`⨆` is existential quantification and the indexed infimum {name Lean.Order.iInf}`⨅` is universal quantification.
* The Heyting implication {name Lean.Order.himp}`⇨` is implication internal to the assertion language.

The difference between entailment and implication is that entailment is a statement in Lean's logic, while implication is internal to the assertion language: for assertions `P` and `Q`, `P ⊑ Q` is a {lean}`Prop` while `P ⇨ Q` is again an assertion.

{module}`Std.WP` comes with {name}`Assertion` instances for {lean}`Prop`, {lean}`Unit`, function types, and pairs.
The lattice operations on {lean}`Prop` coincide with the ordinary logical connectives, with entailment being implication.
The lattice operations on a function type such as {lean}`Nat → Prop` operate pointwise, so entailment of state predicates is universally-quantified implication.
The lattice operations on a pair such as {lean}`(Nat → Prop) × (Bool → Prop)` operate componentwise, so entailment of pair predicates is the pair of entailments on the component predicates.

::::leanSection
```lean -show
universe u
variable {P : Prop} {Pred : Type u} [Assertion Pred]
```
Ordinary propositions that do not mention the state can be embedded into any assertion lattice with corner brackets.
This is written with the syntax {lean (type := "Pred")}`⌜P⌝`, which is notation for {name}`Lean.Order.CompleteLattice.ofProp`.
The popular Iris proof mode uses the same syntax and meaning.
:::syntax term (title := "Embedding Propositions") (namespace := Lean.Order)
```grammar
⌜$_:term⌝
```
{includeDocstring Lean.Order.CompleteLattice.ofProp}
:::
::::

{docstring Lean.Order.CompleteLattice.ofProp}

An assertion of the form `⌜p⌝` is {deftech (key := "pure assertion")}_pure_: it holds or fails independently of the state.
At the assertion type {lean}`Prop`, `⌜p⌝` is the proposition `p` itself, and at a state predicate type such as {lean}`Nat → Prop`, it is the constant predicate `fun _ => p`.
Specifications for a concrete monad can therefore state propositions directly, as in `fun s => s = n`.
Corner brackets are necessary when the assertion type is abstract, as in a specification that quantifies over the monad and its assertion type `Pred`: there, a proposition such as `n = k` is no assertion, and `⌜n = k⌝` embeds it into `Pred`.
The `bump` example at the end of this chapter uses corner brackets for this reason.
{tactic}`vcgen` moves pure preconditions into the ordinary Lean context, where they become hypotheses of the verification conditions.

:::example "Assertions for State Monads"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```
The predicate {name}`ItIsSecret` expresses that a state of type {name}`String` is {lean}`"secret"`:
```lean
def ItIsSecret : String → Prop := fun s => s = "secret"
```
Entailment between such assertions is pointwise implication:
```lean
example : ItIsSecret ⊑ (⌜True⌝ : String → Prop) := by
  simp [ItIsSecret, PartialOrder.rel]
```
:::

## Exception Postconditions

A postcondition for successful termination is a function from the return value to an assertion.
Programs that can throw exceptions additionally require an {deftech}_exception postcondition_, asserting what holds when the program throws an exception.
The exception postcondition type of a given monad is determined by its {name}`WP` instance.

For example, the {name}`WP` instance for {lean}`EStateM String Nat Bool` determines {lean}`Nat → Prop` as the assertion type, hence {lean}`Bool → Nat → Prop` as the postcondition type, and {lean}`String → Nat → Prop` as the exception postcondition type.
A monad without exceptions uses {name}`Unit`.
For a base monad with assertion type `Pred` and exception postcondition type `EPred`, an exception layer such as `ExceptT ε` contributes one more exception postcondition, which gives the type `(ε → Pred) × EPred`.
Since unit and pair types come with {name}`Assertion` instances, such exception postcondition stacks are automatically assertions as well.

The {name}`WP` instances of monad transformer stacks produce exception postcondition stacks.
The notation `EStack⟨e₁, e₂, ...⟩` abbreviates the type of exception postcondition stack `e₁ × (e₂ × (... × Unit))`, and the notation `estack⟨v₁, v₂, ...⟩` builds a value `(v₁, v₂, ..., ())` of such a stack.

:::syntax term (title := "Exception Postcondition Stacks") (namespace := Std.WP)
```grammar
EStack⟨$_,*⟩
```
```grammar
estack⟨$_,*⟩
```
:::

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {P : Pred} {α : Type u} {prog : m α} {Q' : α → Pred}
```
Specifications for programs that might throw exceptions come in two varieties. The {deftech}_total correctness interpretation_ {lean}`⦃P⦄ prog ⦃Q'⦄` asserts that, given {lean}`P` holds, then {lean}`prog` terminates normally _and_ {lean}`Q'` holds for the result. The {deftech}_partial correctness interpretation_ {lean}`⦃P⦄ prog ⦃Q'; ⊤⦄` asserts that, given {lean}`P` holds, and _if_ {lean}`prog` terminates normally _then_ {lean}`Q'` holds for the result.
A triple without an explicit exception postcondition carries the bottom assertion {lean}`(⊥ : EPred)` and thus has the total interpretation; between `⊥` and `⊤`, the exception postcondition expresses a spectrum of correctness properties.
:::

## Predicate Transformers

```lean -show
universe u v w
variable {Pred : Type u} {EPred : Type v} {α : Type w} [Assertion Pred] [Assertion EPred]
```

A predicate transformer is a function from postconditions into assertions that describe preconditions.

{docstring Lean.Order.PredTrans}

:::leanSection
```lean -show
variable {x y : PredTrans Pred EPred α} {post : α → Pred} {epost : EPred}
```
The partial order on predicate transformers is inherited pointwise from the assertion lattice: {lean}`x ⊑ y` when {lean}`x.apply post epost ⊑ y.apply post epost` for all {lean}`post` and {lean}`epost`.
Every predicate transformer that a {name}`WP` instance produces is {deftech}_monotone_: if `post ⊑ post'` and `epost ⊑ epost'`, then `x.apply post epost ⊑ x.apply post' epost'`.

{docstring Lean.Order.PredTrans.monotone}
:::

Predicate transformers form a monad.
The {name}`pure` operator is the identity transformer; it simply instantiates the postcondition with its argument.
The {name}`bind` operator composes predicate transformers.

{docstring PredTrans.pure}

{docstring PredTrans.bind}

The helper operators {name}`PredTrans.pushArg`, {name}`PredTrans.pushExceptT`, and {name}`PredTrans.pushOptionT` modify a predicate transformer by adding a standard side effect.
They are used to implement the {name}`WP` instances for transformers such as {name}`StateT`, {name}`ExceptT`, and {name}`OptionT`; they can also be used to implement monads that can be thought of in terms of one of these.
For example, {name}`PredTrans.pushArg` is typically used for state monads, but can also be used to implement a reader monad's instance, treating the reader's value as read-only state.

{docstring PredTrans.pushArg}

{docstring PredTrans.pushExceptT}

{docstring PredTrans.pushOptionT}

### Weakest Preconditions

```lean -show
variable {Prog : Type u} {Value : Type v} [WP Prog Value Pred EPred] {x : Prog} {post : Value → Pred} {epost : EPred}
```

The {tech}[weakest precondition] semantics of a program type is provided by the {name}`WP` type class.
An instance {lean}`WP Prog Value Pred EPred` interprets programs of type {lean}`Prog` with results of type {lean}`Value` as monotone predicate transformers over the assertion type {lean}`Pred` and the exception postcondition type {lean}`EPred`.
The type {lean}`Prog` determines {lean}`Value`, {lean}`Pred` and {lean}`EPred` as {name}`outParam`s.
The function {name}`wp` applies the interpretation: {lean}`wp x post epost` is the weakest precondition under which the program {lean}`x` establishes the postcondition {lean}`post` and the exception postcondition {lean}`epost`.

{docstring WP}

{docstring WP.wp}

A program `x` that is {deftech}_conjunctive_ distributes a weakest precondition of a meet of two postconditions into a meet of the weakest preconditions of the postconditions.
The type class {name}`WPConjunctive` captures this property, which allows for combining two specifications for `x` into a single strongest one, as {name}`Triple.and` does.

{docstring WPConjunctive}

### Monads Preserving Weakest Preconditions

Most of the built-in specification lemmas for {tactic}`vcgen` rely on the presence of a {name}`WPMonad` instance.
A {name}`WPMonad` instance carries the {name}`WP` interpretation for every result type and asserts that this interpretation is sound for the monad's implementations of {name Pure.pure}`pure` and {name Bind.bind}`bind`.
This means that to prove something about a do block, it suffices to prove it about the chain of elements of the do block.
This unlocks compositional reasoning about do blocks.

{docstring WPMonad}

:::example "Missing `WPMonad` Instance"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```

The single-field structure {name}`Identity` acts like the identity monad {name}`Id`. It has a {name}`WP` instance, but no {name}`WPMonad` instance:
```lean
structure Identity (α : Type u) where
  run : α

variable {α : Type u}

instance : Monad Identity where
  pure x := ⟨x⟩
  bind x f := f x.run

instance : WP (Identity α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun post _ => post x.run⟩
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x.run

theorem Identity.of_run_eq_wp {x : α} {prog : Identity α}
    (h : Identity.run prog = x) (P : α → Prop)
    (hwp : wp prog P ()) : P x := by
  simp_all [wp, WP.wpTrans, ← h]
```

```lean -show
instance : LawfulMonad Identity :=
  LawfulMonad.mk' Identity
    (id_map := fun _ => rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)
```

The missing instance prevents {tactic}`vcgen` from using its specifications for {name}`pure` and {name}`bind`.
For example, the following function reverses a list with a `for` loop in {name}`Identity`:
```lean
def rev (xs : List α) : Identity (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out
```
The theorem `rev_correct` states that {name}`rev` agrees with {name}`List.reverse`.
Without a {name}`WPMonad` instance, {tactic}`vcgen` cannot take {name}`rev` apart and reports that no specification applies to the program:
```lean +error -keep (name := noInst)
theorem rev_correct {xs : List α} :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_run_eq_wp h
  vcgen [rev]
```
```leanOutput noInst
No spec applicable to program (forIn xs [] fun x __s => pure (ForInStep.yield (x :: __s))) >>=
  pure in monad Identity. Candidates were [SpecProof.global Std.WP.Spec.bind].
```
When no specification applies to {name}`bind`, the problem is usually a missing {name}`WPMonad` instance.
The issue can be resolved by adding a suitable instance:
```lean
instance : WPMonad Identity Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind _ _ _ _ := PartialOrder.rel_refl
```
With this instance, and a suitable invariant, {tactic}`vcgen` and the {tactic}`grind`-mode tactic `finish` can prove the theorem.
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

### Soundness Lemmas
%%%
tag := "vcgen-soundness"
%%%

Monads that can be invoked from pure code typically provide an invocation operator that takes any required input state as a parameter and returns either a value paired with an output state or some kind of exceptional value.
Examples include {name}`StateT.run`, {name}`ExceptT.run`, and {name}`Id.run`.
{deftech}_Soundness lemmas_ provide a bridge between statements about invocations of monadic programs and those programs' {tech}[weakest precondition] semantics as given by their {name}`WP` instances.
They show that a property about the invocation is true if its weakest precondition is true.

{docstring Id.of_run_eq_wp}

{docstring StateM.of_run_eq_wp}

{docstring StateM.of_run'_eq_wp}

{docstring ReaderM.of_run_eq_wp}

{docstring Except.of_eq_wp}

{docstring Option.of_eq_wp}

{docstring EStateM.of_run_eq_wp}

## Hoare Triples

A {deftech}_Hoare triple_{citep hoare69}[] consists of a precondition, a program, and a postcondition.
Running the program in a state for which the precondition is true results in a state where the postcondition is true.

{docstring Triple}

::::syntax term (title := "Hoare Triples")
```grammar
⦃ $_ ⦄ $_ ⦃ $_ ⦄
```
```grammar
⦃ $_ ⦄ $_ ⦃ $_; $_ ⦄
```
:::leanSection
```lean -show
universe z
variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z} [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred] {x : Prog} {P : Pred} {Q : Value → Pred} {E : EPred}
```
{lean}`⦃ P ⦄ x ⦃ Q; E ⦄` is syntactic sugar for {lean}`Triple x P Q E`.
When the exception postcondition is omitted, as in {lean}`⦃ P ⦄ x ⦃ Q ⦄`, it defaults to the bottom assertion `⊥`, asserting that the program throws no exception.
:::
::::

{docstring Triple.and}

{docstring Triple.mp}

## Specification Lemmas

{deftech}_Specification lemmas_ are designated theorems that associate a Hoare triple with a program construct, such as {name Bind.bind}`bind`, {name Pure.pure}`pure`, a loop, or a call of a library function.
The {tactic}`vcgen` tactic decomposes a goal `P ⊑ wp prog Q E` by applying a specification lemma whose program matches `prog`, as the section on {ref "vcgen-verification-conditions"}[verification conditions] describes.
If no specification lemma applies to `prog`, then {tactic}`vcgen` reports an error that names `prog` and the candidate lemmas.
Specification lemmas make reasoning about programs _modular_: the specification lemma of a function `f` is proved once, and {tactic}`vcgen` applies it at every call of `f` without unfolding the definition of `f`.
In this respect, {name Pure.pure}`pure` and {name Bind.bind}`bind` are ordinary functions: the specification lemmas {name}`Spec.pure` and {name}`Spec.bind` hold in every monad with a {name}`WPMonad` instance.

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

A {deftech}_logical variable_ is a universally quantified variable of a specification lemma that the program does not mention and that relates the initial state to the final state and the return value.

:::example "Logical Variables"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```

The function {name}`double` doubles the value of a {name}`Nat` state:
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
Its specification should _relate_ the initial and final states, but it cannot know their precise values.
The specification uses a logical variable to stand for the initial state:
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
#synth WP (StateM Nat Unit) Unit (Nat → Prop) EStack⟨⟩
```

## Invariant Specifications

The {tech}[specification lemmas] for {name}`ForIn.forIn` and {name}`ForIn'.forIn'` take parameters of type {name}`Invariant`, and {tactic}`vcgen` ensures that invariants are not accidentally generated by other automation.

{docstring Invariant}

Invariants use lists to model the sequence of values in a {keywordOf Lean.Parser.Term.doFor}`for` loop.
An invariant is a function of the prefix of elements that the loop has already consumed, the suffix of elements that remain, the current accumulator state, and any further state arguments of the monad's assertion language.

{docstring Invariant.withEarlyReturnNewDo}

# Verification Conditions
%%%
tag := "vcgen-verification-conditions"
%%%

The {tactic}`vcgen` tactic converts a goal that's expressed in terms of weakest preconditions to a set of invariants and verification conditions that, together, suffice to prove the original goal.
In particular, {tech}[Hoare triples] are defined in terms of weakest preconditions, so {tactic}`vcgen` can be used to prove them.

:::leanSection
```lean -show
variable {m : Type u → Type v} [Monad m] {Pred EPred : Type u} [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] {α : Type u} {e : m α} {P : Pred} {Q : α → Pred} {E : EPred}
```
{TODO}[This model does not cover frames: the `frames` clause and frameprocs.]
The verification conditions for a goal are generated as follows:
1. The goal is brought into the form of an entailment `P ⊑ R` between assertions.
   Binders are introduced, a {tech}[Hoare triple] is unfolded to {lean}`P ⊑ wp e Q E`, and a goal `wp e Q E` becomes `⊤ ⊑ wp e Q E`.
2. The precondition `P` moves into the local context: a pure assertion `⌜φ⌝` becomes a hypothesis `φ`, an existential `⨆` becomes a variable, and the arguments of a state predicate become variables.
3. The assertion `R` is decomposed along its connectives: `⊓` gives one goal per conjunct, `⇨` moves its antecedent into the precondition, `⌜φ⌝` gives the proposition `φ`, and `⊤` closes the goal.
4. If `R` is {lean}`wp e Q E`, then the program {lean}`e` is decomposed:
   1. A `let` is introduced.
      An application of an {tech}[auxiliary matching function] whose {tech (key := "match discriminant")}[discriminant] is a constructor application is reduced; any other conditional or match is split into one goal per branch.
   2. An application of a function is handled by the first applicable specification lemma in priority order.
      Hypotheses that are Hoare triples also count as specification lemmas.
      Lean includes specification lemmas for {name Bind.bind}`bind`, {name Pure.pure}`pure`, {name}`ForIn.forIn` and the other functions that result from desugaring {keywordOf Lean.Parser.Term.do}`do`-notation.
      If no specification lemma applies, then {tactic}`vcgen` reports an error.
   3. A specification lemma `P' ⊑ wp e' Q' E'` is applied by transitivity of `⊑`: the goal {lean}`P ⊑ wp e Q E` follows from `P ⊑ P'` and `wp e' Q' E' ⊑ wp e Q E`.
      The second entailment holds when `e'` unifies with {lean}`e`, `Q' ⊑ Q` and `E' ⊑ E`.
      In effect, {tactic}`vcgen` replaces the weakest precondition in the goal by the precondition of the lemma, which gives the new goal `P ⊑ P'`.
   4. Unification instantiates the variables of the lemma that occur in its program.
      The universally quantified postcondition of an {tech}[auto-framing specification] becomes {lean}`Q`, so `Q' ⊑ Q` holds by reflexivity and no goal for the postcondition remains.
      Otherwise, the entailments `Q' ⊑ Q` and `E' ⊑ E` become new goals.
      Assumptions of a type registered with {attr}`spec_invariant_type` become invariant goals.
      The logical variables of the lemma appear as metavariables in all of these new goals.
5. Each new goal is processed again from step 1.
   For example, the specification lemma {name}`Spec.bind` is auto-framing and has the precondition `wp x (fun a => wp (f a) Q E) E`.
   For a goal `P ⊑ wp (x >>= f) Q E`, the new goal is `P ⊑ wp x (fun a => wp (f a) Q E) E`.
   When a specification lemma for `x` applies to this goal, the entailment between the postconditions has `wp (f a) Q E` on the right, so the rest of the program is decomposed in the same way.
   Before a new goal is processed, its hypotheses are internalized into `grind`'s E-graph, and a goal whose hypotheses are contradictory is dropped.
6. A goal that no step decomposes further is a verification condition.
   Before it is emitted, {tactic}`vcgen` solves its conjuncts of the form `True` or `e₁ = e₂` by definitional equality.
   Solving an equality can assign a metavariable, so some logical variables become assigned: a conjunct `s = ?n` assigns `?n := s`.
   The unsolved conjuncts remain as the verification condition.
7. The resulting subgoals receive the names `inv1`, `inv2`, … for invariants and `vc1`, `vc2`, … for verification conditions, in the order of generation.

VC generation stops early after `stepLimit` program steps.
An `until` clause stops VC generation at the first program that matches the given pattern.
A `with` clause runs the given `grind`-mode step on every remaining verification condition.
A clause `simplifying_assumptions [h₁, h₂]` rewrites the hypotheses that binders and branches introduce, and the state arguments of each weakest precondition, with `h₁` and `h₂` as additional rewrite rules.
This keeps the intermediate goals in a normal form that the user chooses: for example, a sequence of state updates can fold into one constructor application, so that the goals do not grow with the number of updates.
Simplified hypotheses also help `grind` to detect contradictory goals.
:::

# Enabling `vcgen` For Monads

If a monad is implemented in terms of {tech}[monad transformers] that are provided by the Lean standard library, such as {name}`ExceptT` and {name}`StateT`, then it should not require additional instances to work with {tactic}`vcgen`.
Other monads will require instances of {name}`WP`, {name}`LawfulMonad`, and {name}`WPMonad`.

Once the basic instances are provided, the next step is to prove a {ref "vcgen-soundness"}[soundness lemma].
This lemma should show that the weakest precondition for running the monadic computation and asserting a desired predicate is in fact sufficient to prove the predicate.

In addition to the definition of the monad, typical libraries provide a set of primitive operators.
Each of these should be provided with a {tech}[specification lemma].
It may additionally be useful to make the internals of the state private, and export a carefully-designed set of assertion operators.

The specification lemmas for the library's primitive operators should preserve every fact about the state that they do not deliberately hide.
While it's often easier to think in terms of how the operator transforms an input state into an output state, {tech}[verification condition] generation works more reliably when the postcondition is universally quantified, so that automation can instantiate it with the precondition of the next statement instead of proving an entailment.

:::example "Auto-Framing Specifications"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```

The function {name}`double` doubles a natural number state:
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
Thinking chronologically, a reasonable specification is that the value of the output state is twice that of the input state.
This is expressed using a logical variable that stands for the initial state:
```lean -keep
theorem double_spec {n : Nat} :
    ⦃ fun s => s = n ⦄ double ⦃ fun _ s => s = 2 * n ⦄ := by
  simp [double]
  vcgen with finish
```
However, an equivalent {deftech}_auto-framing specification_ leads to smaller verification conditions when {name}`double` is used in other functions:
```lean
@[spec]
theorem better_double_spec {Q : Unit → Nat → Prop} :
    ⦃ fun s => Q () (2 * s) ⦄ double ⦃ Q ⦄ := by
  simp [double]
  vcgen with finish
```
Now, the precondition merely states that the postcondition should hold for double the initial state.
Any property that `Q` states about state that {name}`double` does not change, such as a second state layer in a monad stack, holds after the call.
At a call of {name}`double`, {tactic}`vcgen` instantiates `Q` with the postcondition that the rest of the program requires, so no entailment between postconditions remains as a verification condition.

The precondition of {name}`better_double_spec` is exactly the weakest precondition of {name}`double`, so callers depend on the complete behavior of {name}`double`.
An auto-framing specification can also leave details open.
For example, the precondition `fun s => ∀ s', s ≤ s' → Q () s'` only promises that {name}`double` does not decrease the state.
:::

:::example "A Logging Monad"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

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

Rather than writing it from scratch, the {name}`WP` instance uses {name}`PredTrans.pushArg`.
This operator was designed to model state monads, but {name}`LogM` can be seen as a state monad that can only append to the state.
This appending is visible in the body of the instance, where the initial state and the log that resulted from the action are appended:
```lean
instance : WP (LogM β α) α (Array β → Prop) EStack⟨⟩ where
  wpTrans
    | { log, value } =>
      PredTrans.pushArg (fun s => pure (value, s ++ log))
  wp_trans_monotone x := fun _ _ _ _ _ hpost s =>
    hpost x.value (s ++ x.log)
```

The {name}`WPMonad` instance also benefits from the conceptual model as a state monad and admits very short proofs:
```lean
instance : WPMonad (LogM β) (Array β → Prop) EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure x post epost := by simp [wp, WP.wpTrans, pure]
  bind_le_wp_bind x f post epost := by simp [wp, WP.wpTrans, bind]
```

The soundness lemma has one important detail: the weakest precondition is applied to the empty array.
This is necessary because the logging computation has been modeled as an append-only state, so there must be some initial state.
Semantically, the empty array is the correct choice so as to not place items in a log that don't come from the program; technically, it must also be a value that commutes with the append operator on arrays.
```lean
theorem LogM.of_run_eq_wp {α : Type u} {β : Type v}
    {x : α × Array β} {prog : LogM β α}
    (h : LogM.run prog = x) (P : α × Array β → Prop)
    (hwp : wp prog (fun v l => P (v, l)) () #[]) : P x := by
  rw [← h]
  simp [wp, WP.wpTrans] at hwp
  exact hwp
```

Next, each operator in the library should be provided with a specification lemma.
There is only one: {name}`log`.
For new monads, these proofs must often break the abstraction boundaries of {tech}[Hoare triples] and weakest preconditions; the specifications that they provide can then be used abstractly by clients of the library.
```lean
theorem log_spec {x : β} {s' : Array β} :
    ⦃ fun s => s = s' ⦄ log x ⦃ fun _ s => s = s'.push x ⦄ := by
  constructor
  simp [log, wp, WP.wpTrans]
```

A better specification for {name}`log` is an {tech}[auto-framing specification]:
```lean
@[spec]
theorem log_spec_better {x : β} {Q : Unit → Array β → Prop} :
    ⦃ fun s => Q () (s.push x) ⦄ log x ⦃ Q ⦄ := by
  constructor
  simp [log, wp, WP.wpTrans]
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
```
:::

# Discharging Verification Conditions
%%%
tag := "vcgen-discharging"
%%%

The verification conditions that {tactic}`vcgen` produces are ordinary Lean goals, so any tactic can discharge them.
The `with` clause runs a single `grind`-mode step, typically `finish`, on every remaining verification condition.
The step runs inside the goal context that {tactic}`vcgen` internalized into `grind`'s E-graph during generation, so the context is not re-internalized for every verification condition.
Internalizing the context of a single verification condition takes time linear in the size of that context, so internalizing the context prefix that all verification conditions share only once is cheaper than internalizing each context on its own.

When working with concrete monads, the verification conditions speak directly about result values and states.
Monad-polymorphic theorems instead lead to goals over an abstract assertion lattice. `grind` discharges such goals when they reduce to entailments between pure assertions, as in the following example. Other goals over an abstract lattice can require a manual proof.

:::example "Monad-Polymorphic Proofs"
```imports -show
import Std.WP
import Std.Tactic.Do
```
```lean -show
open Std.WP Lean.Order

set_option experimental.vcgen true

```
The function {name}`bump` increments its state by the indicated amount and returns the resulting value.
The underlying monad {lean}`m` and its assertion types stay abstract.
Because the assertion type `Pred` is abstract, the specification below embeds its propositions with corner brackets.
```lean
variable {m : Type → Type v} [Monad m]
variable {Pred EPred : Type}
variable [Assertion Pred] [Assertion EPred]
variable [WPMonad m Pred EPred]

def bump (n : Nat) : StateT Nat m Nat := do
  modifyThe Nat (· + n)
  getThe Nat
```

The specification lemma for {name}`bump` quantifies over the abstract assertion lattice, and its verification conditions are entailments in that lattice.
The `finish` step discharges them:
```lean
theorem bump_correct :
    ⦃ fun n => ⌜n = k⌝ ⦄
    bump (m := m) i
    ⦃ fun r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  vcgen [bump] with finish
```
:::
