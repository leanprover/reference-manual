/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual

import Manual.Meta

import Std.Tactic.Do

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

set_option mvcgen.warning false

open Manual (comment)

#doc (Manual) "The `mvcgen` tactic" =>
%%%
tag := "mvcgen-tactic"
%%%

The {tactic}`mvcgen` tactic implements a _monadic verification condition generator_:
It breaks down a goal involving a program written using Lean's imperative `do` notation into a number of pure _verification conditions_ (VCs) that discharge said goal.
A verification condition is a sub-goal that does not mention the monad underlying the `do` block.

In order to use the {tactic}`mvcgen` tactic, `Std.Tactic.Do` must be imported and the namespace `Std.Do` must be opened.

```
import Std.Tactic.Do
open Std.Do
```

# Verifying imperative programs using `mvcgen`

This section is a tutorial introducing the most important concepts of {tactic}`mvcgen` top-down.
Recall that you need to import `Std.Tactic.Do` and open `Std.Do` to run these examples.

```lean -show
open Std.Do
```

:::example "Array Sum" (open := true) (keep := true)
As a “hello world” to {tactic}`mvcgen`, the following example {name}`mySum` computes the sum of an array using local mutability and a `for` loop.
Then it proves {name}`mySum` correct relative to {name}`Array.sum`, requiring us to specify an invariant for the loop:
```lean
def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- Focus on the part of the program with the `do` block (`Id.run ...`)
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- Break down into verification conditions
  mvcgen
  -- Specify the invariant which should hold throughout the loop
  -- * `out` refers to the current value of the `let mut` variable
  -- * `xs` is a `List.Cursor`, which is a data structure representing
  --   a list that is split into `xs.prefix` and `xs.suffix`.
  --   It tracks how far into the loop we have gotten.
  -- Our invariant is that `out` holds the sum of the prefix.
  -- The notation ⌜p⌝ embeds a `p : Prop` into the assertion language.
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- After specifying the invariant, we can further simplify our goals
  -- by "leaving the proof mode". `mleave` is just
  -- `simp only [...] at *` with a stable simp subset.
  all_goals mleave
  -- Prove that our invariant is preserved at each step of the loop
  case vc1 ih =>
    -- The goal here mentions `pref`, which binds the `prefix` field of
    -- the cursor passed to the invariant. Unpacking the
    -- (dependently-typed) cursor makes it easier for `grind`.
    grind
  -- Prove that the invariant is true at the start
  case vc2 =>
    grind
  -- Prove that the invariant at the end of the loop implies the
  -- property we wanted
  case vc3 h =>
    grind
```
Note that the case labels are actually unique prefixes of the full case labels.
Whenever referring to cases, only this prefix should be used; the suffix is merely a poor man's hint to the user where that particular VC came from.
For example,

* `vc1.step` conveys that this VC proves the inductive step for the loop
* `vc2.a.pre` is meant to prove that the hypotheses of a goal implies the precondition of a specification (of {name}`forIn`).
* `vc3.a.post` is meant to prove that the postcondition of a specification (of {name}`forIn`) implies the target of the goal.

After specifying the loop invariant, the proof can be shortened to just `all_goals mleave; grind` (cf. {tactic}`mleave`).
```lean
theorem mySum_correct_short (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  all_goals mleave; grind
```
This pattern is in fact so popular that `mvcgen` comes with special syntax for it:
```lean
theorem mySum_correct_shorter (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  with grind
```
The `mvcgen invariants ... with ...` expands to the same syntax as the
tactic sequence `mvcgen; case inv1 => ...; all_goals mleave; grind`
above. It is the form that we will be using from now on.
:::

It is helpful to compare the proof of {name}`mySum_correct_shorter` to a traditional correctness proof:

```lean
theorem mySum_correct_vanilla (l : Array Nat) : mySum l = l.sum := by
  -- Turn the array into a list
  cases l with | mk l =>
  -- Unfold `mySum` and rewrite `forIn` to `foldl`
  simp [mySum]
  -- Generalize the inductive hypothesis
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- Grind away
  induction l with grind
```

This proof is similarly succinct as the proof in {name}`mySum_correct_shorter` using {tactic}`mvcgen`.
However, the traditional approach relies on important properties of the program:

* The `for` loop does not `break` or `return` early. Otherwise, the `forIn` could not be rewritten to a `foldl`.
* The loop body `(· + ·)` is small enough to be repeated in the proof.
* The loop body is `pure`, that is, does not perform any effects.
  (Indeed, all computations in the base monad `Id` factor through `pure`.)
  While `forIn` could still be rewritten to a `foldlM`, reasoning about the monadic loop body can be tough for `grind`.

In the following sections, we will go through several examples to learn about {tactic}`mvcgen` and its support library, and also see where traditional proofs become difficult.
This is usually caused by

* `do` blocks using control flow constructs such as `for` loops, `break`s and early `return`.
* Effectful computations in non-`Id` monads.
  Such computations affect the implicit monadic context (state, exceptions) in ways that need to be reflected in loop invariants.

{tactic}`mvcgen` scales to these challenges with reasonable effort.

## Control flow

Let us consider another example that combines `for` loops with an early return.

:::example "Detecting Duplicates in a List" (open := true) (keep := true)
Recall that {name}`List.Nodup` is a predicate that asserts that a given list does not contain any duplicates.
The function {name}`nodup` below decides this predicate:

```lean
def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturn
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun xs seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
  with grind
```
:::

The proof has the same succinct structure as for the initial {name}`mySum` example, because we again offload all proofs to {tactic}`grind` and its existing framework around {name}`List.Nodup`.
Therefore, the only difference is in the invariant.
Since our loop has an early return, we construct the invariant using the helper function {lean}`Invariant.withEarlyReturn`.
This function allows us to specify the invariant in three parts:

* `onReturn ret seen` holds after the loop was left through an early return with value `ret`.
  In case of {name}`nodup`, the only value that is ever returned is {name}`false`, in which case {name}`nodup` has decided there _is_ a duplicate in the list.
* `onContinue xs seen` is the regular induction step that proves the invariant is preserved each loop iteration.
  The iteration state is captured by the cursor `xs`.
  The given example asserts that the set `seen` contains all the elements of previous loop iterations and asserts that there were no duplicates so far.
* `onExcept` must hold when the loop throws an exception.
  There are no exceptions in `Id`, so we leave it unspecified to use the default.
  (Exceptions will be discussed at a later point.)

:::TODO
Note that the form `mvcgen invariants?` would hint that {name}`Invariant.withEarlyReturn` is a useful way to construct the invariant:
```
example (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants?
```
:::

Now consider the following direct (and excessively golfed) proof without {tactic}`mvcgen`:

```lean
theorem nodup_correct_directly (l : List Int) : nodup l ↔ l.Nodup := by
  rw [nodup]
  generalize hseen : (∅ : Std.HashSet Int) = seen
  change ?lhs ↔ l.Nodup
  suffices h : ?lhs ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen by grind
  clear hseen
  induction l generalizing seen with grind [Id.run_pure, Id.run_bind]
```

Some observations:

* The proof is even shorter than the one with {tactic}`mvcgen`.
* The use of {tactic}`generalize` to generalize the accumulator relies on there being exactly one occurrence of `∅` to generalize. If that were not the case, we would have to copy parts of the program into the proof. This is a no go for larger functions.
* {tactic}`grind` splits along the control flow of the function and reasons about {name}`Id`, given the right lemmas.
  While this works for {name}`Id.run_pure` and {name}`Id.run_bind`, it would not work for {name}`Id.run_seq`, for example, because that lemma is not E-matchable. If {tactic}`grind` would fail, we would be forced to do all the control flow splitting and monadic reasoning by hand until {tactic}`grind` can pick up again.

The usual way to avoid replicating the control flow of a definition under proof is to use the {tactic}`fun_cases` or {tactic}`fun_induction` tactics.
Unfortunately, {tactic}`fun_cases` does not help with control flow inside a {name}`forIn` application, for example.
This is in contrast to {tactic}`mvcgen`, which ships with support for many {name}`forIn` implementations and is easily extended with `@[spec]` annotations for custom {name}`forIn` implementations.
Furthermore, a {tactic}`mvcgen`-powered proof will never need to copy any part of the original program.

## Compositional reasoning about effectful programs using Hoare triples

The previous examples reasoned about functions defined using `Id.run do <prog>` to make use of local mutability and early return in `<prog>`.
However, real-world programs often use `do` notation and monads `M` to hide away state and failure conditions as implicit “effects”.
In this use case, functions usually omit the `M.run`.
Instead they have monadic return type `M α` and compose well with other functions of that return type.

:::example "Generating Fresh Numbers" (open := true) (keep := true)
Here is an example involving a stateful function {name}`mkFresh` that returns auto-incremented counter values:

```lean
structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n ← (·.counter) <$> get
  modify (fun s => {s with counter := s.counter + 1})
  pure n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList
```

`mkFreshN n` returns `n` “fresh” numbers, modifying the internal {name}`Supply` state through {name}`mkFresh`.
Here, “fresh” refers to all previously generated numbers being distinct from the next generated number.
We can formulate and prove a correctness property {name}`mkFreshN_correct` in terms of {name}`List.Nodup`:

```lean
theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  -- Focus on `(mkFreshN n).run' s`.
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  -- Show something about monadic program `mkFresh n`.
  -- The `mkFreshN` and `mkFresh` arguments to `mvcgen` add to an
  -- internal `simp` set and makes `mvcgen` unfold these definitions.
  mvcgen [mkFreshN, mkFresh]
  invariants
  -- Invariant: The counter is larger than any accumulated number,
  --            and all accumulated numbers are distinct.
  -- Note that the invariant may refer to the state through function
  -- argument `state : Supply`. Since the next number to accumulate is
  -- the counter, it is distinct to all accumulated numbers.
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind
```
:::

## Composing specifications

Nested unfolding of definitions as in `mvcgen [mkFreshN, mkFresh]` is quite blunt but effective for small programs.
A more compositional way is to develop individual _specification lemmas_ for each monadic function.
These can either be passed as arguments to {tactic}`mvcgen` or registered in a global (or `scoped`, or `local`) database of specifications using the `@[spec]` attribute:

:::example "Decomposing a Proof into Specifications" (open := true) (keep := true)
```lean
@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  -- Unfold `mkFresh` and blast away:
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `mvcgen [mkFreshN, mkFresh_spec]` if `mkFresh_spec` were not
  -- registered with `@[spec]`
  mvcgen [mkFreshN]
  invariants
  -- As before:
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind

theorem mkFreshN_correct_compositional (n : Nat) :
    ((mkFreshN n).run' s).Nodup :=
  -- The type `⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄` of `mkFreshN` is
  -- definitionally equal to
  -- `∀ (n : Nat) (s : Supply), True → ((mkFreshN n).run' s).Nodup`
  mkFreshN_spec n s True.intro
```

```lean -show
variable {c : Nat}
```
Here, the notation {lean}`⦃fun state => ⌜state.counter = c⌝⦄ mkFresh ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄` denotes a _Hoare triple_ (cf. {name}`Std.Do.Triple`).
Specifications for monadic functions always have such a Hoare triple result type.
:::

## Hoare triples

{docstring Std.Do.Triple}

:::syntax term (title := "Hoare triple") (namespace := Std.Do)
```grammar
⦃ term ⦄ term ⦃ term ⦄
```
:::

{docstring Std.Do.Triple.and}

{docstring Std.Do.Triple.mp}

```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {α σ ε : Type u} {P : Assertion ps} {Q : PostCond α ps} {prog : m α}
```
Given the meaning of Hoare triples above, the specification theorem for {name}`mkFresh` says:

> If {lean}`c` refers to the {name}`Supply.counter` field of the {name}`Supply` prestate, then running {name}`mkFresh` returns {lean}`c` and modifies the {name}`Supply.counter` of the poststate to be larger than {lean}`c`.

Note that this specification is lossy: {name}`mkFresh` could increment its state by an arbitrary non-negative amount and still satisfy the specification.
This is good, because specifications may _abstract over_ uninteresting implementation details, ensuring resilient and small proofs.

Hoare triples are defined in terms of a logic of stateful predicates plus a weakest precondition semantics {lean}`wp⟦prog⟧` that translates monadic programs into this logic:

```lean
-- This is the definition of Std.Do.Triple:
def Triple [WP m ps] {α : Type u} (prog : m α)
    (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦prog⟧ Q
```

The {name}`WP` type class maps a monad {lean}`m` to its {name}`PostShape` {lean}`ps`, and this {name}`PostShape` governs the exact shape of the {name}`Std.Do.Triple`.
Many of the standard monad transformers such as {name}`StateT`, {name}`ReaderT` and {name}`ExceptT` come with a canonical {name}`WP` instance.
For example, `StateT σ` comes with a {name}`WP` instance that adds a `σ` argument to every {name}`Assertion`.
Stateful entailment `⊢ₛ` eta-expands through these additional `σ` arguments.
For {name}`StateM` programs, the following type is definitionally equivalent to {name}`Std.Do.Triple`:

```lean
def StateMTriple {α σ : Type u} (prog : StateM σ α)
    (P : σ → ULift Prop) (Q : (α → σ → ULift Prop) × PUnit) : Prop :=
  ∀ s, (P s).down → let (a, s') := prog.run s; (Q.1 a s').down

example : @StateMTriple α σ = Std.Do.Triple (m := StateM σ) := rfl
```

```lean -show
variable {p : Prop}
```

The common postcondition notation `⇓ r => ...` injects an assertion of type `α → Assertion ps` into
`PostCond ps` (the `⇓` is meant to be parsed like `fun`); in case of {name}`StateM` by adjoining it with an empty tuple {name}`PUnit.unit`.
The shape of postconditions becomes more interesting once exceptions enter the picture.
The notation {lean}`⌜p⌝` embeds a pure hypotheses {lean}`p` into a stateful assertion.
Vice versa, any stateful hypothesis {lean}`P` is called _pure_ if it is equivalent to {lean}`⌜p⌝`
for some {lean}`p`.
Pure, stateful hypotheses may be freely moved into the regular Lean context and back.
(This can be done manually with the {tactic}`mpure` tactic.)

### An advanced note about pure preconditions and a notion of frame rule

This subsection is a bit of a digression and can be skipped on first reading.

Say the specification for some [`Aeneas`](https://github.com/AeneasVerif/aeneas)-inspired monadic addition function `x +? y : M UInt8` has the
requirement that the addition won't overflow, that is, `h : x.toNat + y.toNat ≤ UInt8.size`.
Should this requirement be encoded as a regular Lean hypothesis of the specification (`add_spec_hyp`) or should this requirement be encoded as a pure precondition of the Hoare triple, using `⌜·⌝` notation (`add_spec_pre`)?

```
theorem add_spec_hyp (x y : UInt8) (h : x.toNat + y.toNat ≤ UInt8.size) :
    ⦃⌜True⌝⦄ x +? y ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := ...

theorem add_spec_pre (x y : UInt8) :
    ⦃⌜x.toNat + y.toNat ≤ UInt8.size⌝⦄
    x +? y
    ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := ...
```

The first approach is advisable, although it should not make a difference in practice.
The VC generator will move pure hypotheses from the stateful context into the regular Lean context, so the second form turns effectively into the first form.
This is referred to as _framing_ hypotheses (cf. the {tactic}`mpure` and {tactic}`mframe` tactics).
Hypotheses in the Lean context are part of the immutable _frame_ of the stateful logic, because in contrast to stateful hypotheses they survive the rule of consequence.

## Monad transformer stacks

Real-world programs often orchestrate the interaction of independent subsystems through a stack of monad transformers.
We can tweak the previous example to demonstrate this.

```lean -show
namespace Stack
variable {m : Type → Type} {α : Type} {ps : PostShape.{0}}
attribute [-instance] Lake.instMonadLiftTOfMonadLift_lake
```

:::example "Transformer Stacks" (open := true) (keep := true)
Suppose that {name}`mkFresh` is generalized to work in any base monad {lean}`m` under {lean}`StateT Supply`.
Furthermore, {name}`mkFreshN` is defined in terms of a concrete monad transformer stack {name}`AppM` and lifts {name}`mkFresh` into {name}`AppM`.
Then the {tactic}`mvcgen`-based proof goes through unchanged:

```lean
def mkFresh [Monad m] : StateT Supply m Nat := do
  let n ← (·.counter) <$> get
  modify (fun s => {s with counter := s.counter + 1})
  pure n

abbrev AppM := StateT Bool (StateT Supply (ReaderM String))
abbrev liftCounterM : StateT Supply (ReaderM String) α → AppM α := liftM

def mkFreshN (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let n ← liftCounterM mkFresh
    acc := acc.push n
  return acc.toList

@[spec]
theorem mkFresh_spec [Monad m] [WPMonad m ps] (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh (m := m)
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `liftCounterM` here ensures unfolding
  mvcgen [mkFreshN, liftCounterM]
  invariants
  · ⇓⟨xs, acc⟩ _ state =>
      ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝
  with grind
```

The {name}`WPMonad` type class asserts that {lean}`wp⟦prog⟧` distributes over the {name}`Monad` operations (“monad morphism”).
This proof might not look much more exciting than when only a single monad was involved.
However, under the radar of the user the proof builds on a cascade of specifications for `MonadLift` instances.
:::

```lean -show
end Stack
```

## Exceptions

```lean -show
variable {Q' : α → Assertion ps}
```

If `let mut` is the first-order pendant to {name}`StateT`, then early `return` is the first-order pendant to {name}`ExceptT`.
We have seen how the {tactic}`mvcgen` copes with {name}`StateT`; here we will look at the program logic's support for {name}`ExceptT`.

Exceptions are the reason why the type of postconditions {lean}`PostCond α ps` is not simply a single condition of type {lean}`α → Assertion ps` for the success case.
To see why, suppose the latter was the case, and suppose that program {lean}`prog` throws an exception in a prestate satisfying {lean}`P`.
Should we be able to prove {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄`?
(Recall that `⇓` is grammatically similar to `fun`.)
There is no result `r`, so it is unclear what this proof means for {lean}`Q'`!

So there are two reasonable options, inspired by non-termination in traditional program logics:

1. _Total_ correctness interpretation: {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` asserts that, given {lean}`P` holds, then {lean}`prog` terminates _and_ {lean}`Q'` holds for the result.
2. _Partial_ correctness interpretation: {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` asserts that, given {lean}`P` holds, and _if_ {lean}`prog` terminates _then_ {lean}`Q'` holds for the result.

The notation {lean}`⇓ r => Q' r` has the total interpretation (cf. {name}`PostCond.noThrow`), while {lean}`⇓? r => Q' r` has the partial interpretation (cf. {name}`PostCond.mayThrow`).

{docstring Std.Do.PostCond}

{docstring Std.Do.PostCond.noThrow}

{docstring Std.Do.PostCond.mayThrow}

:::syntax term (title := "Postconditions") (namespace := Std.Do)
```grammar
⇓ $_:term* => $_:term
```

```grammar
⇓? $_:term* => $_:term
```
:::

So in the running example, {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` is unprovable, but {lean}`⦃P⦄ prog ⦃⇓? r => Q' r⦄` is trivially provable.
However, the binary choice suggests that there is actually a _spectrum_ of correctness properties to express.
The notion of postconditions {name}`PostCond` in `Std.Do` supports this spectrum.

For example, suppose that our {name}`Supply` of fresh numbers is bounded and we want to throw an exception if the supply is exhausted.
Then {name}`mkFreshN` should throw an exception _only if_ the supply is indeed exhausted.
The following correctness property expresses this:

```lean -show
namespace Exceptions
```

```lean
structure Supply where
  counter : Nat
  limit : Nat
  property : counter ≤ limit

def mkFresh : EStateM String Supply Nat := do
  let supply ← get
  if h : supply.counter = supply.limit then
    throw s!"Supply exhausted: {supply.counter} = {supply.limit}"
  else
    let n := supply.counter
    have := supply.property
    set {supply with counter := n + 1, property := by omega}
    pure n

def mkFreshN (n : Nat) : EStateM String Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃post⟨fun r state => ⌜r = c ∧ c < state.counter⌝,
          fun _ state => ⌜c = state.counter ∧ c = state.limit⌝⟩⦄ := by
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄
    mkFreshN n
    ⦃post⟨fun r => ⌜r.Nodup⌝,
          fun _msg state => ⌜state.counter = state.limit⌝⟩⦄ := by
  mvcgen [mkFreshN]
  invariants
  · post⟨fun ⟨xs, acc⟩ state =>
           ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝,
         fun _msg state => ⌜state.counter = state.limit⌝⟩
  with grind

theorem mkFreshN_correct (n : Nat) :
    match (mkFreshN n).run s with
    | .ok    l _  => l.Nodup
    | .error _ s' => s'.counter = s'.limit := by
  generalize h : (mkFreshN n).run s = x
  apply EStateM.of_wp_run_eq h
  mvcgen
```

Just as any {lean}`StateT σ`-like layer in the monad stack gives rise to a {lean}`PostShape.arg σ` layer in the {lean}`ps`
that {name}`WP` maps into, any {lean}`ExceptT ε`-like layer gives rise to a {lean}`PostShape.except ε` layer.

Every {lean}`PostShape.arg σ` adds another `σ → ...` layer to the language of {lean}`Assertion`s.
Every {lean}`PostShape.except ε` leaves the {lean}`Assertion` language unchanged, but adds another exception
condition to the postcondition.

{docstring Std.Do.Assertion}

Hence the {name}`WP` instance for {lean}`EStateM ε σ` maps to the {name}`PostShape` {lean}`PostShape.except ε (.arg σ .pure)`, just
as for {lean}`ExceptT ε (StateM σ)`.

```lean -show
end Exceptions
```

## Extending `mvcgen` with support for custom monads

The {tactic}`mvcgen` framework is designed to be extensible.
None of the monads so far have in any way been hard-coded into {tactic}`mvcgen`.
Rather, {tactic}`mvcgen` relies on instances of the {name}`WP` and {name}`WPMonad` type class and user-provided specifications to generate verification conditions.

The {name}`WP` instance defines the weakest precondition interpretation of a monad {lean}`m` into a predicate transformer {lean}`PredTrans ps`,
and the matching {name}`WPMonad` instance asserts that this translation distributes over the {name}`Monad` operations.

{docstring Std.Do.PredTrans}

{docstring Std.Do.WP}

:::syntax term (title := "Weakest preconditions") (namespace := Std.Do)
```grammar
wp⟦ $_:term ⟧
```
:::

{docstring Std.Do.WPMonad}

:::example "Adding `mvcgen` support for Aeneas" (open := true)
Suppose one wants to use `mvcgen` to generate verification conditions for programs generated by [`Aeneas`](https://github.com/AeneasVerif/aeneas).
`Aeneas` translates Rust programs into Lean programs in the following {name}`Result` monad:

```lean
inductive Error where
  | integerOverflow: Error
  -- ... more error kinds ...

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div

instance Result.instMonad : Monad Result where
  pure x := .ok x
  bind x f := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance Result.instLawfulMonad : LawfulMonad Result := by
  -- TODO: Replace sorry with grind when it no longer introduces section
  --       variables
  apply LawfulMonad.mk' <;> (simp only [Result.instMonad]; sorry)
```

Support for this monad is a matter of

1. Adding a {name}`WP` and {name}`WPMonad` instance for {name}`Result`
2. Registering specification lemmas for the translation of basic Rust primitives such as addition etc.

The first part is straightforward:

```lean
instance Result.instWP : WP Result (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

-- set_option trace.Meta.synthInstance true in
instance Result.instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure := by
    intros
    ext Q
    simp [wp, PredTrans.pure, pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [instWP, bind]
    ext Q
    cases x <;> simp [PredTrans.bind, PredTrans.const]

theorem Result.of_wp {α} {x : Result α} (P : Result α → Prop) :
    (⊢ₛ wp⟦x⟧ post⟨fun a => ⌜P (.ok a)⌝,
                  fun e => ⌜P (.fail e)⌝⟩) → P x := by
  intro hspec
  simp only [instWP] at hspec
  split at hspec <;> simp_all
```

The {name}`WP` instance above translates programs in {lean}`Result α` to predicate transformers in {lean}`PredTrans ps α`.
That is, a function in {lean}`PostCond α ps → Assertion ps`, mapping a postcondition to its weakest precondition.
Note that this definition of the {name}`WP` instance determines what properties can be derived from proved specifications via {lean}`Result.of_wp`.
This lemma defines what “weakest precondition” means.

To exemplify the second part, here is an example definition of {name}`UInt32` addition in {name}`Result` that models integer overflow:

```lean
instance : MonadExcept Error Result where
  throw e := .fail e
  tryCatch x h := match x with
  | .ok v => pure v
  | .fail e => h e
  | .div => .div

def addOp (x y : UInt32) : Result UInt32 :=
  if x.toNat + y.toNat ≥ UInt32.size then
    throw .integerOverflow
  else
    pure (x + y)
```

There are two relevant specification lemmas to register:

```lean
@[spec]
theorem Result.throw_spec {α Q} (e : Error) :
    ⦃Q.2.1 e⦄ throw (m := Result) (α := α) e ⦃Q⦄ := id

@[spec]
theorem addOp_ok_spec {x y} (h : x.toNat + y.toNat < UInt32.size) :
    ⦃⌜True⌝⦄
    addOp x y
    ⦃⇓ r => ⌜r = x + y ∧ (x + y).toNat = x.toNat + y.toNat⌝⦄ := by
  mvcgen [addOp] with (simp_all; try grind)
```

This is already enough to prove the following example:

```lean
example :
  ⦃⌜True⌝⦄
  do let mut x ← addOp 1 3
     for _ in [:4] do
        x ← addOp x 5
     return x
  ⦃⇓ r => ⌜r.toNat = 24⌝⦄ := by
  mvcgen
  invariants
  · ⇓⟨xs, x⟩ => ⌜x.toNat = 4 + 5 * xs.prefix.length⌝
  with (simp_all [UInt32.size]; try grind)
```
:::

## Proof mode for stateful goals

```lean -show
variable {σs : List (Type u)} {H T : SPred σs}
```

It is a priority of {tactic}`mvcgen` to break down monadic programs into VCs that are straightforward to understand.
For example, when the monad stack is monomorphic and all loop invariants have been instantiated, an invocation of `all_goals mleave` should simplify away any `Std.Do.SPred` specific constructs and leave behind a goal that is easily understood by humans and `grind`.
This `all_goals mleave` step is carried out automatically by {tactic}`mvcgen` after loop invariants have been instantiated.

However, there are times when `mleave` will be unable to remove all {name}`Std.Do.SPred` constructs.
In this case, verification conditions of the form {lean}`H ⊢ₛ T` will be left behind.
The assertion language {name}`Assertion` translates into an {name}`Std.Do.SPred` as follows:

```lean -keep
abbrev PostShape.args : PostShape.{u} → List (Type u)
  | .pure => []
  | .arg σ s => σ :: PostShape.args s
  | .except _ s => PostShape.args s

abbrev Assertion (ps : PostShape.{u}) : Type u :=
  SPred (PostShape.args ps)
```

{docstring Std.Do.SPred}

{docstring Std.Do.SPred.entails}

:::syntax term (title := "Notation for `SPred`") (namespace := Std.Do)
```grammar
⌜$_:term⌝
```

```grammar
$_:term ⊢ₛ $_:term
```

```grammar
$_:term ⊣⊢ₛ $_:term
```

```grammar
spred($_:term ∧ $_:term)
```

```grammar
spred($_:term ∨ $_:term)
```

```grammar
spred($_:term → $_:term)
```

```grammar
spred(¬$_:term)
```

```grammar
spred(∀ $_:ident, $_:term)
```

```grammar
spred(∃ $_:ident, $_:term)
```
:::

A common case for when a VC of the form {lean}`H ⊢ₛ T` is left behind is when the base monad {lean}`m` is polymorphic.
In this case, the proof will depend on a {lean}`WP m ps` instance which governs the translation into the {name}`Assertion` language, but the exact correspondence to `σs : List (Type u)` is yet unknown.
To successfully discharge such a VC, `mvcgen` comes with an entire proof mode that is inspired by that of the Iris concurrent separation logic.
(In fact, the proof mode was adapted in large part from its Lean clone, [`iris-lean`](https://github.com/leanprover-community/iris-lean).)
The Lean 4 test file [`tests/lean/run/spredProofMode.lean`](https://github.com/leanprover/lean4/blob/76971a88fff3b3df75dceb588b5bd98b1552bafc/tests/lean/run/spredProofMode.lean) contains many examples of that proof mode to learn from, and {ref "tactic-ref-spred"}[the reference manual] contains a list of all proof mode tactics.

## Further reading

More examples can be found in Lean's test suite.
* [`tests/lean/run/doLogicTests.lean`](https://github.com/leanprover/lean4/blob/76971a88fff3b3df75dceb588b5bd98b1552bafc/tests/lean/run/doLogicTests.lean) is a kitchen sink test file with many examples.
* [`tests/lean/run/bhaviksSampler.lean`](https://github.com/leanprover/lean4/blob/76971a88fff3b3df75dceb588b5bd98b1552bafc/tests/lean/run/bhaviksSampler.lean) is a stubbed out example from a larger development due to Bhavik Mehta.
* [Markus Himmel's `human-eval-lean` project](https://github.com/TwoFX/human-eval-lean/) has a limited number of `mvcgen`-based proofs for imperative algorithm implementations. Contributions welcome!
* [Rish Vaishnav's ongoing `qsort` formalization](https://github.com/rish987/qsort/) is the largest example of `mvcgen` to date.
