/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Różowski
-/

import VersoManual

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

set_option maxRecDepth 600


#doc (Manual) "The `coinductive` Command" =>
%%%
tag := "coinductive-command"
%%%

The {keywordOf Lean.Parser.Command.declaration}`coinductive` command provides a declarative syntax for defining coinductive predicates that mirrors the syntax of {keywordOf Lean.Parser.Command.declaration}`inductive` declarations.
Rather than writing a recursive function with {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint`, users specify constructors just as they would for an inductive type.

:::syntax command (title := "Coinductive Predicates")
```grammar
coinductive $_ $_* : $_ where
  $_*
```
The {keywordOf Lean.Parser.Command.declaration}`coinductive` command defines a coinductive predicate by specifying its constructors.
It can only be used to define predicates, that is, types valued in {lean}`Prop`.
:::

The {keywordOf Lean.Parser.Command.declaration}`coinductive` command defines the same predicate as a corresponding {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` definition, but additionally generates constructors and a case analysis principle, much like an ordinary {keywordOf Lean.Parser.Command.declaration}`inductive` declaration.

:::example "Coinductive Predicate via `coinductive`"
The predicate {lean}`InfSeq` from the {ref "coinductive-predicates"}[running example] can equivalently be defined using the {keywordOf Lean.Parser.Command.declaration}`coinductive` command:

```lean
section
variable (α : Type)

coinductive InfSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → InfSeq r b → InfSeq r a
```

This generates a constructor and a coinduction principle:

```lean (name := checkInfSeqStep)
#check @InfSeq.step
```
```leanOutput checkInfSeqStep
InfSeq.step : ∀ (α : Type) (r : α → α → Prop) {a b : α}, r a b → InfSeq α r b → InfSeq α r a
```

```lean (name := checkInfSeqCoinduct)
#check @InfSeq.coinduct
```
```leanOutput checkInfSeqCoinduct
InfSeq.coinduct : ∀ (α : Type) (r : α → α → Prop) (pred : α → Prop),
  (∀ (a : α), pred a → ∃ b, r a b ∧ pred b) → ∀ (a : α), pred a → InfSeq α r a
```

A case analysis principle is also available:

```lean (name := checkInfSeqCasesOn)
#check @InfSeq.casesOn
```
```leanOutput checkInfSeqCasesOn
InfSeq.casesOn : ∀ (α : Type) (r : α → α → Prop) {motive : (a : α) → InfSeq α r a → Prop} {a : α} (t : InfSeq α r a),
  (∀ {a b : α} (a_1 : r a b) (a_2 : InfSeq α r b), motive a ⋯) → motive a t
```

Case analysis can be used in proofs via the {tactic}`cases` tactic:

```lean
theorem InfSeq.casesOnTest (r : α → α → Prop)
    (a : α) : InfSeq α r a → ∃ b, r a b := by
  intro h
  cases h
  case step b _ hr => exists b
```

```lean
end
```
:::


# Elaboration
%%%
tag := "coinductive-elaboration"
%%%

Under the hood, the {keywordOf Lean.Parser.Command.declaration}`coinductive` command is elaborated in several steps.
First, it is processed as if it were an ordinary {keywordOf Lean.Parser.Command.declaration}`inductive` declaration.
Before registering the types with the kernel, however, a {deftech}_flat inductive_ (also called a _functor form_) is created: each recursive occurrence of the coinductive predicate in the premises of a constructor is replaced by an explicit parameter.

```lean -show
section
variable (α : Type)
coinductive InfSeqF (r : α → α → Prop) : α → Prop where
  | step : r a b → InfSeqF r b → InfSeqF r a
end
```

:::example "Flat Inductive"
For {lean}`InfSeqF`, the generated flat inductive is:

```lean (name := checkFunctor) -keep
#check @InfSeqF._functor
```
```leanOutput checkFunctor
InfSeqF._functor : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop
```

Its constructor takes the predicate parameter in place of recursive calls:

```lean (name := printFunctor) -keep
set_option pp.proofs true in
#print InfSeqF._functor
```

```leanOutput printFunctor
inductive InfSeqF._functor : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop
number of parameters: 3
constructors:
InfSeqF._functor.step : ∀ (α : Type) (r : α → α → Prop) (InfSeqF._functor.call : α → Prop) {a b : α},
  r a b → InfSeqF._functor.call b → InfSeqF._functor α r InfSeqF._functor.call a
```
:::

An equivalent {deftech}_existential form_ is then constructed, expressing the same predicate using existential quantifiers and conjunctions.
This form is used for monotonicity checking and for generating readable coinduction principles.

:::example "Existential Form"

```lean (name := printExist) -keep
set_option pp.proofs true in
#print InfSeqF._functor.existential
```

```leanOutput printExist
def InfSeqF._functor.existential : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop :=
fun α r InfSeqF._functor.call a => ∃ b, r a b ∧ InfSeqF._functor.call b
```

The two forms are connected by an equivalence theorem:

```lean (name := checkExistEquiv) -keep
#check @InfSeqF._functor.existential_equiv
```
```leanOutput checkExistEquiv
InfSeqF._functor.existential_equiv : ∀ (α : Type) (r : α → α → Prop) (InfSeqF._functor.call : α → Prop) (a : α),
  InfSeqF._functor α r InfSeqF._functor.call a ↔ ∃ b, r a b ∧ InfSeqF._functor.call b
```
:::

The existential form is then registered as a coinductive predicate using the {ref "partial-fixpoint"}[partial fixpoint] machinery with the {name}`Lean.Order.ReverseImplicationOrder` complete lattice instance.
Because the flat inductive has already been checked for strict positivity by the kernel, monotonicity of the resulting functor is guaranteed.
Using the correspondence between the flat inductive and the existential form, constructors and a case analysis eliminator are generated, just as for regular inductive types.

:::paragraph
The following declarations are generated for a coinductive predicate named `P`:

 * `P._functor`: the {tech}[flat inductive]
 * `P._functor.existential`: the {tech}[existential form]
 * `P._functor.existential_equiv`: equivalence between the two forms
 * `P.functor_unfold`: theorem connecting the coinductive predicate to its flat inductive
 * Constructors (e.g., `P.step`): corresponding to each constructor in the declaration
 * `P.casesOn`: case analysis principle
 * `P.coinduct`: coinduction principle

:::

# Mutual Coinductive and Inductive Blocks
%%%
tag := "mutual-coinductive-syntax"
%%%

In a {tech}[mutual block] containing {keywordOf Lean.Parser.Command.declaration}`coinductive` definitions, the {keywordOf Lean.Parser.Command.declaration}`inductive` keyword is reinterpreted: instead of being registered as an ordinary kernel inductive type, it is elaborated via the lattice-theoretic {tech (key := "lattice-theoretic inductive predicate")}[inductive fixpoint] machinery.
This allows mixing coinductive and inductive predicates in the same mutual block.

:::example "Mutual Coinductive-Inductive Block"
The predicates {lean}`Tick` and {lean}`Tock` are defined mutually, with {lean}`Tick` as a coinductive predicate and {lean}`Tock` as an inductive predicate:

```lean
mutual
  coinductive Tick : Prop where
  | mk : ¬Tock → Tick

  inductive Tock : Prop where
  | mk : ¬Tick → Tock
end
```

Both constructors are available:
```lean (name := checkTickMk)
#check @Tick.mk
```
```leanOutput checkTickMk
Tick.mk : ¬Tock → Tick
```
```lean (name := checkTockMk)
#check @Tock.mk
```
```leanOutput checkTockMk
Tock.mk : ¬Tick → Tock
```

A mutual induction principle is generated:
```lean (name := checkMutualInduct)
#check @Tick.mutual_induct
```
```leanOutput checkMutualInduct
Tick.mutual_induct : ∀ (pred_1 pred_2 : Prop),
  (pred_1 → pred_2 → False) → ((pred_1 → False) → pred_2) → (pred_1 → Tick) ∧ (Tock → pred_2)
```
:::

# Restrictions
%%%
tag := "coinductive-restrictions"
%%%

:::paragraph
The {keywordOf Lean.Parser.Command.declaration}`coinductive` command has the following restrictions:

 * It can only define predicates, that is, types valued in {lean}`Prop`.
   Attempting to define a coinductive type in {lean}`Type` or higher universes results in an error.

 * It is not allowed inside macro scopes.

 * The name of a coinductive predicate must not conflict with the name of one of its constructors.

 * Pattern matching via {keywordOf Lean.Parser.Term.match}`match` is not yet supported; use the {tactic}`cases` tactic instead.

:::

:::example "Restriction to Predicates"
Attempting to define a coinductive type that is not a predicate results in an error:

```lean +error (name := notPredErr) -keep
coinductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
```
```leanOutput notPredErr
`coinductive` keyword can only be used to define predicates
```
:::
