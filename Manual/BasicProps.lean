/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers


open Manual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "Basic Propositions" =>
%%%
tag := "basic-props"
%%%

With the exception of implication and universal quantification, logical connectives and quantifiers are implemented as {tech}[inductive types] in the {lean}`Prop` universe.
In some sense, the connectives described in this chapter are not special—they could be implemented by any user.
However, these basic connectives are used pervasively in the standard library and built-in proof automation tools.



# Truth
%%%
tag := "true-false"
%%%

Fundamentally, there are only two propositions in Lean: {lean}`True` and {lean}`False`.
The axiom of propositional extensionality ({name}`propext`) allows propositions to be considered equal when they are logically equivalent, and every true proposition is logically equivalent to {lean}`True`.
Similarly, every false proposition is logically equivalent to {lean}`False`.

{lean}`True` is an inductively defined proposition with a single constructor that takes no parameters.
It is always possible to prove {lean}`True`.
{lean}`False`, on the other hand, is an inductively defined proposition with no constructors.
Proving it requires finding an inconsistency in the current context.

Both {lean}`True` and {lean}`False` are {ref "subsingleton-elimination"}[subsingletons]; this means that they can be used to compute inhabitants of non-propositional types.
For {lean}`True`, this amounts to ignoring the proof, which is not informative.
For {lean}`False`, this amounts to a demonstration that the current code is unreachable and does not need to be completed.

{docstring True}

{docstring False}

{docstring False.elim}

:::example "Dead Code and Subsingleton Elimination"


The fourth branch in the definition of {lean}`f` is unreachable, so no concrete {lean}`String` value needs to be provided:
```lean
def f (n : Nat) : String :=
  if h1 : n < 11 then
    "Small"
  else if h2 : n > 13 then
    "Large"
  else if h3 : n % 2 = 1 then
    "Odd"
  else if h4 : n ≠ 12 then
    False.elim (by omega)
  else "Twelve"
```
In this example, {name}`False.elim` indicates to Lean that the current local context is logically inconsistent: proving {name}`False` suffices to abandon the branch.

Similarly, the definition of {name}`g` appears to have the potential to be non-terminating.
However, the recursive call occurs on an unreachable path through the program.
The proof automation used for producing termination proofs can detect that the local assumptions are inconsistent.
```lean
def g (n : Nat) : String :=
  if n < 11 then
    "Small"
  else if n > 13 then
    "Large"
  else if n % 2 = 1 then
    "Odd"
  else if n ≠ 12 then
    g (n + 1)
  else "Twelve"
termination_by n
```
:::

# Logical Connectives

Conjunction is implemented as the inductively defined proposition {name}`And`.
The constructor {name}`And.intro` represents the introduction rule for conjunction: to prove a conjunction, it suffices to prove both conjuncts.
Similarly, {name}`And.elim` represents the elimination rule: given a proof of a conjunction and a proof of some other statement that assumes both conjuncts, the other statement can be proven.
Because {name}`And` is a {tech}[subsingleton], {name}`And.elim` can also be used as part of computing data.
However, it should not be confused with {name}`PProd`: using non-computable reasoning principles such as the Axiom of Choice to define data (including {lean}`Prod`) causes Lean to be unable to compile and run the resulting program, while using them in a proof of a proposition causes no such issue.

In a {ref "tactics"}[tactic] proof, conjunctions can be proved using {name}`And.intro` explicitly via {tactic}`apply`, but {tactic}`constructor` is more common.
When multiple conjunctions are nested in a proof goal, {tactic}`and_intros` can be used to apply {name}`And.intro` in each relevant location.
Assumptions of conjunctions in the context can be simplified using {tactic}`cases`, pattern matching with {tactic}`let` or {tactic show:="match"}`Lean.Parser.Tactic.match`, or {tactic}`rcases`.

{docstring And}

{docstring And.elim}

Disjunction implemented as the inductively defined proposition {name}`Or`.
It has two constructors, one for each introduction rule: a proof of either disjunct is sufficient to prove the disjunction.
While the definition of {lean}`Or` is similar to that of {lean}`Sum`, it is quite different in practice.
Because {lean}`Sum` is a type, it is possible to check _which_ constructor was used to create any given value.
{lean}`Or`, on the other hand, forms propositions: terms that prove a disjunction cannot be interrogated to check which disjunct was true.
In other words, because {lean}`Or` is not a {tech}[subsingleton], its proofs cannot be used as part of a computation.

In a {ref "tactics"}[tactic] proof, disjunctions can be proved using either constructor ({name}`Or.inl` or {name}`Or.inr`) explicitly via {tactic}`apply`.
Assumptions of disjunctions in the context can be simplified using {tactic}`cases`, pattern matching with {tactic show:="match"}`Lean.Parser.Tactic.match`, or {tactic}`rcases`.

{docstring Or}

When either disjunct is {tech}[decidable], it becomes possible to use {lean}`Or` to compute data.
This is because the decision procedure's result provides a suitable branch condition.

{docstring Or.by_cases}

{docstring Or.by_cases'}


```lean (show := false)
section
variable {P : Prop}
```
Rather than encoding negation as an inductive type, {lean}`¬P` is defined to mean {lean}`P → False`.
In other words, to prove a negation, it suffices to assume the negated statement and derive a contradiction.
This also means that {lean}`False` can be derived immediately from a proof of a proposition and its negation, and then used to prove any proposition or inhabit any type.
```lean (show := false)
end
```


{docstring Not}

{docstring absurd}

{docstring Not.elim}




```lean (show := false)
section
variable {A B : Prop}
```
Implication is represented using {ref "function-types"}[function types] in the {tech}[universe] of {tech}[propositions].
To prove {lean}`A → B`, it is enough to prove {lean}`B` after assuming {lean}`A`.
This corresponds to the typing rule for {keywordOf Lean.Parser.Term.fun}`fun`.
Similarly, the typing rule for function application corresponds to {deftech}_modus ponens_: given a proof of {lean}`A → B` and a proof of {lean}`A`, {lean}`B` can be proved.

:::example "Truth-Functional Implication"
The representation of implication as functions in the universe of propositions is equivalent to the traditional definition in which {lean}`A → B` is defined as {lean}`(¬A) ∨ B`.
This can be proved using {tech}[propositional extensionality] and the law of the excluded middle:
```lean
theorem truth_functional_imp {A B : Prop} :
    ((¬ A) ∨ B) = (A → B) := by
  apply propext
  constructor
  . rintro (h | h) a <;> trivial
  . intro h
    by_cases A
    . apply Or.inr; solve_by_elim
    . apply Or.inl; trivial
```
:::

```lean (show := false)
end
```


Logical equivalence, or “if and only if”, is represented using a structure that is equivalent to the conjunction of both directions of the implication.

{docstring Iff}

{docstring Iff.elim}

:::syntax term (title := "Propositional Connectives")
The logical connectives other than implication are typically referred to using dedicated syntax, rather than via their defined names:
```grammar
$_ ∧ $_
```
```grammar
$_ ∨ $_
```
```grammar
¬ $_
```
```grammar
$_ ↔ $_
```
:::


# Quantifiers

Just as implication is implemented as ordinary function types in {lean}`Prop`, universal quantification is implemented as dependent function types in {lean}`Prop`.
Because {lean}`Prop` is {tech}[impredicative], any function type in which the {tech}[codomain] is a {lean}`Prop` is itself a {lean}`Prop`, even if the {tech}[domain] is a {lean}`Type`.
The typing rules for dependent functions precisely match the introduction and elimination rules for universal quantification: if a predicate holds for any arbitrarily chosen element of a type, then it holds universally.
If a predicate holds universally, then it can be instantiated to a proof for any individual.

:::syntax term (title := "Universal Quantification")

```grammar
∀ $x:ident $[$_:ident]* $[: $t]?, $_
```
```grammar
forall $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
∀ $_ $[$_]*, $_
```

```grammar
forall $_ $[$_]*, $_
```

Universal quantifiers bind one or more variables, which are then in scope in the final term.
The identifiers may also be `_`.
With parenthesized type annotations, multiple bound variables may have different types, while the unparenthesized variant requires that all have the same type.
:::

Even though universal quantifiers are represented by functions, their proofs should not be thought of as computations.
Because of proof irrelevance and the elimination restriction for propositions, there's no way to actually compute data using these proofs.
As a result, they are free to use reasoning principles that are not readily computed, such as the classical Axiom of Choice.


Existential quantification is implemented as a structure that is similar to {name}`Subtype` and {name}`Sigma`: it contains a {deftech}_witness_, which is a value that satisfies the predicate, along with a proof that the witness does in fact satisfy the predicate.
In other words, it is a form of dependent pair type.
Unlike both {name}`Subtype` and {name}`Sigma`, it is a {tech}[proposition]; this means that programs cannot in general use a proof of an existential statement to obtain a value that satisfies the predicate.

When writing a proof, the {tactic}`exists` tactic allows one (or more) witness(es) to be specified for a (potentially nested) existential statement.
The {tactic}`constructor` tactic, on the other hand, creates a {tech}[metavariable] for the witness; providing a proof of the predicate may solve the metavariable as well.
The components of an existential assumption can be made available individually by pattern matching with {tactic}`let` or {tactic show:="match"}`Lean.Parser.Tactic.match`, as well as by using {tactic}`cases` or {tactic}`rcases`.

:::example "Proving Existential Statements"

When proving that there exists some natural number that is the sum of four and five, the {tactic}`exists` tactic expects the sum to be provided, constructing the equality proof using {tactic}`trivial`:

```lean
theorem ex_four_plus_five : ∃ n, 4 + 5 = n := by
  exists 9
```

The {tactic}`constructor` tactic, on the other hand, expects a proof.
The {tactic}`rfl` tactic causes the sum to be determined as a side effect of checking definitional equality.

```lean
theorem ex_four_plus_five' : ∃ n, 4 + 5 = n := by
  constructor
  rfl
```


:::

{docstring Exists}

:::syntax term (title := "Existential Quantification")

```grammar
∃ $x:ident $[$_:ident]* $[: $t]?, $_
```
```grammar
exists $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
∃ $_ $[$_]*, $_
```

```grammar
exists $_ $[$_]*, $_
```

Existential quantifiers bind one or more variables, which are then in scope in the final term.
The identifiers may also be `_`.
With parenthesized type annotations, multiple bound variables may have different types, while the unparenthesized variant requires that all have the same type.
If more than one variable is bound, then the result is multiple instances of {name}`Exists`, nested to the right.
:::

{docstring Exists.choose}

# Propositional Equality
%%%
tag := "propositional-equality"
%%%

{deftech}_Propositional equality_ is the operator that allows the equality of two terms to be stated as a proposition.
{tech}[Definitional equality] is checked automatically where necessary.
As a result, its expressive power is limited in order to keep the algorithm that checks it fast and understandable.
Propositional equality, on the other hand, must be explicitly proved and explicitly used—Lean checks the validity of the proofs, rather than determining whether the statement is true.
In exchange, it is much more expressive: many terms are propositionally equal without being definitionally equal.

Propositional equality is defined as an inductive type.
Its sole constructor {name}`Eq.refl` requires that both of the equated values be the same; this is implicitly an appeal to {tech}[definitional equality].
Propositional equality can also be thought of as the least reflexive relation modulo definitional equality.
In addition to {name}`Eq.refl`, equality proofs are generated by the {name}`propext` and {name}`Quot.sound` axioms.


{docstring Eq}

:::syntax term (title := "Propositional Equality")
```grammar
$_ = $_
```
Propositional equality is typically denoted by the infix `=` operator.
:::

{docstring rfl}

{docstring Eq.symm}

{docstring Eq.trans}

{docstring Eq.subst}

{docstring cast}

{docstring congr}

{docstring congrFun}

{docstring congrArg}

{docstring Eq.mp}

{docstring Eq.mpr}

:::syntax term (title := "Casting")
```grammar
$_ ▸ $_
```
When a term's type includes one side of an equality as a sub-term, it can be rewritten using the `▸` operator.
If the both sides of the equality occur in the term's type, then the left side is rewritten to the right.
:::

## Uniqueness of Equality Proofs
%%%
tag := "UIP"
%%%

:::keepEnv

Because of definitional proof irrelevance, propositional equality proofs are _unique_: two mathematical objects cannot be equal in different ways.

```lean
theorem Eq.unique {α : Sort u}
    (x y : α)
    (p1 p2 : x = y) :
    p1 = p2 := by
  rfl
```

Streicher's axiom K{citep streicher1993}[] is also a consequence of definitional proof irrelevance, as is its computation rule.
Axiom K is a principle that's logically equivalent to {name}`Eq.unique`, implemented as an alternative {tech}[recursor] for propositional equality.
```lean
def K {α : Sort u}
    {motive : {x : α} → x = x → Sort v}
    (d : {x : α} → motive (Eq.refl x))
    (x : α) (z : x = x) :
    motive z :=
  d

example {α : Sort u} {a : α}
    {motive : {x : α} → x = x → Sort u}
    {d : {x : α} → motive (Eq.refl x)}
    {v : motive (Eq.refl a)} :
    K (motive := motive) d a rfl = d := by
  rfl
```

:::

## Heterogeneous Equality
%%%
tag := "HEq"
%%%

{deftech}_Heterogeneous equality_ is a version of {tech}[propositional equality] that does not require that the two equated terms have the same type.
However, _proving_ that the terms are equal using its version of {name}`rfl` requires that both the types and the terms are definitionally equal.
In other words, it allows more statements to be formulated.

Heterogeneous equality is typically less convenient in practice than ordinary propositional equality.
The greater flexibility afforded by not requiring both sides of the equality to have the same type means that it has fewer useful properties.
It is often encountered as a result of dependent pattern matching: the {tactic}`split` tactic and functional induction{TODO}[xref] add heterogeneous equality assumptions to the context when the ordinary equality assumptions that are needed to accurate reflect the corresponding control flow would not be type correct.
In these cases, the built-in automation has no choice but to use heterogeneous equality.


{docstring HEq}


{docstring HEq.rfl}


:::::leanSection
::::example "Heterogeneous Equality"
````lean (show := false)
variable {α : Type u} {n k l₁ l₂ l₃ : Nat}
````

The type {lean}`Vector α n` is wrapper around an {lean}`Array α` that includes a proof that the array has size {lean}`n`.
Appending {name}`Vector`s is associative, but this fact cannot be straightforwardly stated using ordinary propositional equality:
```lean
variable
  {xs : Vector α l₁} {ys : Vector α l₂} {zs : Vector α l₃}
set_option linter.unusedVariables false
```
```lean (name := assocFail) (error := true) (keep := false)
theorem Vector.append_associative :
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by sorry
```
The problem is that the associativity of addition of natural numbers holds propositionally, but not definitionally:
```leanOutput assocFail
type mismatch
  xs ++ ys ++ zs
has type
  Vector α (l₁ + l₂ + l₃) : outParam (Type u)
but is expected to have type
  Vector α (l₁ + (l₂ + l₃)) : outParam (Type u)
```

:::paragraph
One solution to this problem is to use the associativity of natural number addition in the statement:
```lean
theorem Vector.append_associative' :
    xs ++ (ys ++ zs) =
    Nat.add_assoc _ _ _ ▸ ((xs ++ ys) ++ zs) := by
  sorry
```
However, such proof statements can be difficult to work with in certain circumstances.
:::

:::paragraph
Another is to use heterogeneous equality:
```lean (keep := false)
theorem Vector.append_associative :
    HEq (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs) := by sorry
```
:::

In this case, {ref "the-simplifier"}[the simplifier] can rewrite both sides of the equation without having to preserve their types.
However, proving the theorem does require eventually proving that the lengths nonetheless match.
```lean (keep := false)
theorem Vector.append_associative :
    HEq (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs) := by
  cases xs; cases ys; cases zs
  simp
  congr 1
  . omega
  . apply heq_of_eqRec_eq
    . rfl
    . apply propext
      constructor <;> intro h <;> simp_all +arith
```
::::
:::::

{docstring HEq.elim}

{docstring HEq.ndrec}

{docstring HEq.ndrecOn}

{docstring HEq.subst}

{docstring eq_of_heq}

{docstring heq_of_eq}

{docstring heq_of_eqRec_eq}

{docstring eqRec_heq}

{docstring cast_heq}

{docstring heq_of_heq_of_eq}

{docstring type_eq_of_heq}
