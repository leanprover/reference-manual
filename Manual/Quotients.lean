/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.Language.Functions
import Manual.Language.InductiveTypes

open Verso.Genre Manual

#doc (Manual) "Quotients" =>
%%%
tag := "quotients"
%%%


{deftech}_Quotient types_ allow a new type to be formed by decreasing the granularity of an existing type's propositional equality.
In particular, given an type $`A` and an equivalence relation $`\sim`, the quotient $`A / \sim` contains the same elements as $`A`, but every pair of elements that are related by $`\sim` are considered equal.
Equality is respected universally; nothing in Lean's logic can observe any difference between two equal terms.
Thus, quotient types provide a way to build an impenetrable abstraction barrier.
In particular, all functions from a quotient type must prove that they respect the equivalence relation.

{docstring Quotient}

:::paragraph
Quotient types are not widely used in programming.
However, they occur regularly in mathematics:

: Integers

  The integers are traditionally defined as a pair of natural numbers $`(n, k)` that encodes the integer $`n - k`.
  In this encoding, two integers $`(n_1, k_1)` and $`(n_2, k_2)` are equal if $`n_1 + k_2 = n_2 + k_1`.

: Rational Numbers

  The number $`\frac{n}{d}` can be encoded as the pair $`(n, d)`, where $`d \neq 0`.
  Two rational numbers $`\frac{n_1}{d_1}` and $`\frac{n_2}{d_2}` are equal if $`n_1 d_2 = n_2 d_1`.

: Real Numbers

  The real numbers can be represented as a Cauchy sequence, but this encoding is not unique.
  Using a quotient type, two Cauchy sequences can be made equal when their difference converges to zero.

: Finite Sets

  Finite sets can be represented as lists of elements.
  With a quotient types, two finite sets can be made equal if they contain the same elements; this definition does not impose any requirements (such as decidable equality or an ordering relation) on the type of elements.

:::

One alternative to quotient types would be to reason directly about the equivalence classes introduced by the relation.
The downside of this approach is that it does not allow _computation_: in addition to knowing _that_ there is an integer that is the sum of 5 and 8, it is useful for $`5 + 8 = 13` to not be a theorem that requires proof.
Defining functions out of sets of equivalence classes relies on non-computational classical reasoning principles, while functions from quotient types are ordinary computational functions that additionally respect an equivalence relation.

# Alternatives to Quotient Types
%%%
tag := "quotient-alternatives"
%%%


Quotient types are not the only way to implement quotients.
An alternative is to select a canonical representative for each equivalence class induced by the equivalence relation, and then pair an element of the underlying type with a proof that it is such a canonical representative.
These manually constructed quotients are often much easier to work with than full quotient types, but not all quotients can be implemented this way.

:::example "Manually Quotiented Integers"
When implemented as pairs of {lean}`Nat`s, each equivalence class according to the desired equality for integers has a canonical representative in which at least one of the {lean}`Nat`s is zero.
This can be represented as a Lean structure:
```lean
structure Z where
  a : Nat
  b : Nat
  canonical : a = 0 ∨ b = 0
```
Due to {tech}[proof irrelevance], every value of this structure type that represents the same integer is _already_ equal.
Constructing a {lean}`Z` can be made more convenient with a wrapper that uses the fact that subtraction of natural numbers truncates at zero to automate the construction of the proof:
```lean
def Z.mk' (n k : Nat) : Z where
  a := n - k
  b := k - n
  canonical := by omega
```

This construction respects the equality demanded of integers:
```lean
theorem Z_mk'_respects_eq :
    (Z.mk' n k = Z.mk' n' k') ↔ (n + k' = n' + k) := by
  simp [Z.mk']
  omega
```

To use this type in examples, it's convenient to have {name}`Neg`, {name}`OfNat`, and {name}`ToString` instances.
These instances make it easier to read or write examples.

```lean
instance : Neg Z where
  neg n := Z.mk' n.b n.a

instance : OfNat Z n where
  ofNat := Z.mk' n 0

instance : ToString Z where
  toString n :=
    if n.a = 0 then
      if n.b = 0 then "0"
      else s!"-{n.b}"
    else toString n.a
```
```lean (name := intFive)
#eval (5 : Z)
```
```leanOutput intFive
5
```
```lean (name := intMinusFive)
#eval (-5 : Z)
```
```leanOutput intMinusFive
-5
```


Addition is addition of the underlying {lean}`Nat`s:
```lean
instance : Add Z where
  add n k := Z.mk' (n.a + k.a) (n.b + k.b)
```

```lean (name := addInt)
#eval (-5 + 22: Z)
```
```leanOutput addInt
17
```

Because each equivalence class is uniquely represented, there's no need to write a proof that these functions from {lean}`Z` respect the equivalence relation.

:::


# Setoids
%%%
tag := "setoids"
%%%

Quotient types are built on setoids.
A {deftech}_setoid_ is a type paired with a distinguished equivalence relation.
Unlike a quotient type, the abstraction barrier is not enforced, and proof automation designed around equality cannot be used with the setoid's equivalence relation.
Setoids are useful on their own, in addition to being a building block for quotient types.

{docstring Setoid}

# Equivalence Relations
%%%
tag := "equivalence-relations"
%%%

An {deftech}_equivalence relation_ is a relation that is reflexive, symmetric, and transitive.

:::syntax term (title := "Equivalence Relations")
Equivalence according to some canonical equivalence relation for a type is written using `≈`, which is overloaded using the {tech}[type class] {name}`HasEquiv`.
```grammar
$_ ≈ $_
```
:::

{docstring HasEquiv}

```lean (show := false)
section
variable (r : α → α → Prop)
```

The fact that a relation {lean}`r` is actually an equivalence relation is stated {lean}`Equivalence r`.

{docstring Equivalence}

```lean (show := false)
end
```

Every {name}`Setoid` instance leads to a corresponding {name}`HasEquiv` instance.

```lean (show := false)
-- Check preceding para
section
variable {α : Sort u} [Setoid α]
/-- info: instHasEquivOfSetoid -/
#guard_msgs in
#synth HasEquiv α
end
```

# Quotient API
%%%
tag := "quotient-api"
%%%

The quotient API relies on a pre-existing {name}`Setoid` instance.

## Introducing Quotients
%%%
tag := "quotient-intro"
%%%


The type {lean}`Quotient` expects an instance of {lean}`Setoid` as an ordinary parameter, rather than as an {tech}[instance implicit] parameter.
This helps ensure that the quotient uses the intended equivalence relation.
The instance can be provided either by naming the instance or by using {name}`inferInstance`.

A value in the quotient is a value from the setoid's underlying type, wrapped in {lean}`Quotient.mk`.

{docstring Quotient.mk}

{docstring Quotient.mk'}

:::example "The Integers as a Quotient Type"
The integers, defined as pairs of natural numbers where the represented integer is the difference of the two numbers, can be represented via a quotient type.
This representation is not unique: both {lean}`(4, 7)` and {lean}`(1, 4)` represent {lean type:="Int"}`-3`.

Two encoded integers should be considered equal when they are related by {name}`Z.eq`:

```lean
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1
```

This relation is an equivalence relation:
```lean
def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp_arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega
```

Thus, it can be used as a {name}`Setoid`:
```lean
instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv
```

The type {lean}`Z` of integers is then the quotient of {lean}`Z'` by the {name}`Setoid` instance:

```lean
def Z : Type := Quotient Z.instSetoid
```

The helper {lean}`Z.mk` makes it simpler to create integers without worrying about the choice of {name}`Setoid` instance:
```lean
def Z.mk (n : Z') : Z := Quotient.mk _ n
```

However, numeric literals are even more convenient.
An {name}`OfNat` instance allows numeric literals to be used for integers:
```lean
instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```
:::



## Eliminating Quotients
%%%
tag := "quotient-elim"
%%%


Functions from quotients can be defined by proving that a function from the underlying type respects the quotient's equivalence relation.
This is accomplished using {lean}`Quotient.lift` or its binary counterpart {lean}`Quotient.lift₂`.
The variants {lean}`Quotient.liftOn` and {lean}`Quotient.liftOn₂` place the quotient parameter first rather than last in the parameter list.

{docstring Quotient.lift}

{docstring Quotient.liftOn}

{docstring Quotient.lift₂}

{docstring Quotient.liftOn₂}

:::example "Integer Negation and Addition"

```lean (show := false)
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp_arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n
```

Given the encoding {lean}`Z` of integers as a quotient of pairs of natural numbers, negation can be implemented by swapping the first and second projections:
```lean
def neg' : Z' → Z
  | (x, y) => .mk (y, x)
```

This can be transformed into a function from {lean}`Z` to {lean}`Z` by proving that negation respects the equivalence relation:
```lean
instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, Setoid.r, Z.eq] at *
      omega
```

Similarly, {lean}`Quotient.lift₂` is useful for defining binary functions from a quotient type.
Addition is defined point-wise:
```lean
def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)
```

Lifting it to the quotient requires a proof that addition respects the equivalence relation:
```lean
instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, Setoid.r, Z.eq]
      omega
```
:::

## Proofs About Quotients
%%%
tag := "quotient-proofs"
%%%


The fundamental tools for proving properties of elements of quotient types are the soundness axiom and the induction principle.
The soundness axiom states that if two elements of the underlying type are related by the quotient's equivalence relation, then they are equal in the quotient type.
The induction principle follows the structure of recursors for inductive types: in order to prove that a predicate holds all elements of a quotient type, it suffices to prove that it holds for an application of {name}`Quotient.mk` to each element of the underlying type.
Because {name}`Quotient` is not an {tech}[inductive type], tactics such as {tactic}`cases` and {tactic}`induction` require that {name}`Quotient.ind` be specified explicitly with the {keyword}`using` modifier.

{docstring Quotient.sound}

{docstring Quotient.ind}

:::example "Proofs About Quotients"

```lean (show := false)
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp_arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n

def neg' : Z' → Z
  | (x, y) => .mk (y, x)

instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, Setoid.r, Z.eq] at *
      omega

def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)

instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, Setoid.r, Z.eq]
      omega

instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```

Given the definition of integers as a quotient type from the prior examples, {name}`Quotient.ind` and {name}`Quotient.sound` can be used to prove that negation is an additive inverse.
First, {lean}`Quotient.ind` is used to replace instances of `n` with applications of {name}`Quotient.mk`.
Having done so, the left side of the equality becomes definitionally equal to a single application of {name}`Quotient.mk`, via unfolding definitions and the computation rule for {name}`Quotient.lift`.
This makes {name}`Quotient.sound` applicable, which yields a new goal: to show that both sides are related by the equivalence relation.
This is provable using {tactic}`simp_arith`.

```lean
theorem Z.add_neg_inverse (n : Z) : n  + (-n) = 0 := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp_arith [· ≈ ·, Setoid.r, eq]
```

:::

# Logical Model
%%%
tag := "quotient-model"
%%%


Like functions and universes, quotient types are a built-in feature of Lean's type system.
However, the underlying primitives are based on the somewhat simpler {name}`Quot` type rather than on {name}`Quotient`, and {name}`Quotient` is defined in terms of {name}`Quot`.
The primary difference is that {name}`Quot` is based on an arbitrary relation, rather than a {name}`Setoid` instance.
The provided relation need not be an equivalence relation; the rules that govern {name}`Quot` and {name}`Eq` automatically extend the provided relation into its reflexive, transitive, symmetric closure.
When the relation is already an equivalence relation, {name}`Quotient` should be used instead of {name}`Quot` so Lean can make use of the fact that the relation is an equivalence relation.

The fundamental quotient type API consists of {lean}`Quot`, {name}`Quot.mk`, {name}`Quot.lift`, {name}`Quot.ind`, and {name}`Quot.sound`.
These are used in the same way as their {name}`Quotient`-based counterparts.

{docstring Quot}

{docstring Quot.mk}

{docstring Quot.lift}

{docstring Quot.ind}

{docstring Quot.sound}

```lean (show := false)
section
variable
  (α β : Sort u)
  (r : α → α → Prop)
  (f : α → β)
  (resp : ∀ x y, r x y → f x = f y)
  (x : α)
```
In addition to the above constants, Lean's kernel contains a reduction rule for {name}`Quot.lift` that causes it to reduce when used with {name}`Quot.mk`, analogous to {tech}[ι-reduction] for inductive types.
Given a relation {lean}`r` over {lean}`α`, a function {lean}`f` from {lean}`α` to {lean}`β`, and a proof {lean}`resp` that {lean}`f` respects {lean}`r`, the term {lean}`Quot.lift f resp (Quot.mk r x)` is {tech key:="definitional equality"}[definitionally equal] to {lean}`f x`.

```lean (show := false)
end
```

```lean (show := false)
section
```

```lean
variable
  (r : α → α → Prop)
  (f : α → β)
  (ok : ∀ x y, r x y → f x = f y)
  (x : α)

example : Quot.lift f ok (Quot.mk r x) = f x := rfl
```

```lean (show := false)
end
```

Because {name}`Quot` is not an inductive type, types implemented as quotients may not occur around {ref "nested-inductive-types"}[nested occurrences] in inductive type declarations.
These types declarations must be rewritten to remove the nested quotient, which can often be done by defining a quotient-free version and then separately defining an equivalence relation that implements the desired equality relation.

:::example "Nested Inductive Types and Quotients"

The nested inductive type of rose trees nests the recursive occurrence of {lean}`RoseTree` under {lean}`List`:
```lean
inductive RoseTree (α : Type u) where
  | leaf : α → RoseTree α
  | branch : List (RoseTree α) → RoseTree α
```

However, taking a quotient of the {name}`List` that identifies all elements in the style of {ref "squash-types"}[squash types] causes Lean to reject the declaration:
```lean (error := true) (name := nestedquot)
inductive SetTree (α : Type u) where
  | leaf : α → SetTree α
  | branch :
    Quot (fun (xs ys : List (SetTree α)) => True) →
    SetTree α
```
```leanOutput nestedquot
(kernel) arg #2 of 'SetTree.branch' contains a non valid occurrence of the datatypes being declared
```

:::


# Quotients and Function Extensionality
%%%
tag := "quotient-funext"
%%%

:::::keepEnv

Because Lean's definitional equality includes a computational reduction rule for {lean}`Quot.lift`, quotient types are used in the standard library to prove function extensionality, which would need to be an {ref "axioms"}[axiom] otherwise.
This is done by first defining a type of functions quotiented by extensional equality, for which extensional equality holds by definition.

```lean
variable {α : Sort u} {β : α → Sort v}

def extEq (f g : (x : α) → β x) : Prop :=
  ∀ x, f x = g x

def ExtFun (α : Sort u) (β : α → Sort v) :=
  Quot (@extEq α β)
```

Extensional functions can be applied just like ordinary functions.
Application respects extensional equality by definition: if applying to functions gives equal results, then applying them gives equal results.
```lean
def extApp
    (f : ExtFun α β)
    (x : α) :
    β x :=
  f.lift (· x) fun g g' h => by
    exact h x
```

```lean (show := false)
section
variable (f : (x : α) → β x)
```
To show that two functions that are extensionally equal are in fact equal, it suffices to show that the functions that result from extensionally applying the corresponding extensional functions are equal.
This is because
```leanTerm
extApp (Quot.mk _ f)
```
is definitionally equal to
```leanTerm
fun x => (Quot.mk extEq f).lift (· x) (fun _ _ h => h x)
```
which is definitionally equal to {lean}`fun x => f x`, which is definitionally equal (by {tech}[η-equivalence]) to {lean}`f`.

```lean (show := false)
end
```

From here, it is enough to show that the extensional versions of the two functions are equal.
This is true due to {name}`Quot.sound`: the fact that they are in the quotient's equivalence relation is an assumption.
This proof is a much more explicit version of the one in the standard library:

```lean
theorem funext'
    {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) :
    f = g := by
  suffices extApp (Quot.mk _ f) = extApp (Quot.mk _ g) by
    unfold extApp at this
    dsimp at this
    exact this
  suffices Quot.mk extEq f = Quot.mk extEq g by
    apply congrArg
    exact this
  apply Quot.sound
  exact h
```

:::::

# Squash Types
%%%
tag := "squash-types"
%%%

```lean (show := false)
section
variable {α : Sort u}
```
Squash types are a quotient by the relation that relates all elements, transforming it into a {tech}[subsingleton].
In other words, if {lean}`α` is inhabited, then {lean}`Squash α` has a single element, and if {lean}`α` is uninhabited, then {lean}`Squash α` is also uninhabited.
Unlike {lean}`Nonempty α`, which is a proposition stating that {lean}`α` is inhabited and is thus represented by a dummy value at runtime, {lean}`Squash α` is a type that is represented identically to {lean}`α`.
Because {lean}`Squash α` is in the same universe as {lean}`α`, it is not subject to the restrictions on computing data from propositions.

```lean (show := false)
end
```

{docstring Squash}

{docstring Squash.mk}

{docstring Squash.lift}
