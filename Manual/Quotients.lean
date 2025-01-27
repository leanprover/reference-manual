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

:::planned 51
 * Define {deftech}[quotient] type
 * Show the computation rule
:::


{deftech}_Quotient types_ allow a new type to be formed by decreasing the granularity of an existing type's propositional equality.
In particular, given an type $`A` and an equivalence relation $`\sim`, the quotient $`A / \sim` contains the same elements as $`A`, but every pair of elements that are related by $`\sim` are considered equal.
Equality is respected universally; nothing in Lean's logic can observe any difference between two equal terms.
Thus, quotient types provide a way to build an impenetrable abstraction barrier.
In particular, all functions from a quotient type must prove that they respect the equivalence relation.

{docstring Quotient}

:::paragraph
Quotients are widely used in mathematics:

: Integers

  The integers are traditionally defined as a pair of natural numbers $`(n, k)` that encodes the integer $`n - k`.
  In this encoding, two integers $`(n_1, k_1)` and $`(n_2, k_2)` are equal if $`n_1 + k_2 = n_2 + k_1`.

: Rational Numbers

  The number $`\frac{n}{d}` can be encoded as the pair $`(n, d)`, where $`d \neq 0`.
  Two rational numbers $`\frac{n_1}{d_1}` and $`\frac{n_2}{d_2}` are equal if $`n_1 d_2 = n_2 d_1`.

: Real Numbers

  The real numbers can be represented as a Cauchy sequence, but this encoding is not unique.
  Using a quotient type, two Cauchy sequences can be made equal when their difference converges to zero.

:::

:::TODO

Ask colleagues for a couple more good examples here

:::

Quotient types are not widely used in programming.


# Setoids

Quotient types are built on setoids.
A {deftech}_setoid_ is a type paired with a distinguished equivalence relation.
Unlike a quotient type, the abstraction barrier is not enforced, and proof automation designed around equality cannot be used with the setoid's equivalence relation.
Setoids are primarily used as a building block for quotient types.

{docstring Setoid}

# Equivalence Relations

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

# Quotient API

## Introducing Quotients

The type {lean}`Quotient` expects an instance of {lean}`Setoid` as its explicit parameter.
A value in the quotient is a value from the setoid's underlying type, wrapped in {lean}`Quotient.mk`.

{docstring Quotient.mk}

{docstring Quotient.mk'}

:::example "The Integers"
The integers can be defined as pairs of natural numbers where the represented integer is the difference of the two numbers.
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
instance Z.instSetoid : Setoid Z'where
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
  ofNat := .mk _ (n, 0)
```
:::



## Eliminating Quotients

Functions from quotients can be defined based on functions from the underlying type by proving that the function respects the quotient's equivalence relation.
This is accomplished using {lean}`Quotient.lift`.

{docstring Quotient.lift}

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
      simp only [instHasEquivOfSetoid, Setoid.r, Z.eq] at *
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
      simp only [instHasEquivOfSetoid, Setoid.r, Z.eq] at *
      cases n; cases k; cases n'; cases k'
      simp_all
      omega
```
:::

## Proofs About Quotients

The fundamental tools for proving properties of elements of quotient types are

{docstring Quotient.sound}

{docstring Quotient.ind}

# Logical Model

Like functions and universes, quotient types are a built-in feature of Lean.
The fundamental quotient type API consists of {lean}`Quot`, {name}`Quot.mk`, {name}`Quot.lift`, {name}`Quot.ind`, and {name}`Quot.sound`.
The first four are constants, while {name}`Quot.sound` is an axiom.

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

```lean
variable
  (r : α → α → Prop)
  (f : α → β)
  (ok : ∀ x y, r x y → f x = f y)
  (x : α)

example : Quot.lift f ok (Quot.mk r x) = f x := rfl
```

# Squash Types

{docstring Squash}

{docstring Squash.mk}

{docstring Squash.lift}
