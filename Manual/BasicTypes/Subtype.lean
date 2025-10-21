/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "Subtypes" =>
%%%
tag := "Subtype"
%%%

The structure {name}`Subtype` represents the elements of a type that satisfy some predicate.
They are used pervasively both in mathematics and in programming; in mathematics, they are used similarly to subsets, while in programming, they allow information that is known about a value to be represented in a way that is visible to Lean's logic.

Syntactically, an element of a {name}`Subtype` resembles a tuple of the base type's element and the proof that it satisfies the proposition.
They differ from dependent pair types ({name}`Sigma`) in that the second element is a proof of a proposition rather than data, and from existential quantification in that the entire {name}`Subtype` is a type rather than a proposition.
Even though they are pairs syntactically, {name}`Subtype` should really be thought of as elements of the base type with associated proof obligations.

Subtypes are {ref "inductive-types-trivial-wrappers"}[trivial wrappers].
They are thus represented identically to the base type in compiled code.


{docstring Subtype}

::::leanSection
```lean -show
variable {α : Type u} {p : Prop}
```
:::syntax term (title := "Subtypes")
```grammar
{ $x : $t:term // $t:term }
```

{lean}`{ x : α // p }` is a notation for {lean}`Subtype fun (x : α) => p`.

The type ascription may be omitted:

```grammar
{ $x:ident // $t:term }
```

{lean}`{ x // p }` is a notation for {lean}`Subtype fun (x : _) => p`.
:::
::::

Due to {tech}[proof irrelevance] and {tech (key := "η-equivalence")}[η-equality], two elements of a subtype are definitionally equal when the elements of the base type are definitionally equal.
In a proof, the {tactic}`ext` tactic can be used to transform a goal of equality of elements of a subtype into equality of their values.

:::example "Definitional Equality of Subtypes"

The non-empty strings {lean}`s1` and {lean}`s2` are definitionally equal despite the fact that their embedded proof terms are different.
No case splitting is needed in order to prove that they are equal.

```lean
def NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property :=
    fun h =>
      List.cons_ne_nil _ _ (String.data_eq_of_eq h)

theorem s1_eq_s2 : s1 = s2 := by rfl
```
:::

:::example "Extensional Equality of Subtypes"

The non-empty strings {lean}`s1` and {lean}`s2` are definitionally equal.
Ignoring that fact, the equality of the embedded strings can be used to prove that they are equal.
The {tactic}`ext` tactic transforms a goal that consists of equality of non-empty strings into a goal that consists of equality of the strings.

```lean
abbrev NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property :=
    fun h =>
      List.cons_ne_nil _ _ (String.data_eq_of_eq h)

theorem s1_eq_s2 : s1 = s2 := by
  ext
  dsimp only [s1, s2]
  rfl
```
:::

There is a coercion from a subtype to its base type.
This allows subtypes to be used in positions where the base type is expected, essentially erasing the proof that the value satisfies the predicate.

:::example "Subtype Coercions"

Elements of subtypes can be coerced to their base type.
Here, {name}`nine` is coerced from a subtype of `Nat` that contains multiples of {lean  (type := "Nat")}`3` to {lean}`Nat`.

```lean (name := subtype_coe)
abbrev DivBy3 := { x : Nat // x % 3 = 0 }

def nine : DivBy3 := ⟨9, by rfl⟩

set_option eval.type true in
#eval Nat.succ nine
```
```leanOutput subtype_coe
10 : Nat
```

:::
