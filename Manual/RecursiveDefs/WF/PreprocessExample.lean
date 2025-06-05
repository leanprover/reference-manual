/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta

/-!
This is extracted into its own file because line numbers show up in the error message, and we don't
want to update it over and over again as we edit the large file.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

#doc (Manual) "Well-founded recursion preprocessing example (for inclusion elsewhere)" =>

::::example "Preprocessing for a custom data type"

This example demonstrates what is necessary to enable automatic well-founded recursion for a custom container type.
The structure type {name}`Pair` is a homogeneous pair: it contains precisely two elements, both of which have the same type.
It can be thought of as being similar to a list or array that always contains precisely two elements.

As a container, {name}`Pair` can support a {name Pair.map}`map` operation.
To support well-founded recursion in which recursive calls occur in the body of a function being mapped over a {name}`Pair`, some additional definitions are required, including a membership predicate, a theorem that relates the size of a member to the size of the containing pair, helpers to introduce and eliminate assumptions about membership, {attr}`wf_preprocess` rules to insert these helpers, and an extension to the {tactic}`decreasing_trivial` tactic.
Each of these steps makes it easier to work with {name}`Pair`, but none are strictly necessary; there's no need to immediately implement all steps for every type.

```lean
/-- A homogeneous pair -/
structure Pair (α : Type u) where
  fst : α
  snd : α

/-- Mapping a function over the elements of a pair -/
def Pair.map (f : α → β) (p : Pair α) : Pair β where
  fst := f p.fst
  snd := f p.snd
```

Defining a nested inductive data type of binary trees that uses {name}`Pair` and attempting to define its {name Tree.map}`map` function demonstrates the need for preprocessing rules.

```lean
/-- A binary tree defined using `Pair` -/
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | node : Pair (Tree α) → Tree α
```

A straightforward definition of the {name Tree.map}`map` function fails:

```lean (error := true) (keep := false) (name := badwf)
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
```

```leanOutput badwf (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
p : Pair (Tree α)
t' : Tree α
⊢ sizeOf t' < 1 + sizeOf p
```

:::paragraph
```lean (show := false)
section
variable (t' : Tree α) (p : Pair (Tree α))
```
Clearly the proof obligation is not solvable, because nothing connects {lean}`t'` to {lean}`p`.
```lean (show := false)
end
```
:::

The standard idiom to enable this kind of function definition is to have a function that enriches each element of a collection with a proof that they are, in fact, elements of the collection.
Stating this property requires a membership predicate.

```lean
inductive Pair.Mem (p : Pair α) : α → Prop where
  | fst : Mem p p.fst
  | snd : Mem p p.snd

instance : Membership α (Pair α) where
  mem := Pair.Mem
```

Every inductive type automatically has a {name}`SizeOf` instance.
An element of a collection should be smaller than the collection, but this fact must be proved before it can be used to construct a termination proof:

```lean
theorem Pair.sizeOf_lt_of_mem {α} [SizeOf α]
    {p : Pair α} {x : α} (h : x ∈ p) :
    sizeOf x < sizeOf p := by
  cases h <;> cases p <;> (simp; omega)
```

The next step is to define {name Pair.attach}`attach` and {name Pair.unattach}`unattach` functions that enrich the elements of the pair with a proof that they are elements of the pair, or remove said proof.
Here, the type of {name}`Pair.unattach` is more general and can be used with any {ref "Subtype"}[subtype]; this is a typical pattern.

```lean
def Pair.attach (p : Pair α) : Pair {x : α // x ∈ p} where
  fst := ⟨p.fst, .fst⟩
  snd := ⟨p.snd, .snd⟩

def Pair.unattach {P : α → Prop} :
    Pair {x : α // P x} → Pair α :=
  Pair.map Subtype.val
```

{name Tree.map}`Tree.map` can now be defined by using {name}`Pair.attach` and {name}`Pair.sizeOf_lt_of_mem` explicitly:

```lean (keep := false)
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.attach.map (fun ⟨t', _⟩ => t'.map f))
termination_by t => t
decreasing_by
  have := Pair.sizeOf_lt_of_mem ‹_›
  simp_all +arith
  omega
```

This transformation can be made fully automatic.
The preprocessing feature of well-founded recursion can be used to automate the introduction of the {lean}`Pair.attach` function.
This is done in two stages.
First, when {name}`Pair.map` is applied to one of the function's parameters, it is rewritten to an {name Pair.attach}`attach`/{name Pair.unattach}`unattach` composition.
Then, when a function is mapped over the result of {name}`Pair.unattach`, the function is rewritten to accept the proof of membership and bring it into scope.
```lean
@[wf_preprocess]
theorem Pair.map_wfParam (f : α → β) (p : Pair α) :
    (wfParam p).map f = p.attach.unattach.map f := by
  cases p
  simp [wfParam, Pair.attach, Pair.unattach, Pair.map]

@[wf_preprocess]
theorem Pair.map_unattach {P : α → Prop}
    (p : Pair (Subtype P)) (f : α → β) :
    p.unattach.map f =
    p.map fun ⟨x, h⟩ =>
      binderNameHint x f <|
      f (wfParam x) := by
  cases p; simp [wfParam, Pair.unattach, Pair.map]
```

Now the function body can be written without extra considerations, and the membership assumption is still available to the termination proof.

```lean (keep := false)
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
decreasing_by
  have := Pair.sizeOf_lt_of_mem ‹_›
  simp_all
  omega
```

The proof can be made fully automatic by adding {name Pair.sizeOf_lt_of_mem}`sizeOf_lt_of_mem` to the {tactic}`decreasing_trivial` tactic, as is done for similar built-in theorems.

```lean
macro "sizeOf_pair_dec" : tactic =>
  `(tactic| with_reducible
    have := Pair.sizeOf_lt_of_mem ‹_›
    omega
    done)

macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| sizeOf_pair_dec)

def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
```

To keep the example short, the {tactic}`sizeOf_pair_dec` tactic is tailored to this particular recursion pattern and isn't really general enough for a general-purpose container library.
It does, however, demonstrate that libraries can be just as convenient in practice as the container types in the standard library.

::::
