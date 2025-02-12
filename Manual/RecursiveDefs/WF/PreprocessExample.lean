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
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Well-founded recursion preprocessing example (for inclusion elsewhere)" =>

:::example "Preprocessing for a custom data type"

In this example, we define a new container-like data type (for homogeneous pairs), with a membership predicate, a map function and the necessary setup to allow well-founded recursion through that map function.

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

To demonstrate the problem, we define a nested inductive data type for binary trees, and try to define a map function for it.

```lean
/-- A binary tree defined using `Pair` -/
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | node : Pair (Tree α) → Tree α
```

Our definition of the map function fails:

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

```lean (show := false)
section
variable (t' : Tree α) (p : Pair (Tree α))
```
Clearly the proof obligation is not solvable, as nothing connects `t'` to `p`. {TODO}[Cannot use `lean` here? Because this is in an example?]
```lean (show := false)
end
```

The idiom to allow this function definition is to have a function that enriches the elements of the pair with the assertion that the elements are in the pair.
For that we need a membership predicate.

```lean
inductive Pair.Mem (p : Pair α) : α → Prop where
| fst : Mem p p.fst
| snd : Mem p p.snd

instance : Membership α (Pair α) where
  mem := Pair.Mem

theorem Pair.size_lt_of_mem {α} [SizeOf α]
    {p : Pair α} {x : α} (h : x ∈ p) :
    sizeOf x < sizeOf p := by
  cases h <;> cases p <;> (simp; omega)
```

Furthermore we introduce `attach` and `unattach` functions that enrich the elements of the pair with the assertion that they are in the pair, respectively remove that assertion.

```lean
def Pair.attach (p : Pair α) : Pair {x : α // x ∈ p} where
  fst := ⟨p.fst, .fst⟩
  snd := ⟨p.snd, .snd⟩

def Pair.unattach {P : α → Prop} :
    Pair {x : α // P x} → Pair α :=
  Pair.map Subtype.val
```

This already allows us to define the `map` function by using `Pair.attach` explicitly:

```lean (keep := false)
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.attach.map (fun ⟨t', _⟩ => t'.map f))
termination_by t => t
decreasing_by have := Pair.size_lt_of_mem ‹_›; simp_all; omega
```

We can use the preprocessing feature of well-founded recursion to automate the introduction of the {lean}`Pair.attach` function:

```lean
@[wf_preprocess]
theorem Pair.map_wfParam (f : α → β) (p : Pair α) :
    (wfParam p).map f = p.attach.unattach.map f := by
  cases p
  simp [wfParam, Pair.attach, Pair.unattach, Pair.map]

@[wf_preprocess]
theorem Pair.map_unattach {P : α → Prop}
    (p : Pair (Subtype P)) (f : α → β) :
    p.unattach.map f = p.map fun ⟨x, h⟩ => f (wfParam x) := by
  cases p; simp [wfParam, Pair.unattach, Pair.map]
```

Now the function body can be written without extra considerations, and the membership assumption is still available to the termination proof.

```lean
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
decreasing_by have := Pair.size_lt_of_mem ‹_›; simp_all; omega
```


:::
