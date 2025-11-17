/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean hiding module
open Verso.Doc.Elab (CodeBlockExpander)
open Verso.Code.External

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


open Lean.Grind

set_option maxHeartbeats 1000000 -- Needed for elaboration of the `IndexMap` example.
set_option maxRecDepth 20000 -- Needed for compilation of the `IndexMap` example.

set_option pp.rawOnError true

set_option verso.exampleProject "."
set_option verso.exampleModule "IndexMapGrind"


#doc (Manual) "`IndexMap`" =>


In this section we'll build an example of a new data structure and basic API for it, illustrating the use of {tactic}`grind`.
The example will be derived from Rust's [`indexmap`](https://docs.rs/indexmap/latest/indexmap/) data structure.

{anchorName IndexMap}`IndexMap` is intended as a replacement for {name Std.HashMap}`HashMap` (in particular, it has fast hash-based lookup), but allowing the user to maintain control of the order of the elements.
We won't give a complete API, just set up some basic functions and theorems about them.

The two main functions we'll implement for now are {anchorName insert}`insert` and {anchorName eraseSwap}`eraseSwap`:
* `insert k v` checks if `k` is already in the map. If so, it replaces the value with `v`, keeping `k` in the same position in the ordering.
  If it is not already in the map, `insert` adds `(k, v)` to the end of the map.
* `eraseSwap k` removes the element with key `k` from the map, and swaps it with the last element of the map (or does nothing if `k` is not in the map).
  (This behavior may be surprising: this function exists because it is an efficient way to an erase element when you don't care about the order of the remaining elements.
  Another function, not implemented here, would preserve the order of the remaining elements, but at the cost of running in time proportional to the number of elements after the erased element.)

Our goals will be:

: Complete encapsulation

  The implementation of {anchorName IndexMap}`IndexMap` is hidden from the users, *and* the theorems about the implementation details are private.

: Use {tactic}`grind` as much as possible

  We'll prefer adding a private theorem and annotating it with {attrs}`@[grind]` over writing a longer proof whenever practical.

: Use auto-parameters as much as possible

  Ideally, we don't even need to see the proofs; they should mostly be handled invisibly by {tactic}`grind`.

To begin with, we'll write out a skeleton of what we want to achieve, liberally using {lean}`sorry` as a placeholder for all proofs.
In particular, this version makes no use of {tactic}`grind`.

```module (module := IndexMap)
import Std.Data.HashMap

open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  indices : HashMap α Nat
  keys : Array α
  values : Array β
  size_keys : keys.size = values.size
  WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i

namespace IndexMap

variable {α : Type u} {β : Type v}
  [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity
  size_keys := sorry
  WF := sorry

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

instance :
    GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]'(by sorry)
  getElem? m a :=
    m.indices[a]?.bind (m.values[·]?)
  getElem! m a :=
    m.indices[a]?.bind (m.values[·]?) |>.getD default

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := sorry
  getElem!_def := sorry

@[inline] def insert (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a sorry
      values := m.values.set i b sorry
      size_keys := sorry
      WF := sorry }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b
      size_keys := sorry
      WF := sorry }

instance : Singleton (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) :=
  ⟨fun _ => rfl⟩

/--
Erase the key-value pair with the given key,
moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop
        size_keys := sorry
        WF := sorry }
    else
      let lastKey := m.keys.back sorry
      let lastValue := m.values.back sorry
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey sorry
        values := m.values.pop.set i lastValue sorry
        size_keys := sorry
        WF := sorry }
  | none => m

/-! ### Verification theorems -/

theorem getIdx_findIdx (m : IndexMap α β) (a : α)
    (h : a ∈ m) :
    m.getIdx (m.findIdx a h) sorry = m[a] :=
  sorry

theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  sorry

theorem getElem_insert
    (m : IndexMap α β) (a a' : α) (b : β)
    (h : a' ∈ m.insert a b) :
    (m.insert a b)[a']'h =
      if h' : a' == a then b else m[a']'sorry := by
  sorry

theorem findIdx_insert_self
    (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a sorry =
      if h : a ∈ m then m.findIdx a h else m.size := by
  sorry

end IndexMap
```


Let's get started.
We'll aspire to never writing a proof by hand, and the first step of that is to install auto-parameters for the `size_keys` and `WF` field,
so we can omit these fields whenever `grind` can prove them.
While we're modifying the definition of `IndexMap` itself, lets make all the fields private, since we're planning on having complete encapsulation.

```anchor IndexMap
structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind
```

Let's give {tactic}`grind` access to the definition of `size`, and `size_keys` private field:
```anchor size
@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size :=
  m.size_keys'
```

:::paragraph
Our first {lean}`sorry`s in the draft version are the {anchorTerm size}`size_keys` and {anchorTerm IndexMap}`WF` fields in our construction of {anchorTerm emptyWithCapacity}`def emptyWithCapacity`.
Surely these are trivial, and solvable by {tactic}`grind`, so we simply delete those fields:

```anchor emptyWithCapacity
def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity
```
:::

Our next task is to deal with the {lean}`sorry` in our construction of the original {anchorTerm GetElem?}`GetElem?` instance:
```anchor GetElem? (module := IndexMap)
instance :
    GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]'(by sorry)
  getElem? m a :=
    m.indices[a]?.bind (m.values[·]?)
  getElem! m a :=
    m.indices[a]?.bind (m.values[·]?) |>.getD default
```

The goal at this sorry is
```
m : IndexMap α β
a : α
h : a ∈ m
⊢ m.indices[a] < m.values.size
```

:::comment
FIXME (Q3): @david-christiansen:
We need to keep the goal display above in sync with the `sorry` in the code block before it.

The solution is to add support for term goals to the SubVerso extraction mechanism, along the lines of the existing support for saving ordinary goals.
:::


Let's try proving this as a stand-alone theorem, via {tactic}`grind`, and see where {tactic}`grind` gets stuck.
Because we've added {tactic}`grind` annotations for {anchorTerm size}`size` and {anchorTerm size}`size_keys` already, we can safely reformulate the goal as:

```anchor getElem_indices_lt_init
theorem getElem_indices_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.indices[a] < m.size := by
  grind
```

This fails, and looking at the `Goal diagnostics` section of the message from {tactic}`grind` we see that it hasn't done much:

```anchorError getElem_indices_lt_init (expandTrace := facts)
`grind` failed
case grind
α : Type u
β : Type v
inst : BEq α
inst_1 : Hashable α
m : IndexMap α β
a : α
h : a ∈ m
h_1 : m.size ≤ m.indices[a]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] a ∈ m
    [prop] m.size ≤ m.indices[a]
  [eqc] True propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
```

An immediate problem we can see here is that
{tactic}`grind` does not yet know that `a ∈ m` is the same as `a ∈ m.indices`.
Let's add this fact:

```anchor mem_indices_of_mem
@[local grind =] private theorem mem_indices_of_mem
    {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices := Iff.rfl
```

::::leanSection
```lean -show
variable {α : Type u} [BEq α] [Hashable α]
```
:::paragraph

However this proof is going to work, we know the following:
* It must use the well-formedness condition of the map.
* It can't do so without relating `m.indices[a]` and `m.indices[a]?` (because the later is what appears in the well-formedness condition).
* The expected relationship there doesn't even hold unless the map `m.indices` satisfies {lean}`LawfulGetElem`,
  for which we need {tech}[instances] of {lean}`LawfulBEq α` and {lean}`LawfulHashable α`.

:::
:::TODO
TODO: I'd like to ensure there's a link to the `LawfulGetElem` instance for `HashMap`, so we can see these requirements!
:::
::::

:::paragraph
Let's configure things so that those are available:
```anchor Lawfuls
variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF
```

and then give {tactic}`grind` one manual hint, to relate {anchorTerm getElem_indices_lt}`m.indices[a]` and {anchorTerm getElem_indices_lt}`m.indices[a]?`:

```anchor getElem_indices_lt
private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind
```
:::

With that theorem proved, we want to make it accessible to {tactic}`grind`.
We could either add {attrs}`@[local grind]` before the theorem statement,
or write `attribute [local grind] getElem_indices_lt` after the theorem statement.
These will use {tactic}`grind`'s built-in heuristics for deciding a pattern to match the theorem on.

:::paragraph
In this case, let's see which patterns the {attr}`grind` attribute generates:
```anchor getElem_indices_lt_attr
attribute [local grind] getElem_indices_lt
```
```anchorInfo getElem_indices_lt_attr
Try these:
  [apply] [grind
    .] for pattern: [@LE.le `[Nat] `[instLENat] ((@getElem (Std.HashMap #8 `[Nat] #6 #5) _ `[Nat] _ _ (@IndexMap.indices _ #7 _ _ #4) #3 #0) + 1) (@IndexMap.size _ _ _ _ #4)]
  [apply] [grind →] for pattern: [LawfulBEq #8 #6, LawfulHashable _ _ #5, @Membership.mem _ (IndexMap _ #7 _ _) _ #4 #3]
```
These patterns are not useful.
The first is matching on the entire conclusion of the theorem (in fact, a normalized version of it, in which `x < y` has been replaced by `x + 1 ≤ y`).
The second is too general: it will match any term that includes the theorem's assumptions, ignoring the conclusion.
:::

:::paragraph
We want something more general than the entire conclusion, the conclusion should not be ignored.
We'd like this theorem to fire whenever {tactic}`grind` sees {anchorTerm getElem_indices_lt_pattern}`m.indices[a]`, and so instead of using the attribute we write a custom pattern:

```anchor getElem_indices_lt_pattern
grind_pattern getElem_indices_lt => m.indices[a]
```
:::

:::paragraph
The Lean standard library uses the {tactic}`get_elem_tactic` tactic as an auto-parameter for the `xs[i]` notation
(which desugars to `GetElem.getElem xs i h`, with the proof `h` generated by {tactic}`get_elem_tactic`).
We'd like to not only have {tactic}`grind` fill in these proofs, but even to be able to omit these proofs.
To achieve this, we add the line


```anchor get_elem_grind
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)
```

(In later versions of Lean this may be part of the built-in behavior.)
:::

:::paragraph
We can now return to constructing our {anchorName GetElem?}`GetElem?` instance, and simply write:
```anchor GetElem?
instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default
```
with neither any {lean}`sorry`s, nor any explicitly written proofs.
:::

:::paragraph
Next, we want to expose the content of these definitions, but only locally in this file:
```anchor getElem_local
@[local grind =] private theorem getElem_def
    (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m[a] = m.values[m.indices[a]'h] :=
  rfl
@[local grind =] private theorem getElem?_def
    (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) :=
  rfl
@[local grind =] private theorem getElem!_def
    [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (m.values[·]?)).getD default :=
  rfl
```
Again we're using the {anchorTerm getElem_local}`@[local grind =] private theorem` pattern to hide these implementation details,
but allow {tactic}`grind` to see these facts locally.
:::

:::paragraph
Next, we want to prove the {anchorName LawfulGetElem}`LawfulGetElem` instance, and hope that {tactic}`grind` can fill in the proofs:
```anchor LawfulGetElem
instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind
```

Success!
:::

:::paragraph
Let's press onward, and see if we can define {anchorName insert}`insert` without having to write any proofs:
```anchor insert
@[inline] def insert [LawfulBEq α] (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a
      values := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b }
```
In both branches, {tactic}`grind` is automatically proving both the {anchorTerm IndexMap}`size_keys'` and {anchorTerm IndexMap}`WF` fields!
Note also in the first branch the {anchorTerm insert}`set` calls {anchorTerm insert}`m.keys.set i a` and {anchorTerm insert}`m.values.set i b`
are having their “in-bounds” obligations automatically filled in by {tactic}`grind` via the {tactic}`get_elem_tactic` auto-parameter.
:::

:::paragraph
Next let's try `eraseSwap`:
```anchor eraseSwap_init
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m
```
```anchorError eraseSwap_init
`grind` failed
case grind.1.1.2.2.1.1.1
α : Type u
β : Type v
inst : BEq α
inst_1 : Hashable α
m : IndexMap α β
a : α
b : β
i : Nat
inst_2 : LawfulBEq α
inst_3 : LawfulHashable α
m_1 : IndexMap α β
a_1 : α
i_1 : Nat
h : m_1.indices[a_1]? = some i_1
w : ¬i_1 = m_1.size - 1
i_2 : Nat
a_2 : α
h_1 : ((m_1.keys.pop.set i_1 (m_1.keys.back ⋯) ⋯)[i_2]? = some a_2) =
  ¬((m_1.indices.erase a_1).insert (m_1.keys.back ⋯) i_1)[a_2]? = some i_2
h_2 : -1 * ↑(m_1.keys.set i_1 (m_1.keys.back ⋯) ⋯).size + 1 ≤ 0
left : (m_1.keys.pop.set i_1 (m_1.keys.back ⋯) ⋯)[i_2]? = some a_2
right : ¬((m_1.indices.erase a_1).insert (m_1.keys.back ⋯) i_1)[a_2]? = some i_2
h_4 : ¬i_1 = i_2
left_1 : ¬m_1.keys[i_2]? = some a_1
right_1 : ¬m_1.indices[a_1]? = some i_2
h_6 : (m_1.keys.back ⋯ == a_2) = true
h_7 : i_1 + 1 ≤ m_1.keys.pop.size
left_2 : a_2 ∈ m_1.indices.erase a_1
left_3 : (a_1 == a_2) = false
right_3 : a_2 ∈ m_1.indices
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [ring] Rings

[grind] Diagnostics
```

This fails while attempting to prove the {anchorName IndexMap}`WF` field in the second branch.
As usual, there is detailed information from {tactic}`grind` about its failure state, but almost too much to be helpful!
Let's look at the model produced by `cutsat` and see if we can see what's going on:
```anchorError eraseSwap_init (onlyTrace := "Assignment satisfying linear constraints") (expandTrace := cutsat)
[cutsat] Assignment satisfying linear constraints
  [assign] i_1 := 0
  [assign] i_2 := 1
  [assign] m_1.keys.pop.size := 2
  [assign] m_1.keys.size := 3
  [assign] m_1.size := 3
  [assign] (m_1.keys.pop.set i_1 (m_1.keys.back ⋯) ⋯).size := 2
  [assign] m_1.values.size := 3
  [assign] m_1.indices[a_1] := 0
  [assign] ((m_1.indices.erase a_1).insert (m_1.keys.back ⋯) i_1)[a_2] := 0
  [assign] (m_1.keys.set i_1 (m_1.keys.back ⋯) ⋯).pop.size := 2
  [assign] (m_1.keys.set i_1 (m_1.keys.back ⋯) ⋯).size := 3
  [assign] m_1.indices[a_1] := 0
  [assign] m_1.indices[a_2] := 1
  [assign] m_1.indices[m_1.keys[i_2]] := 1
  [assign] m_1.indices[m_1.keys[i_2]] := 1
```


```comment
FIXME (@kim-em / @leodemoura): there is some repeated output here.
```

This model consists of an {anchorName IndexMap}`IndexMap` of size {lean}`3`,
with keys `a_1`, `a_2` and the otherwise unnamed `(keys m_1).back ⋯`.

:::


:::paragraph
Everything looks fine, *except* the line:
```
(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2] := 0
```
This shouldn't be possible! Since the three keys are distinct,
we should have
```
(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2] =
  ((indices m_1).erase a_1)[a_2] =
  (indices m_1)[a_2] =
  1
```
Now that we've found something suspicious, we can look through the equivalence classes identified by `grind`.
(In the future we'll be providing search tools for inspecting equivalence classes, but for now you need to read through manually.)
We find amongst many others:
```
{a_2,
  (keys m_1).back ⋯,
  (keys m_1)[(keys m_1).size - 1],
  (keys m_1)[i_2], ...}
```
This should imply, by the injectivity of {anchorName IndexMap}`keys`, that `i_2 = (keys m_1).size - 1`.
Since this identity *wasn't* reflected by the `cutsat` model,
we suspect that {tactic}`grind` is not managing to use the injectivity of {anchorName IndexMap}`keys`.

:::


Thinking about the way that we've provided the well-formedness condition, as
`∀ (i : Nat) (a : α), keys[i]? = some a ↔ indices[a]? = some i`, this perhaps isn't surprising:
it's expressed in terms of `keys[i]?` and `indices[a]?`.
Let's add a variant version of the well-formedness condition using {name GetElem.getElem}`getElem` instead of {name GetElem?.getElem?}`getElem?`:
```anchor WF'
@[local grind .] private theorem WF'
    (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind
```
We can verify that with this available, {tactic}`grind` can now prove:
```anchor WF'ex
example {m : IndexMap α β} {a : α} {h : a ∈ m} :
  m.keys[m.indices[a]'h] = a := by grind
```

Trying again with {anchorName eraseSwap}`eraseSwap`, everything goes through cleanly now, with no manual proofs:
```anchor eraseSwap
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m
```


Finally we turn to the verification theorems about the basic operations, relating {anchorName Verification}`getIdx`, {anchorName Verification}`findIdx`, and {anchorName Verification}`insert`.
By adding a {anchorTerm Verification}`local grind` annotation allowing {tactic}`grind` to unfold the definitions of these operations,
the proofs all go through effortlessly:
```anchor Verification
/-! ### Verification theorems -/

attribute [local grind] getIdx findIdx insert

@[grind _=_] theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind

@[grind =] theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind

@[grind =] theorem getElem_insert
    (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind

@[grind =] theorem findIdx_insert_self
    (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a =
      if h : a ∈ m then m.findIdx a else m.size := by
  grind
```

Note that these are part of the public API of {anchorName Verification}`IndexMap`, so we need to mark them as {attrs}`@[grind]`,
so that users without our internal {keyword}`local grind` annotations can still use them in {tactic}`grind` proofs.


Putting this all together, our prototype API has reached the following state:

:::TODO
Construct this version from the source module using annotations that cause unwanted content to be discarded, so we keep them in sync
:::

```lean
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)

open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size :=
  m.size_keys'

def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity

instance : EmptyCollection (IndexMap α β) where
  emptyCollection := emptyWithCapacity

instance : Inhabited (IndexMap α β) where
  default := ∅

@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))

@[local grind] private theorem mem_indices_of_mem
    {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices := Iff.rfl

@[inline] def findIdx? (m : IndexMap α β) (a : α) : Option Nat :=
  m.indices[a]?

@[inline] def findIdx (m : IndexMap α β) (a : α)
    (h : a ∈ m := by get_elem_tactic) : Nat :=
  m.indices[a]

@[inline] def getIdx? (m : IndexMap α β) (i : Nat) : Option β :=
  m.values[i]?

@[inline] def getIdx (m : IndexMap α β) (i : Nat)
    (h : i < m.size := by get_elem_tactic) : β :=
  m.values[i]

variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF

private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind

grind_pattern getElem_indices_lt => m.indices[a]

attribute [local grind] size

instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default

@[local grind] private theorem getElem_def
    (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m[a] = m.values[m.indices[a]'h] :=
  rfl
@[local grind] private theorem getElem?_def
    (m : IndexMap α β) (a : α) :
    m[a]? = m.indices[a]?.bind (fun i => (m.values[i]?)) :=
  rfl
@[local grind] private theorem getElem!_def
    [Inhabited β] (m : IndexMap α β) (a : α) :
    m[a]! = (m.indices[a]?.bind (m.values[·]?)).getD default :=
  rfl

instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind

@[inline] def insert [LawfulBEq α] (m : IndexMap α β) (a : α) (b : β) :
    IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys := m.keys.set i a
      values := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys := m.keys.push a
      values := m.values.push b }

instance [LawfulBEq α] : Singleton (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance [LawfulBEq α] : Insert (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance [LawfulBEq α] : LawfulSingleton (α × β) (IndexMap α β) :=
    ⟨fun _ => rfl⟩

@[local grind] private theorem WF'
    (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind

/--
Erase the key-value pair with the given key,
moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
@[inline] def eraseSwap (m : IndexMap α β) (a : α) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    if w : i = m.size - 1 then
      { indices := m.indices.erase a
        keys := m.keys.pop
        values := m.values.pop }
    else
      let lastKey := m.keys.back
      let lastValue := m.values.back
      { indices := (m.indices.erase a).insert lastKey i
        keys := m.keys.pop.set i lastKey
        values := m.values.pop.set i lastValue }
  | none => m

/-! ### Verification theorems -/

attribute [local grind] getIdx findIdx insert

@[grind] theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind

@[grind] theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind

@[grind] theorem getElem_insert
    (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind

@[grind] theorem findIdx_insert_self
    (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a =
      if h : a ∈ m then m.findIdx a else m.size := by
  grind

end IndexMap
```

We haven't yet proved all the theorems we would want about these operations (or indeed any theorems about {anchorName eraseSwap}`eraseSwap`); the interested reader is encouraged to try proving more,
and perhaps even releasing a complete {anchorName IndexMap}`IndexMap` library!

Summarizing the design principles discussed above about encapsulation:
* the fields of {anchorName IndexMap}`IndexMap` are all private, as these are implementation details.
* the theorems about these fields are all private, and marked as {attrs}`@[local grind]`, rather than {attrs}`@[grind]`, as they won't be needed after we've set up the API.
* the verification theorems are both marked as {attrs}`@[grind]`, and proved by {tactic}`grind`:
  the annotation is necessary because we want grind to be able to prove these facts even once we're outside the current module, and the {attrs}`@[local grind]` theorems are no longer available.
