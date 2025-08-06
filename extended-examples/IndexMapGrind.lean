import Std.Data.HashMap
import IndexMapGrind.CheckMsgs

open Std in
-- This block is here as a guard: when/if the global `get_elem_tactic` uses grind, this will fail,
-- prompting us to update the sentence about "later versions of Lean" in the chapter.
example (m : HashMap Nat Nat) : (m.insert 1 2).size ≤ m.size + 1 := by
  fail_if_success get_elem_tactic
  grind


-- ANCHOR: get_elem_grind
macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)
-- ANCHOR_END: get_elem_grind

open Std in
-- This code is also here as a guard: it makes sure `grind` is working in tactic.
example (m : HashMap Nat Nat) : (m.insert 1 2).size ≤ m.size + 1 := by
  get_elem_tactic


open Std

-- ANCHOR: IndexMap
structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind
-- ANCHOR_END: IndexMap

namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}

-- ANCHOR: size
@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size :=
  m.size_keys'
-- ANCHOR_END: size

-- ANCHOR: emptyWithCapacity
def emptyWithCapacity (capacity := 8) : IndexMap α β where
  indices := HashMap.emptyWithCapacity capacity
  keys := Array.emptyWithCapacity capacity
  values := Array.emptyWithCapacity capacity
-- ANCHOR_END: emptyWithCapacity

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

discarding
/--
error: `grind` failed
case grind
α : Type u
β : Type v
inst : BEq α
inst_1 : Hashable α
m : IndexMap α β
a : α
h : a ∈ m
h_1 : m.size ≤ (indices m)[a]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] a ∈ m
    [prop] m.size ≤ (indices m)[a]
  [eqc] True propositions
    [prop] m.size ≤ (indices m)[a]
    [prop] a ∈ m
  [eqc] Equivalence classes
    [eqc] {Membership.mem, fun m a => a ∈ m}
  [ematch] E-matching patterns
    [thm] HashMap.contains_iff_mem: [@Membership.mem #5 (HashMap _ #4 #3 #2) _ #1 #0]
  [cutsat] Assignment satisfying linear constraints
    [assign] m.size := 0
    [assign] (indices m)[a] := 0
-/
#check_msgs in
-- ANCHOR: getElem_indices_lt_init
theorem getElem_indices_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.indices[a] < m.size := by
  grind
-- ANCHOR_END: getElem_indices_lt_init
stop discarding

-- ANCHOR: mem_indices_of_mem
@[local grind] private theorem mem_indices_of_mem
    {m : IndexMap α β} {a : α} :
    a ∈ m ↔ a ∈ m.indices := Iff.rfl
-- ANCHOR_END: mem_indices_of_mem

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

-- ANCHOR: Lawfuls
variable [LawfulBEq α] [LawfulHashable α]

attribute [local grind _=_] IndexMap.WF
-- ANCHOR_END: Lawfuls

-- ANCHOR: getElem_indices_lt
private theorem getElem_indices_lt {h : a ∈ m} : m.indices[a] < m.size := by
  have : m.indices[a]? = some m.indices[a] := by grind
  grind
-- ANCHOR_END: getElem_indices_lt

section
/--
info: getElem_indices_lt: [@LE.le `[Nat] `[instLENat] ((@getElem (HashMap #8 `[Nat] #6 #5) _ `[Nat] _ _ (@indices _ #7 _ _ #4) #3 #0) + 1) (@size _ _ _ _ #4)]
-/
#check_msgs in
-- ANCHOR: getElem_indices_lt_attr
attribute [local grind?] getElem_indices_lt
-- ANCHOR_END: getElem_indices_lt_attr
end

-- ANCHOR: getElem_indices_lt_pattern
grind_pattern getElem_indices_lt => m.indices[a]
-- ANCHOR_END: getElem_indices_lt_pattern

attribute [local grind] size

-- ANCHOR: GetElem?
instance : GetElem? (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem m a h :=
    m.values[m.indices[a]]
  getElem? m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?))
  getElem! m a :=
    m.indices[a]?.bind (fun i => (m.values[i]?)) |>.getD default
-- ANCHOR_END: GetElem?

-- ANCHOR: getElem_local
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
-- ANCHOR_END: getElem_local

-- ANCHOR: LawfulGetElem
instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind
-- ANCHOR_END: LawfulGetElem

-- ANCHOR: insert
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
-- ANCHOR_END: insert

discarding
/--
error: could not synthesize default value for field 'WF' of 'IndexMap' using tactics
---
error: `grind` failed
case grind.1.1.2.2.1.1.1.1
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
h : (indices m_1)[a_1]? = some i_1
w : ¬i_1 = m_1.size - 1
i_2 : Nat
a_2 : α
h_1 :
  (((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some a_2) =
    ¬(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = some i_2
h_2 : -1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + 1 ≤ 0
left : ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some a_2
right : ¬(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = some i_2
h_4 : ¬i_1 = i_2
left_1 : ¬(keys m_1)[i_2]? = some a_1
right_1 : ¬(indices m_1)[a_1]? = some i_2
h_6 : ((keys m_1).back ⋯ == a_2) = true
h_7 : i_1 + 1 ≤ (keys m_1).pop.size
left_2 : ((indices m_1).erase a_1).contains a_2 = true
right_2 : a_2 ∈ (indices m_1).erase a_1
h_9 : 0 = (indices m_1)[a_1]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] LawfulBEq α
    [prop] LawfulHashable α
    [prop] (indices m_1)[a_1]? = some i_1
    [prop] ¬i_1 = m_1.size - 1
    [prop] (((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some a_2) =
          ¬(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = some i_2
    [prop] ¬a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1 →
          (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = none
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size ≤ i_2 →
          ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = none
    [prop] ¬a_1 ∈ indices m_1 → (indices m_1)[a_1]? = none
    [prop] ∀ (h_10 : a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1),
          (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? =
            some (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]
    [prop] ∀ (h_10 : i_2 + 1 ≤ ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size),
          ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? =
            some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] ∀ (h : a_1 ∈ indices m_1), (indices m_1)[a_1]? = some (indices m_1)[a_1]
    [prop] ((keys m_1)[i_1]? = some a_1) = ((indices m_1)[a_1]? = some i_1)
    [prop] ((keys m_1)[i_2]? = some a_1) = ((indices m_1)[a_1]? = some i_2)
    [prop] m_1.size = (values m_1).size
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? =
          if i_1 = i_2 then some ((keys m_1).back ⋯) else (keys m_1).pop[i_2]?
    [prop] (keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯ = ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop
    [prop] (keys m_1).back ⋯ = (keys m_1)[(keys m_1).size - 1]
    [prop] (keys m_1).size = m_1.size
    [prop] (keys m_1).pop.size = (keys m_1).size - 1
    [prop] (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? =
          if ((keys m_1).back ⋯ == a_2) = true then some i_1 else ((indices m_1).erase a_1)[a_2]?
    [prop] (keys m_1).size ≤ i_2 → (keys m_1)[i_2]? = none
    [prop] (keys m_1).size ≤ i_1 → (keys m_1)[i_1]? = none
    [prop] ∀ (h : i_2 + 1 ≤ (keys m_1).size), (keys m_1)[i_2]? = some (keys m_1)[i_2]
    [prop] ∀ (h : i_1 + 1 ≤ (keys m_1).size), (keys m_1)[i_1]? = some (keys m_1)[i_1]
    [prop] ((indices m_1).contains a_1 = true) = (a_1 ∈ indices m_1)
    [prop] ((((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1).contains a_2 = true) =
          (a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)
    [prop] ((keys m_1)[(indices m_1)[a_1]]? = some a_1) = ((indices m_1)[a_1]? = some (indices m_1)[a_1])
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop[i_2]? =
          if i_2 + 1 ≤ ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1 then
            ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]?
          else none
    [prop] ∀ (h_10 : i_1 + 1 ≤ (keys m_1).pop.size),
          (keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯ = ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop
    [prop] ((keys m_1)[i_2]? = some a_2) = ((indices m_1)[a_2]? = some i_2)
    [prop] ((keys m_1)[i_1]? = some a_2) = ((indices m_1)[a_2]? = some i_1)
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size ≤ i_2 →
          ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = none
    [prop] (keys m_1).size ≤ i_2 → (keys m_1)[i_2]? = none
    [prop] (keys m_1).size ≤ i_1 → (keys m_1)[i_1]? = none
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop.size = ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size = (keys m_1).pop.size
    [prop] (a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1) =
          ((keys m_1).back ⋯ = a_2 ∨ a_2 ∈ (indices m_1).erase a_1)
    [prop] ∀ (h : a_1 ∈ m_1), (indices m_1)[a_1] + 1 ≤ m_1.size
    [prop] ¬a_2 ∈ indices m_1 → (indices m_1)[a_2]? = none
    [prop] ∀ (h : a_2 ∈ indices m_1), (indices m_1)[a_2]? = some (indices m_1)[a_2]
    [prop] (((indices m_1).erase a_1).contains a_2 = true) = (a_2 ∈ (indices m_1).erase a_1)
    [prop] ((keys m_1)[(indices m_1)[a_1]]? = some a_2) = ((indices m_1)[a_2]? = some (indices m_1)[a_1])
    [prop] ((keys m_1)[i_1]? = some (keys m_1)[i_1]) = ((indices m_1)[(keys m_1)[i_1]]? = some i_1)
    [prop] ((keys m_1)[i_2]? = some (keys m_1)[i_1]) = ((indices m_1)[(keys m_1)[i_1]]? = some i_2)
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size = (keys m_1).size
    [prop] (a_2 ∈ (indices m_1).erase a_1) = ((a_1 == a_2) = false ∧ a_2 ∈ indices m_1)
    [prop] ((((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1).contains a_2 = true) =
          ((keys m_1).back ⋯ = a_2 ∨ ((indices m_1).erase a_1).contains a_2 = true)
    [prop] (a_1 ∈ m_1) = (a_1 ∈ indices m_1)
    [prop] ((indices m_1).contains a_2 = true) = (a_2 ∈ indices m_1)
    [prop] (((indices m_1).erase a_1).contains a_2 = true) = ((!a_1 == a_2) = true ∧ (indices m_1).contains a_2 = true)
    [prop] -1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + 1 ≤ 0
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some a_2
    [prop] ¬(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = some i_2
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size ≤ i_2 →
          ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = none
    [prop] ∀ (h_10 : i_2 + 1 ≤ ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size),
          ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? =
          if i_1 = i_2 then some ((keys m_1).back ⋯) else (keys m_1)[i_2]?
    [prop] ((keys m_1)[i_1]? = some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]) =
          ((indices m_1)[((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]]? = some i_1)
    [prop] ((keys m_1)[i_2]? = some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]) =
          ((indices m_1)[((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]]? = some i_2)
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size ≤ i_2 →
          ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = none
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2] =
          if i_1 = i_2 then (keys m_1).back ⋯ else (keys m_1).pop[i_2]
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop[i_2] = ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] ((keys m_1)[i_1]? = some (keys m_1)[i_2]) = ((indices m_1)[(keys m_1)[i_2]]? = some i_1)
    [prop] ((keys m_1)[i_2]? = some (keys m_1)[i_2]) = ((indices m_1)[(keys m_1)[i_2]]? = some i_2)
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2] = if i_1 = i_2 then (keys m_1).back ⋯ else (keys m_1)[i_2]
    [prop] ¬(keys m_1)[i_2] ∈ indices m_1 → (indices m_1)[(keys m_1)[i_2]]? = none
    [prop] ∀ (h_10 : (keys m_1)[i_2] ∈ indices m_1),
          (indices m_1)[(keys m_1)[i_2]]? = some (indices m_1)[(keys m_1)[i_2]]
    [prop] ((keys m_1)[(indices m_1)[a_1]]? = some (keys m_1)[i_2]) =
          ((indices m_1)[(keys m_1)[i_2]]? = some (indices m_1)[a_1])
    [prop] ((indices m_1).contains (keys m_1)[i_2] = true) = ((keys m_1)[i_2] ∈ indices m_1)
    [prop] ((keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some (keys m_1)[i_2]) =
          ((indices m_1)[(keys m_1)[i_2]]? = some (indices m_1)[(keys m_1)[i_2]])
    [prop] ((keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some a_2) =
          ((indices m_1)[a_2]? = some (indices m_1)[(keys m_1)[i_2]])
    [prop] ((keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some a_1) =
          ((indices m_1)[a_1]? = some (indices m_1)[(keys m_1)[i_2]])
    [prop] ∀ (h_10 : (keys m_1)[i_2] ∈ m_1), (indices m_1)[(keys m_1)[i_2]] + 1 ≤ m_1.size
    [prop] ((keys m_1)[i_2] ∈ m_1) = ((keys m_1)[i_2] ∈ indices m_1)
    [prop] ¬i_1 = i_2
    [prop] (keys m_1).pop.size ≤ i_2 → (keys m_1).pop[i_2]? = none
    [prop] ∀ (h : i_2 + 1 ≤ (keys m_1).pop.size), (keys m_1).pop[i_2]? = some (keys m_1).pop[i_2]
    [prop] (keys m_1).pop[i_2]? = if i_2 + 1 ≤ (keys m_1).size - 1 then (keys m_1)[i_2]? else none
    [prop] (keys m_1).pop.size ≤ i_2 → (keys m_1).pop[i_2]? = none
    [prop] (keys m_1).pop[i_2] = (keys m_1)[i_2]
    [prop] ¬(keys m_1)[i_2]? = some a_1
    [prop] ¬(indices m_1)[a_1]? = some i_2
    [prop] ((keys m_1).back ⋯ == a_2) = true
    [prop] (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2] =
          if h₂ : ((keys m_1).back ⋯ == a_2) = true then i_1 else ((indices m_1).erase a_1)[a_2]
    [prop] i_1 + 1 ≤ (keys m_1).pop.size
    [prop] ((indices m_1).erase a_1).contains a_2 = true
    [prop] a_2 ∈ (indices m_1).erase a_1
    [prop] 0 = (indices m_1)[a_1]
  [eqc] True propositions
    [prop] ¬(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = some i_2
    [prop] LawfulBEq α
    [prop] (((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some a_2) =
          ¬(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = some i_2
    [prop] 0 = (indices m_1)[a_1]
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some a_2
    [prop] LawfulHashable α
    [prop] -1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + 1 ≤ 0
    [prop] -1 * ↑(keys m_1).size + 1 ≤ 0
    [prop] -1 * ↑m_1.size + 1 ≤ 0
    [prop] i_1 < (keys m_1).pop.size
    [prop] 0 < (keys m_1).size
    [prop] ((keys m_1)[i_1]? = some a_1) = ((indices m_1)[a_1]? = some i_1)
    [prop] ((keys m_1)[i_2]? = some a_1) = ((indices m_1)[a_1]? = some i_2)
    [prop] ((keys m_1).back ⋯ == a_2) = true
    [prop] (indices m_1)[a_1]? = some i_1
    [prop] (indices m_1)[a_1]? = some (indices m_1)[a_1]
    [prop] (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? =
          some (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? =
          some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] (keys m_1)[i_1]? = some a_1
    [prop] i_2 + 1 ≤ ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size
    [prop] i_1 < (keys m_1).size
    [prop] i_2 < ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size
    [prop] (keys m_1).size - 1 < (keys m_1).size
    [prop] a_1 ∈ indices m_1
    [prop] a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1
    [prop] ¬a_1 ∈ indices m_1 → (indices m_1)[a_1]? = none
    [prop] ¬a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1 →
          (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = none
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size ≤ i_2 →
          ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = none
    [prop] ∀ (h_10 : i_2 + 1 ≤ ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size),
          ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? =
            some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] ∀ (h : a_1 ∈ indices m_1), (indices m_1)[a_1]? = some (indices m_1)[a_1]
    [prop] ∀ (h_10 : a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1),
          (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? =
            some (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]
    [prop] (keys m_1).back ⋯ = a_2 ∨ a_2 ∈ (indices m_1).erase a_1
    [prop] ((indices m_1).contains a_1 = true) = (a_1 ∈ indices m_1)
    [prop] ((((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1).contains a_2 = true) =
          (a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)
    [prop] ((keys m_1)[i_1]? = some a_2) = ((indices m_1)[a_2]? = some i_1)
    [prop] ((keys m_1)[i_1]? = some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]) =
          ((indices m_1)[((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]]? = some i_1)
    [prop] ((keys m_1)[i_2]? = some a_2) = ((indices m_1)[a_2]? = some i_2)
    [prop] ((keys m_1)[i_2]? = some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]) =
          ((indices m_1)[((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]]? = some i_2)
    [prop] ((keys m_1)[(indices m_1)[a_1]]? = some a_1) = ((indices m_1)[a_1]? = some (indices m_1)[a_1])
    [prop] (a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1) =
          ((keys m_1).back ⋯ = a_2 ∨ a_2 ∈ (indices m_1).erase a_1)
    [prop] (indices m_1).contains a_1 = true
    [prop] (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1).contains a_2 = true
    [prop] (indices m_1)[a_2]? = some i_2
    [prop] (indices m_1)[((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]]? = some i_2
    [prop] (keys m_1).back ⋯ = a_2
    [prop] (keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯ = ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop
    [prop] (keys m_1).pop[i_2]? = some (keys m_1).pop[i_2]
    [prop] (keys m_1)[i_1]? = some (keys m_1)[i_1]
    [prop] (keys m_1)[i_2]? = some a_2
    [prop] (keys m_1)[i_2]? = some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] (keys m_1)[i_2]? = some (keys m_1)[i_2]
    [prop] (keys m_1)[(indices m_1)[a_1]]? = some a_1
    [prop] i_1 + 1 ≤ (keys m_1).pop.size
    [prop] i_1 + 1 ≤ (keys m_1).size
    [prop] i_2 + 1 ≤ (keys m_1).pop.size
    [prop] i_2 + 1 ≤ (keys m_1).size
    [prop] i_2 + 1 ≤ ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1
    [prop] i_2 + 1 ≤ (keys m_1).size - 1
    [prop] (indices m_1)[a_1] + 1 ≤ m_1.size
    [prop] i_2 < ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop.size
    [prop] i_2 < (keys m_1).pop.size
    [prop] i_2 < (keys m_1).size
    [prop] a_2 ∈ (indices m_1).erase a_1
    [prop] a_1 ∈ m_1
    [prop] (keys m_1).pop.size ≤ i_2 → (keys m_1).pop[i_2]? = none
    [prop] (keys m_1).size ≤ i_1 → (keys m_1)[i_1]? = none
    [prop] (keys m_1).size ≤ i_2 → (keys m_1)[i_2]? = none
    [prop] ∀ (h_10 : i_1 + 1 ≤ (keys m_1).pop.size),
          (keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯ = ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop
    [prop] ∀ (h : i_1 + 1 ≤ (keys m_1).size), (keys m_1)[i_1]? = some (keys m_1)[i_1]
    [prop] ∀ (h : i_2 + 1 ≤ (keys m_1).pop.size), (keys m_1).pop[i_2]? = some (keys m_1).pop[i_2]
    [prop] ∀ (h : i_2 + 1 ≤ (keys m_1).size), (keys m_1)[i_2]? = some (keys m_1)[i_2]
    [prop] ∀ (h : a_1 ∈ m_1), (indices m_1)[a_1] + 1 ≤ m_1.size
    [prop] (a_1 == a_2) = false ∧ a_2 ∈ indices m_1
    [prop] (keys m_1).back ⋯ = a_2 ∨ ((indices m_1).erase a_1).contains a_2 = true
    [prop] (((indices m_1).erase a_1).contains a_2 = true) = (a_2 ∈ (indices m_1).erase a_1)
    [prop] ((((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1).contains a_2 = true) =
          ((keys m_1).back ⋯ = a_2 ∨ ((indices m_1).erase a_1).contains a_2 = true)
    [prop] ((keys m_1)[i_1]? = some (keys m_1)[i_1]) = ((indices m_1)[(keys m_1)[i_1]]? = some i_1)
    [prop] ((keys m_1)[i_1]? = some (keys m_1)[i_2]) = ((indices m_1)[(keys m_1)[i_2]]? = some i_1)
    [prop] ((keys m_1)[i_2]? = some (keys m_1)[i_1]) = ((indices m_1)[(keys m_1)[i_1]]? = some i_2)
    [prop] ((keys m_1)[i_2]? = some (keys m_1)[i_2]) = ((indices m_1)[(keys m_1)[i_2]]? = some i_2)
    [prop] ((keys m_1)[(indices m_1)[a_1]]? = some a_2) = ((indices m_1)[a_2]? = some (indices m_1)[a_1])
    [prop] (a_2 ∈ (indices m_1).erase a_1) = ((a_1 == a_2) = false ∧ a_2 ∈ indices m_1)
    [prop] (a_1 ∈ m_1) = (a_1 ∈ indices m_1)
    [prop] (a_1 == a_2) = false
    [prop] ((indices m_1).erase a_1).contains a_2 = true
    [prop] (indices m_1)[a_2]? = some (indices m_1)[a_2]
    [prop] (indices m_1)[(keys m_1)[i_1]]? = some i_1
    [prop] (indices m_1)[(keys m_1)[i_2]]? = some i_2
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] i_2 + 1 ≤ ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size
    [prop] i_2 < ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size
    [prop] a_2 ∈ indices m_1
    [prop] ¬a_2 ∈ indices m_1 → (indices m_1)[a_2]? = none
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size ≤ i_2 →
          ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = none
    [prop] ∀ (h_10 : i_2 + 1 ≤ ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size),
          ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] ∀ (h : a_2 ∈ indices m_1), (indices m_1)[a_2]? = some (indices m_1)[a_2]
    [prop] (!a_1 == a_2) = true ∧ (indices m_1).contains a_2 = true
    [prop] ((indices m_1).contains a_2 = true) = (a_2 ∈ indices m_1)
    [prop] (((indices m_1).erase a_1).contains a_2 = true) = ((!a_1 == a_2) = true ∧ (indices m_1).contains a_2 = true)
    [prop] ((keys m_1)[(indices m_1)[a_1]]? = some (keys m_1)[i_2]) =
          ((indices m_1)[(keys m_1)[i_2]]? = some (indices m_1)[a_1])
    [prop] (!a_1 == a_2) = true
    [prop] (indices m_1).contains a_2 = true
    [prop] (indices m_1)[(keys m_1)[i_2]]? = some (indices m_1)[(keys m_1)[i_2]]
    [prop] (keys m_1)[i_2] ∈ indices m_1
    [prop] ¬(keys m_1)[i_2] ∈ indices m_1 → (indices m_1)[(keys m_1)[i_2]]? = none
    [prop] ∀ (h_10 : (keys m_1)[i_2] ∈ indices m_1),
          (indices m_1)[(keys m_1)[i_2]]? = some (indices m_1)[(keys m_1)[i_2]]
    [prop] ((indices m_1).contains (keys m_1)[i_2] = true) = ((keys m_1)[i_2] ∈ indices m_1)
    [prop] ((keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some a_1) =
          ((indices m_1)[a_1]? = some (indices m_1)[(keys m_1)[i_2]])
    [prop] ((keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some a_2) =
          ((indices m_1)[a_2]? = some (indices m_1)[(keys m_1)[i_2]])
    [prop] ((keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some (keys m_1)[i_2]) =
          ((indices m_1)[(keys m_1)[i_2]]? = some (indices m_1)[(keys m_1)[i_2]])
    [prop] (indices m_1).contains (keys m_1)[i_2] = true
    [prop] (indices m_1)[a_2]? = some (indices m_1)[(keys m_1)[i_2]]
    [prop] (keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some a_2
    [prop] (keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some (keys m_1)[i_2]
    [prop] (indices m_1)[(keys m_1)[i_2]] + 1 ≤ m_1.size
    [prop] (keys m_1)[i_2] ∈ m_1
    [prop] ∀ (h_10 : (keys m_1)[i_2] ∈ m_1), (indices m_1)[(keys m_1)[i_2]] + 1 ≤ m_1.size
    [prop] ((keys m_1)[i_2] ∈ m_1) = ((keys m_1)[i_2] ∈ indices m_1)
  [eqc] False propositions
    [prop] i_1 = m_1.size - 1
    [prop] (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = some i_2
    [prop] a_1 = a_2
    [prop] ¬a_1 ∈ indices m_1
    [prop] ¬a_2 ∈ ((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1
    [prop] i_1 = i_2
    [prop] (indices m_1)[a_1]? = none
    [prop] (indices m_1)[a_1]? = some i_2
    [prop] (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = none
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = none
    [prop] (keys m_1)[i_2]? = some a_1
    [prop] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size ≤ i_2
    [prop] (indices m_1)[a_2]? = some i_1
    [prop] (indices m_1)[((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]]? = some i_1
    [prop] (keys m_1).pop[i_2]? = none
    [prop] (keys m_1)[i_1]? = none
    [prop] (keys m_1)[i_1]? = some a_2
    [prop] (keys m_1)[i_1]? = some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]
    [prop] (keys m_1)[i_2]? = none
    [prop] (keys m_1).pop.size ≤ i_2
    [prop] (keys m_1).size ≤ i_1
    [prop] (keys m_1).size ≤ i_2
    [prop] ¬a_2 ∈ indices m_1
    [prop] (indices m_1)[a_2]? = none
    [prop] (indices m_1)[a_2]? = some (indices m_1)[a_1]
    [prop] (indices m_1)[(keys m_1)[i_1]]? = some i_2
    [prop] (indices m_1)[(keys m_1)[i_2]]? = some i_1
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = none
    [prop] (keys m_1)[i_1]? = some (keys m_1)[i_2]
    [prop] (keys m_1)[i_2]? = some (keys m_1)[i_1]
    [prop] (keys m_1)[(indices m_1)[a_1]]? = some a_2
    [prop] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size ≤ i_2
    [prop] ¬(keys m_1)[i_2] ∈ indices m_1
    [prop] (indices m_1)[(keys m_1)[i_2]]? = none
    [prop] (indices m_1)[(keys m_1)[i_2]]? = some (indices m_1)[a_1]
    [prop] (keys m_1)[(indices m_1)[a_1]]? = some (keys m_1)[i_2]
    [prop] (indices m_1)[a_1]? = some (indices m_1)[(keys m_1)[i_2]]
    [prop] (keys m_1)[(indices m_1)[(keys m_1)[i_2]]]? = some a_1
  [eqc] Equivalence classes
    [eqc] {a_1, (keys m_1)[i_1]}
    [eqc] {i_1,
        0,
        (indices m_1)[a_1],
        (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2],
        if h₂ : ((keys m_1).back ⋯ == a_2) = true then i_1 else ((indices m_1).erase a_1)[a_2],
        (indices m_1)[a_1]}
    [eqc] {i_2, (indices m_1)[a_2], (indices m_1)[(keys m_1)[i_2]], (indices m_1)[(keys m_1)[i_2]]}
    [eqc] {a_2,
        (keys m_1).back ⋯,
        ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2],
        (keys m_1)[(keys m_1).size - 1],
        if i_1 = i_2 then (keys m_1).back ⋯ else (keys m_1).pop[i_2],
        ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop[i_2],
        (keys m_1).pop[i_2],
        (keys m_1)[i_2],
        ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2],
        if i_1 = i_2 then (keys m_1).back ⋯ else (keys m_1)[i_2]}
    [eqc] {false, a_1 == a_2}
    [eqc] {true,
        (keys m_1).back ⋯ == a_2,
        (indices m_1).contains a_1,
        (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1).contains a_2,
        ((indices m_1).erase a_1).contains a_2,
        !a_1 == a_2,
        (indices m_1).contains a_2,
        (indices m_1).contains (keys m_1)[i_2]}
    [eqc] {(keys m_1).pop.size,
        m_1.size - 1,
        ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size,
        (keys m_1).size - 1,
        ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop.size,
        ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1}
    [eqc] {(keys m_1).size, m_1.size, (values m_1).size, ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size}
    [eqc] {some i_1,
        (indices m_1)[a_1]?,
        (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]?,
        some (indices m_1)[a_1],
        some (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2],
        if ((keys m_1).back ⋯ == a_2) = true then some i_1 else ((indices m_1).erase a_1)[a_2]?,
        (indices m_1)[(keys m_1)[i_1]]?}
    [eqc] {some i_2,
        (indices m_1)[a_2]?,
        (indices m_1)[((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]]?,
        some (indices m_1)[a_2],
        (indices m_1)[(keys m_1)[i_2]]?,
        some (indices m_1)[(keys m_1)[i_2]]}
    [eqc] {some a_2,
        ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]?,
        some ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2],
        if i_1 = i_2 then some ((keys m_1).back ⋯) else (keys m_1).pop[i_2]?,
        (keys m_1).pop[i_2]?,
        (keys m_1)[i_2]?,
        some (keys m_1).pop[i_2],
        some (keys m_1)[i_2],
        if i_2 + 1 ≤ ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1 then
          ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]?
        else none,
        if i_2 + 1 ≤ (keys m_1).size - 1 then (keys m_1)[i_2]? else none,
        ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop[i_2]?,
        ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2]?,
        some ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯)[i_2],
        if i_1 = i_2 then some ((keys m_1).back ⋯) else (keys m_1)[i_2]?,
        (keys m_1)[(indices m_1)[(keys m_1)[i_2]]]?}
    [eqc] {↑(m_1.size - 1), ↑((keys m_1).size - 1), ↑(((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1)}
    [eqc] {Membership.mem, fun m a => a ∈ m}
    [eqc] {↑i_1, ↑0, ↑(indices m_1)[a_1]}
    [eqc] {↑i_2, ↑(indices m_1)[(keys m_1)[i_2]]}
    [eqc] {↑(keys m_1).pop.size,
        ↑(m_1.size - 1),
        ↑((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size,
        ↑((keys m_1).size - 1),
        ↑(((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1)}
    [eqc] {↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size, ↑(keys m_1).size, ↑m_1.size}
    [eqc] {(keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯, ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop}
    [eqc] {if -1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + 1 ≤ 0 then
          ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + -1
        else 0,
        if -1 * ↑(keys m_1).size + 1 ≤ 0 then ↑(keys m_1).size + -1 else 0,
        if -1 * ↑m_1.size + 1 ≤ 0 then ↑m_1.size + -1 else 0,
        ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + -1,
        ↑(keys m_1).size + -1,
        ↑m_1.size + -1,
        if -1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + 1 ≤ 0 then
          ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + -1
        else 0,
        if -1 * ↑(keys m_1).size + 1 ≤ 0 then ↑(keys m_1).size + -1 else 0}
    [eqc] {-1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + 1, -1 * ↑(keys m_1).size + 1, -1 * ↑m_1.size + 1}
    [eqc] {-1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size, -1 * ↑(keys m_1).size, -1 * ↑m_1.size}
    [eqc] {some a_1, (keys m_1)[i_1]?, some (keys m_1)[i_1], (keys m_1)[(indices m_1)[a_1]]?}
    [eqc] {i_2 + 1, (indices m_1)[(keys m_1)[i_2]] + 1}
    [eqc] {i_1 + 1, (indices m_1)[a_1] + 1}
  [cases] Case analyses
    [cases] [1/2]: if -1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + 1 ≤ 0 then
          ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + -1
        else 0
      [cases] source: E-matching Array.getElem?_pop
    [cases] [1/2]: (((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯)[i_2]? = some a_2) =
          ¬(((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2]? = some i_2
      [cases] source: Initial goal
    [cases] [2/2]: if i_1 = i_2 then some ((keys m_1).back ⋯) else (keys m_1).pop[i_2]?
      [cases] source: E-matching Array.getElem?_set
    [cases] [2/2]: ((keys m_1)[i_2]? = some a_1) = ((indices m_1)[a_1]? = some i_2)
      [cases] source: E-matching WF
    [cases] [1/2]: if ((keys m_1).back ⋯ == a_2) = true then some i_1 else ((indices m_1).erase a_1)[a_2]?
      [cases] source: E-matching HashMap.getElem?_insert
    [cases] [1/2]: i_1 + 1 ≤ (keys m_1).pop.size
      [cases] source: E-matching Array.set_pop
    [cases] [1/2]: (((indices m_1).erase a_1).contains a_2 = true) = (a_2 ∈ (indices m_1).erase a_1)
      [cases] source: E-matching HashMap.contains_iff_mem
    [cases] [1/2]: 0 = (indices m_1)[a_1]
      [cases] source: Model-based theory combination at argument #2 of
            i_1 < (keys m_1).pop.size
          and
            0 < (keys m_1).size
  [ematch] E-matching patterns
    [thm] getElem?_neg: [@getElem? #8 #7 #6 #5 #4 #2 #1]
    [thm] getElem?_pos: [@getElem? #8 #7 #6 #5 #4 #2 #1]
    [thm] HashMap.contains_iff_mem: [@Membership.mem #5 (HashMap _ #4 #3 #2) _ #1 #0]
    [thm] WF: [@getElem? (HashMap #6 `[Nat] #4 #3) _ `[Nat] _ _ (@indices _ #5 _ _ #2) #0, @some `[Nat] #1]
    [thm] size.eq_1: [@size #4 #3 #2 #1 #0]
    [thm] Option.some_le_some: [@LE.le (Option #3) _ (@some _ #1) (@some _ #0)]
    [thm] Option.mem_some: [@Membership.mem #2 (Option _) _ (@some _ #0) #1]
    [thm] Array.contains_iff_mem: [@Membership.mem #4 (Array _) _ #1 #0]
    [thm] Array.getElem?_set: [@getElem? (Array #5) `[Nat] _ _ _ (@Array.set _ #4 #3 #1 #2) #0]
    [thm] Array.mem_or_eq_of_mem_set: [@Membership.mem #6 (Array _) _ (@Array.set _ #5 #4 #2 _) #3]
    [thm] Array.set_pop: [@Array.set #4 (@Array.pop _ #3) #1 #2 #0]
    [thm] Array.getElem?_pop: [@getElem? (Array #2) `[Nat] _ _ _ (@Array.pop _ #1) #0]
    [thm] Array.set_pop: [@Array.pop #4 (@Array.set _ #3 #1 #2 _)]
    [thm] WF: [@getElem? (Array #6) `[Nat] _ _ _ (@keys _ #5 #4 #3 #2) #1, @some _ #0]
    [thm] Array.back_eq_getElem: [@Array.back #2 #1 #0]
    [thm] Option.some_lt_some: [@LT.lt (Option #3) _ (@some _ #1) (@some _ #0)]
    [thm] Array.size_pos_of_mem: [@Membership.mem #3 (Array _) _ #1 #2, @Array.size _ #1]
    [thm] size_keys: [@Array.size #4 (@keys _ #3 #2 #1 #0)]
    [thm] Array.getElem?_eq_none: [@Array.size #3 #1, @getElem? (Array _) `[Nat] _ _ _ #1 #2]
    [thm] Array.size_pop: [@Array.size #1 (@Array.pop _ #0)]
    [thm] Array.size_set: [@Array.size #4 (@Array.set _ #3 #2 #1 #0)]
    [thm] HashMap.mem_insert: [@Membership.mem #9 (HashMap _ #8 #7 #6) _ (@HashMap.insert _ _ #7 #6 #5 #2 #0) #1]
    [thm] HashMap.getElem?_insert: [@getElem? (HashMap #9 #8 #7 #6) _ _ _ _ (@HashMap.insert _ _ #7 #6 #5 #2 #0) #1]
    [thm] HashMap.mem_erase: [@Membership.mem #8 (HashMap _ #7 #6 #5) _ (@HashMap.erase _ _ #6 #5 #4 #1) #0]
    [thm] HashMap.getElem?_erase: [@getElem? (HashMap #8 #7 #6 #5) _ _ _ _ (@HashMap.erase _ _ #6 #5 #4 #1) #0]
    [thm] Option.not_lt_none: [@LT.lt (Option #2) _ #0 (@none _)]
    [thm] Option.none_lt_some: [@LT.lt (Option #2) _ (@none _) (@some _ #0)]
    [thm] Option.not_mem_none: [@Membership.mem #1 (Option _) _ (@none _) #0]
    [thm] Option.not_some_le_none: [@LE.le (Option #2) _ (@some _ #0) (@none _)]
    [thm] Option.none_le: [@LE.le (Option #2) _ (@none _) #0]
    [thm] Array.getElem_mem: [@Membership.mem #3 (Array _) _ #2 (@getElem (Array _) `[Nat] _ _ _ #2 #1 #0)]
    [thm] getElem_indices_lt: [@getElem (HashMap #8 `[Nat] #6 #5) _ `[Nat] _ _ (@indices _ #7 _ _ #4) #3 _]
    [thm] HashMap.getElem_erase: [@getElem (HashMap #9 #8 #7 #6) _ _ _ _ (@HashMap.erase _ _ #7 #6 #5 #2) #1 #0]
    [thm] HashMap.getElem_insert: [@getElem (HashMap #10 #9 #8 #7) _ _ _ _ (@HashMap.insert _ _ #8 #7 #6 #3 #1) #2 #0]
    [thm] Array.getElem_set: [@getElem (Array #6) `[Nat] _ _ _ (@Array.set _ #5 #4 #2 #3) #1 #0]
    [thm] Array.getElem_pop: [@getElem (Array #3) `[Nat] _ _ _ (@Array.pop _ #2) #1 #0]
    [thm] Option.some_beq_some: [@BEq.beq (Option #3) _ (@some _ #1) (@some _ #0)]
    [thm] Option.some_beq_none: [@BEq.beq (Option #2) _ (@some _ #0) (@none _)]
    [thm] Option.none_beq_some: [@BEq.beq (Option #2) _ (@none _) (@some _ #0)]
    [thm] Option.none_beq_none: [@BEq.beq (Option #1) _ (@none _) (@none _)]
    [thm] HashMap.contains_erase: [@HashMap.contains #8 #7 #6 #5 (@HashMap.erase _ _ #6 #5 #4 #1) #0]
    [thm] HashMap.contains_insert: [@HashMap.contains #9 #8 #7 #6 (@HashMap.insert _ _ #7 #6 #5 #2 #0) #1]
    [thm] getElem_def: [@getElem (IndexMap #8 #7 #6 #5) _ _ _ _ #2 #1 #0]
    [thm] mem_indices_of_mem: [@Membership.mem #5 (IndexMap _ #4 #3 #2) _ #1 #0]
    [thm] getElem?_def: [@getElem? (IndexMap #7 #6 #5 #4) _ _ _ _ #1 #0]
  [cutsat] Assignment satisfying linear constraints
    [assign] i_1 := 0
    [assign] i_2 := 1
    [assign] (keys m_1).pop.size := 2
    [assign] (keys m_1).size := 3
    [assign] m_1.size := 3
    [assign] ((keys m_1).pop.set i_1 ((keys m_1).back ⋯) ⋯).size := 2
    [assign] (values m_1).size := 3
    [assign] (indices m_1)[a_1] := 0
    [assign] (((indices m_1).erase a_1).insert ((keys m_1).back ⋯) i_1)[a_2] := 0
    [assign] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).pop.size := 2
    [assign] ((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size := 3
    [assign] (indices m_1)[a_1] := 0
    [assign] (indices m_1)[a_2] := 1
    [assign] (indices m_1)[(keys m_1)[i_2]] := 1
    [assign] (indices m_1)[(keys m_1)[i_2]] := 1
  [ring] Rings
    [ring] Ring `Int`
      [basis] Basis
        [_] ↑(keys m_1).size + -1 * ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size = 0
        [_] ↑((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size + -1 * ↑m_1.size = 0
    [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
      [basis] Basis
        [_] ↑((keys m_1).size - 1) + -1 * ↑(m_1.size - 1) = 0
        [_] ↑(m_1.size - 1) + -1 * ↑(((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1) = 0
      [diseqs] Disequalities
        [_] ¬-1 * ↑(((keys m_1).set i_1 ((keys m_1).back ⋯) ⋯).size - 1) = 0
[grind] Issues
  [issue] type error constructing proof for WF
      when assigning metavariable ?a with ⏎
        i_2
      has type
        Nat
      of sort `Type` but is expected to have type
        α
      of sort `Type u`
  [issue] type error constructing proof for WF
      when assigning metavariable ?a with ⏎
        (indices m_1)[a_1]
      has type
        Nat
      of sort `Type` but is expected to have type
        α
      of sort `Type u`
  [issue] type error constructing proof for WF
      when assigning metavariable ?a with ⏎
        i_2
      has type
        Nat
      of sort `Type` but is expected to have type
        α
      of sort `Type u`
  [issue] type error constructing proof for WF
      when assigning metavariable ?a with ⏎
        (indices m_1)[a_1]
      has type
        Nat
      of sort `Type` but is expected to have type
        α
      of sort `Type u`
  [issue] type error constructing proof for WF
      when assigning metavariable ?a with ⏎
        (indices m_1)[(keys m_1)[i_2]]
      has type
        Nat
      of sort `Type` but is expected to have type
        α
      of sort `Type u`
  [issue] type error constructing proof for WF
      when assigning metavariable ?a with ⏎
        (indices m_1)[(keys m_1)[i_2]]
      has type
        Nat
      of sort `Type` but is expected to have type
        α
      of sort `Type u`
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] WF ↦ 16
    [thm] getElem?_neg ↦ 9
    [thm] getElem?_pos ↦ 9
    [thm] Array.getElem?_eq_none ↦ 5
    [thm] HashMap.contains_iff_mem ↦ 5
    [thm] Array.getElem?_pop ↦ 2
    [thm] Array.getElem?_set ↦ 2
    [thm] Array.getElem_pop ↦ 2
    [thm] Array.getElem_set ↦ 2
    [thm] Array.set_pop ↦ 2
    [thm] Array.size_pop ↦ 2
    [thm] Array.size_set ↦ 2
    [thm] getElem_indices_lt ↦ 2
    [thm] mem_indices_of_mem ↦ 2
    [thm] Array.back_eq_getElem ↦ 1
    [thm] size_keys ↦ 1
    [thm] size.eq_1 ↦ 1
    [thm] HashMap.contains_erase ↦ 1
    [thm] HashMap.contains_insert ↦ 1
    [thm] HashMap.getElem?_insert ↦ 1
    [thm] HashMap.getElem_insert ↦ 1
    [thm] HashMap.mem_erase ↦ 1
    [thm] HashMap.mem_insert ↦ 1
-/
#check_msgs in
-- ANCHOR: eraseSwap_init
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
-- ANCHOR_END: eraseSwap_init
stop discarding

instance [LawfulBEq α] : Singleton (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance [LawfulBEq α] : Insert (α × β) (IndexMap α β) :=
    ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance [LawfulBEq α] : LawfulSingleton (α × β) (IndexMap α β) :=
    ⟨fun _ => rfl⟩

-- ANCHOR: WF'
@[local grind] private theorem WF'
    (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
    m.keys[i] = a ↔ m.indices[a] = i := by
  have := m.WF i a
  grind
-- ANCHOR_END: WF'

-- ANCHOR: WF'ex
example {m : IndexMap α β} {a : α} {h : a ∈ m} :
  m.keys[m.indices[a]'h] = a := by grind
-- ANCHOR_END: WF'ex


/--
Erase the key-value pair with the given key,
moving the last pair into its place in the order.
If the key is not present, the map is unchanged.
-/
-- ANCHOR: eraseSwap
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
-- ANCHOR_END: eraseSwap

-- ANCHOR: Verification
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
-- ANCHOR_END: Verification

end IndexMap
