--ANCHOR: imports
import Std.Data.HashMap
--ANCHOR_END: imports
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




-- ANCHOR: IndexMap
open Std

structure IndexMap
    (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  private indices : HashMap α Nat
  private keys : Array α
  private values : Array β
  private size_keys' : keys.size = values.size := by grind
  private WF : ∀ (i : Nat) (a : α),
    keys[i]? = some a ↔ indices[a]? = some i := by grind
-- ANCHOR_END: IndexMap


-- ANCHOR: variables
namespace IndexMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]
variable {m : IndexMap α β} {a : α} {b : β} {i : Nat}
-- ANCHOR_END: variables

-- ANCHOR: size
@[inline] def size (m : IndexMap α β) : Nat :=
  m.values.size

@[local grind =] private theorem size_keys : m.keys.size = m.size :=
  m.size_keys'

@[local grind =] private theorem size_values : m.values.size = m.size := rfl
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

-- ANCHOR: Membership
@[inline] def contains (m : IndexMap α β)
    (a : α) : Bool :=
  m.indices.contains a

instance : Membership α (IndexMap α β) where
  mem m a := a ∈ m.indices

instance {m : IndexMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.indices))
-- ANCHOR_END: Membership

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
h_1 : m.size ≤ m.indices[a]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] a ∈ m
    [prop] m.size ≤ m.indices[a]
  [eqc] True propositions
    [prop] m.size ≤ m.indices[a]
    [prop] a ∈ m
  [eqc] Equivalence classes
    [eqc] {Membership.mem, fun m a => a ∈ m}
  [ematch] E-matching patterns
    [thm] getElem?_pos: [@getElem #8 #7 #6 #5 _ #2 #1 _]
    [thm] HashMap.contains_iff_mem: [@Membership.mem #5 (HashMap _ #4 #3 #2) _ #1 #0]
  [cutsat] Assignment satisfying linear constraints
    [assign] m.size := 0
    [assign] m.indices[a] := 0
-/
#check_msgs in
-- ANCHOR: getElem_indices_lt_init
theorem getElem_indices_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.indices[a] < m.size := by
  grind
-- ANCHOR_END: getElem_indices_lt_init
stop discarding

-- ANCHOR: mem_indices
@[local grind _=_] private theorem mem_indices
    {m : IndexMap α β} {a : α} :
    a ∈ m.indices ↔ a ∈ m := Iff.rfl
-- ANCHOR_END: mem_indices

-- ANCHOR: getFindIdx
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
-- ANCHOR_END: getFindIdx

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
info: Try these:
  [apply] [grind
    .] for pattern: [@LE.le `[Nat] `[instLENat] ((@getElem (HashMap #8 `[Nat] #6 #5) _ `[Nat] _ _ (@indices _ #7 _ _ #4) #3 #0) + 1) (@size _ _ _ _ #4)]
  [apply] [grind →] for pattern: [LawfulBEq #8 #6, LawfulHashable _ _ #5, @Membership.mem _ (IndexMap _ #7 _ _) _ #4 #3]
-/
#check_msgs in
-- ANCHOR: getElem_indices_lt_attr
attribute [local grind] getElem_indices_lt
-- ANCHOR_END: getElem_indices_lt_attr
end

-- ANCHOR: getElem_indices_lt_pattern
grind_pattern getElem_indices_lt => m.indices[a]
-- ANCHOR_END: getElem_indices_lt_pattern

-- ANCHOR: local_grind_size
attribute [local grind] size
-- ANCHOR_END: local_grind_size

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
-- ANCHOR_END: getElem_local

-- ANCHOR: LawfulGetElem
instance : LawfulGetElem (IndexMap α β) α β (fun m a => a ∈ m) where
  getElem?_def := by grind
  getElem!_def := by grind
-- ANCHOR_END: LawfulGetElem

-- ANCHOR: insert
@[inline] def insert (m : IndexMap α β) (a : α) (b : β) : IndexMap α β :=
  match h : m.indices[a]? with
  | some i =>
    { indices := m.indices
      keys    := m.keys.set i a
      values  := m.values.set i b }
  | none =>
    { indices := m.indices.insert a m.size
      keys    := m.keys.push a
      values  := m.values.push b }
-- ANCHOR_END: insert

discarding
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

instance : Singleton (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : IndexMap α β).insert a b⟩

instance : Insert (α × β) (IndexMap α β) :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (IndexMap α β) :=
  ⟨fun _ => rfl⟩

-- ANCHOR: WF'
@[local grind .]
private theorem WF' (i : Nat) (a : α) (h₁ : i < m.keys.size) (h₂ : a ∈ m) :
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

-- TODO: similarly define `eraseShift`, etc.

-- ANCHOR: Verification
/-! ### Verification theorems (not exhaustive) -/

@[grind =]
theorem mem_insert (m : IndexMap α β) (a a' : α) (b : β) :
    a' ∈ m.insert a b ↔ a' = a ∨ a' ∈ m := by
  grind +locals

@[grind =]
theorem getElem_insert (m : IndexMap α β) (a a' : α) (b : β) (h : a' ∈ m.insert a b) :
    (m.insert a b)[a'] = if h' : a' == a then b else m[a'] := by
  grind +locals

theorem findIdx_lt (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.findIdx a h < m.size := by
  grind +locals

grind_pattern findIdx_lt => m.findIdx a h

@[grind =]
theorem findIdx_insert_self (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).findIdx a = if h : a ∈ m then m.findIdx a else m.size := by
  grind +locals

@[grind =]
theorem findIdx?_eq (m : IndexMap α β) (a : α) :
    m.findIdx? a = if h : a ∈ m then some (m.findIdx a h) else none := by
  grind +locals

@[grind =]
theorem getIdx_findIdx (m : IndexMap α β) (a : α) (h : a ∈ m) :
    m.getIdx (m.findIdx a) = m[a] := by grind +locals

omit [LawfulBEq α] [LawfulHashable α] in
@[grind =]
theorem getIdx?_eq (m : IndexMap α β) (i : Nat) :
    m.getIdx? i = if h : i < m.size then some (m.getIdx i h) else none := by
  grind +locals

private theorem getElem_keys_mem {m : IndexMap α β} {i : Nat} (h : i < m.size) :
    m.keys[i] ∈ m := by
  have : m.indices[m.keys[i]]? = some i := by grind
  grind

local grind_pattern getElem_keys_mem => m.keys[i]

theorem getElem?_eraseSwap (m : IndexMap α β) (a a' : α) :
    (m.eraseSwap a)[a']? = if a' == a then none else m[a']? := by
  grind +locals

@[grind =]
theorem mem_eraseSwap (m : IndexMap α β) (a a' : α) :
    a' ∈ m.eraseSwap a ↔ a' ≠ a ∧ a' ∈ m := by
  grind +locals

theorem getElem_eraseSwap (m : IndexMap α β) (a a' : α) (h : a' ∈ m.eraseSwap a) :
    (m.eraseSwap a)[a'] = m[a'] := by
  grind +locals
-- ANCHOR_END: Verification

end IndexMap
