/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)
open Verso.Code.External (lit)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

#doc (Manual) "Homomorphism Annotations" =>
%%%
tag := "grind-hom"
%%%

::::keepEnv
```lean -show
axiom T : Type
axiom U : Type
variable {x y : T} [LE T] [LE U] [LT T] [LT U] [OfNat T n]
axiom T.toU : T → U
axiom f : T → T → T
axiom g : U → U → U
axiom h : Nat → U
variable {p : Prop} [Decidable p]
```

The {tactic}`grind` tactic can be extended to a new domain by defining a mapping from the new domain to one for which there already exists a dedicated solver.
This extension consists of a _homomorphism_: a structure-preserving translation from the new domain to the existing domain.
In other words, {tactic}`grind` can be made to reason about some new type {lean}`T` using an existing solver for {lean}`U` by defining a mapping {name}`T.toU` from {lean}`T` to {lean}`U` that satisfies certain properties.
Lean includes homomorphism rewrite rules for {name}`Fin`, {name}`BitVec`, {name}`UInt8`–{name}`UInt64`, {name}`USize`, {name}`Int8`–{name}`Int64`, and {name}`ISize` that rewrite them to {ref "cutsat"}[the `lia` solver's] domain.
Additionally, the inequality relations and byte-index bounds of {name}`String.Pos` are mapped, allowing {tactic}`grind` to reason about string positions.
Homomorphism rewriting is controlled by the `hom` flag to {tactic}`grind`, and it is enabled by default.

```lean -show
-- These tests check the claims made just above: that each listed
-- type really is a homomorphism source type in this version of
-- Lean, and that `Nat` is not.
--
-- Each example proves an equality of the source type from an
-- equality of the images. Only the `=`-injection licenses that
-- step, so the example fails if the type loses its rules.
--
-- The trace assertions confirm that the homomorphism engine is
-- what did the work, rather than some other solver. Two quirks:
-- `trace.grind.hom.pred` is registered as inherited, so it must
-- be switched off explicitly or `Fin` also reports its range
-- facts; and `substring := true` still anchors the `trace:`
-- prefix, so the expected text must be a prefix of the message.

-- `Fin` and `BitVec` inject directly into `Nat`, so the negated
-- goal is the only thing translated.
set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] ¬a = b -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Fin 8) (h : a.val = b.val) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] ¬a = b -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : BitVec 8) (h : a.toNat = b.toNat) : a = b := by
  grind

-- The fixed-width integer types inject through `BitVec`, so the
-- hypothesis is translated as well as the goal.
set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : UInt8) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : UInt16) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : UInt32) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : UInt64) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : USize) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Int8) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Int16) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Int32) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : Int64) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] a.toBitVec = b.toBitVec -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (a b : ISize) (h : a.toBitVec = b.toBitVec) : a = b := by
  grind

-- `String.Pos` injects via its offset, then the byte index.
set_option trace.grind.hom.pred false in
/-- trace: [grind.hom] p.offset = q.offset -/
#guard_msgs (substring := true) in
set_option trace.grind.hom true in
example (s : String) (p q : s.Pos) (h : p.offset = q.offset) :
    p = q := by
  grind

-- `Nat` is not a source type: `cutsat` handles it natively, so
-- unlike the types above, these still succeed with `-hom`.
example (a b c : Nat) : a + (b + c) = (c + a) + b := by grind -hom
example (a b : Nat) (h : a ≤ b) (h₂ : b ≤ a) : a = b := by
  grind -hom
```


To use the feature at all, the mapping should be injective with respect to equality.
That is, given {lean}`x` and {lean}`y` of type {lean}`T`, it should be the case that {lean}`x = y` is logically equivalent to {lean}`x.toU = y.toU`.
Adding the {attr}`grind hom` attribute to a suitable injectivity theorem activates the mapping feature.

To be useful, the mapping should translate operations of interest on {lean}`T` into operations in {lean}`U` that are supported by {tactic}`grind`'s solvers.
The {attr}`grind hom` attribute can be added to the following kinds of theorems:
* To translate {lean}`f` into {lean}`g`, it should be the case that {lean}`(f x y).toU = g x.toU y.toU`.
* Ordering relations can be translated by showing that {lean}`x ≤ y ↔ x.toU ≤ y.toU` and {lean}`x < y ↔ x.toU < y.toU`.
* Numeric literals can be translated by providing a theorem that translates them into a function into {lean}`U`.
  This is done by adding the {attr}`grind hom` attribute to a theorem of the form {lean}`(OfNat.ofNat n : T).toU = h n`.
* Conditionals can be translated by providing a theorem that shows that {lean}`(if p then x else y).toU = if p then x.toU else y.toU`.

Additional facts about the range of the mapping can be provided by tagging lemmas with {attr}`grind hom_pred`.
This is typically used to restrict the range, such as by asserting that the target of {name}`Fin.val` is less than the {name}`Fin`'s bound.
These lemmas are instantiated when the constants that they mention are used in terms that are not themselves rewritten by {attr}`grind hom` rules.
::::

Homomorphism lemmas are applied prior to adding statements to the shared “whiteboard,” rather than repeatedly while the solvers run.
This can be much more efficient.
Because the mapping is injective, _disequality_ of terms in the new type implies disequality in the solver's domain, so {tactic}`grind`'s strategy of negating statements to derive a contradiction can be applied directly even without having a bijection.
Because they run only very early in the process, homomorphism lemmas are applied without a discharger.
This means that they do not permit conditional rewrites that require further proving (though rewrites can still be made conditional on an instance-implicit hypothesis, and propositional hypotheses are permitted when they are fully determined by the left-hand side).


When debugging, homomorphism rewrites can be observed by setting {option}`trace.grind.hom` or {option}`trace.grind.hom.pred` to `true`.

{optionDocs trace.grind.hom}

{optionDocs trace.grind.hom.pred}

:::example "Very Small Integers"

Tiny numbers (that is, whole numbers from zero to three) can be represented using a four-constructor inductive type:

```lean
inductive Tiny where
  | zero
  | one
  | two
  | three
```

```lean
namespace Tiny
```

A few instances allow numeric literals to be used for {name}`Tiny`:
```lean
instance : Zero Tiny where
  zero := .zero

instance : One Tiny where
  one := .one

instance : OfNat Tiny 2 where
  ofNat := .two

instance : OfNat Tiny 3 where
  ofNat := .three
```

They can be converted to and from {name}`Nat`:
```lean
def toNat : Tiny → Nat
  | .zero => 0
  | .one => 1
  | .two => 2
  | .three => 3

def ofNat : (n : Nat) → n < 4 → Tiny
  | 0, _ => 0
  | 1, _ => 1
  | 2, _ => 2
  | 3, _ => 3
```

And they can be compared with each other:
```lean
instance : LE Tiny where
  le x y := x.toNat ≤ y.toNat

instance : LT Tiny where
  lt x y := x.toNat < y.toNat
```

{name}`Tiny.toNat` is an injective mapping:
```lean
@[grind hom]
theorem eq_iff_toNat_eq (x y : Tiny) : x = y ↔ x.toNat = y.toNat := by
  cases x <;> cases y <;> simp [toNat]
```

Similarly, because the {inst}`LE Tiny` and {inst}`LT Tiny` instances are defined in terms of those for {name}`Nat`, they are logically equivalent:
```lean
@[grind hom]
theorem le_iff_toNat_le (x y : Tiny) : x ≤ y ↔ x.toNat ≤ y.toNat := by
  rfl
@[grind hom]
theorem lt_iff_toNat_lt (x y : Tiny) : x < y ↔ x.toNat < y.toNat := by
  rfl
```

Whenever a {name}`Tiny` number is converted to a {name}`Nat`, the resulting number is less than four.
Adding a {attr}`grind hom_pred` attribute to the proof causes {tactic}`grind` to include this knowledge when {name}`Tiny.toNat` is used in a term that is added to the “whiteboard” but not rewritten by a {attr}`grind hom` rule:
```lean
@[grind hom_pred]
theorem toNat_lt_4 (x : Tiny) : x.toNat < 4 := by
  cases x <;> simp [toNat]
```

A finite type like {name}`Tiny` must decide the meaning of operations that go outside its bounds.
In this case, {name}`Tiny.succ` and the addition operator are defined such that they truncate; modular arithmetic would be another valid implementation.
```lean
def succ (x : Tiny) : Tiny :=
  match x with
  | .zero => .one
  | .one => .two
  | .two => .three
  | .three => .three

instance : Add Tiny where
  add
  | .zero, y => y
  | .one, y => y.succ
  | .two, y => y.succ.succ
  | .three, y => y.succ.succ.succ
```

Natural numbers do not exhibit truncating addition, so it seems natural to require that the result of the addition does not truncate prior to mapping it to natural number addition.
However, this results in an error:
```lean +error (name := homNoH)
@[grind hom]
theorem toNat_add_lt_4_eq_add (x y : Tiny)
    (h : x.toNat + y.toNat < 4) :
    (x + y).toNat = x.toNat + y.toNat := by
  cases x <;> cases y <;> simp [toNat] at h <;> rfl
```
```leanOutput homNoH
invalid `[grind hom]` theorem, `toNat_add_lt_4_eq_add` is conditional: hypothesis
  x.toNat + y.toNat < 4
is not determined by the left-hand side and would have to be discharged when the rule is applied. Homomorphism rules must be unconditional; use E-matching attributes such as `[grind =]` or `[grind →]` for conditional theorems
```
This is because conditional rewrites are disallowed; the homomorphism feature is used too early in {tactic}`grind` to support them.

Instead, addition of tiny numbers can be mapped to truncating addition of natural numbers:
```lean
@[grind hom]
theorem toNat_add_eq_add (x y : Tiny) :
    (x + y).toNat = min (x.toNat + y.toNat) 3 := by
  cases x <;> cases y <;> rfl
```
Given these definitions, we might expect the following example to succeed, but it does not:
```lean +error (name := noLits)
example : (2 : Tiny) + (1 : Tiny) = (3 : Tiny) := by grind
```
Examining {tactic}`grind`'s output, the problem is that it does not successfully register the contradiction that arises from the fact that {lean}`(2 : Tiny) + (1 : Tiny) = (3 : Tiny)` is negated.
This is because the rewriting process does not rewrite literals like {lean (type := "Tiny")}`2` (that is, {lean}`OfNat.ofNat (α := Tiny) 2`), which are left alone:
```leanOutput noLits
`grind` failed
case grind.1
h : ¬2 + 1 = 3
h_1 : toNat 1 + toNat 2 ≤ 3
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [assoc] Operator `min`

[grind] Diagnostics
```

Setting {option}`trace.grind.hom` to `true` demonstrates the rewriting performed by the homomorphism lemmas, as well as the added {attr}`grind hom_pred` facts:
```lean +error (name := noLits')
set_option trace.grind.hom true in
example : (2 : Tiny) + (1 : Tiny) = (3 : Tiny) := by grind
```
```leanOutput noLits'
[grind.hom] ¬2 + 1 = 3
    ===>
    ¬min (toNat 2 + toNat 1) 3 = toNat 3
[grind.hom.pred] toNat 1 < 4
[grind.hom.pred] toNat 2 < 4
[grind.hom.pred] toNat 3 < 4
```

This can be fixed by providing rules for each supported literal:
```lean
@[grind hom]
theorem toNat_zero_eq_zero : (0 : Tiny).toNat = 0 := by simp [toNat]
@[grind hom]
theorem toNat_one_eq_one : (1 : Tiny).toNat = 1 := by simp [toNat]
@[grind hom]
theorem toNat_two_eq_two : (2 : Tiny).toNat = 2 := by simp [toNat]
@[grind hom]
theorem toNat_three_eq_three : (3 : Tiny).toNat = 3 := by simp [toNat]
```

After this, the proof is successful, as is one that exercises the truncation behavior of addition:
```lean
example : (2 : Tiny) + (1 : Tiny) = (3 : Tiny) := by grind

example : (3 : Tiny) + (3 : Tiny) = (3 : Tiny) := by grind
```

Enabling {option}`trace.grind.hom` reveals that the {attr}`grind hom_pred` rule no longer fires, because all subterms of type {name}`Tiny` are now rewritten:
```lean (name := withLits)
set_option trace.grind.hom true in
example : (2 : Tiny) + (1 : Tiny) = (3 : Tiny) := by grind
```
```leanOutput withLits
[grind.hom] ¬2 + 1 = 3
    ===>
    ¬min (2 + 1) 3 = 3
```
:::




:::example "Difference Lists" (tag := "difference-lists-hom")

Difference lists, in which lists are represented as functions, {ref "difference-lists-ac" (domain := Manual.examples)}[provide an associative append operator].
Reasoning about them as lists using {attr}`grind hom` is very appealing; however, the default representation as a function doesn't have the right injectivity property:
```lean
namespace NotInj
def DList α := List α → List α
def DList.toList (xs : DList α) : List α := xs []

theorem DList.not_toList_inj :
    (∀ (α : Type) (xs ys : DList α), xs = ys ↔ xs.toList = ys.toList) →
    False := by
  intro h
  let l1 : DList Nat := fun xs => 1 :: 2 :: xs
  let l2 : DList Nat := fun _ => [1, 2]
  have : l1 ≠ l2 := by
    intro h
    have := congrFun h [3]
    simp [l1, l2] at this
  have toList_eq : l1.toList = l2.toList := rfl
  have := h Nat l1 l2 |>.mpr toList_eq
  contradiction

end NotInj
```

In other words, Lean's function type includes functions that aren't really difference lists.
To use {attr}`grind hom` with difference lists, they need more structure to rule out these counterexamples:
```lean
@[ext]
structure DList α where
  appendTail : List α → List α
  wf : ∀ xs, appendTail xs = appendTail [] ++ xs

def DList.toList (xs : DList α) : List α :=
  xs.appendTail []
```
This additional well-formedness property rules out the invalid cases:
```lean
theorem DList.ext_toList (xs ys : DList α) (h : xs.toList = ys.toList) :
    xs = ys := by
  have : xs.appendTail = ys.appendTail := by
    funext zs
    rw [xs.wf, ys.wf]
    exact congrArg (· ++ zs) h
  cases xs; cases ys; simp_all

@[grind hom]
theorem DList.toList_inj (xs ys : DList α) :
    xs = ys ↔ xs.toList = ys.toList := by
  constructor
  . intro h; rw [h]
  . apply DList.ext_toList
```

The difference list operators can now be translated to list operators:
```lean
def DList.nil : DList α where
  appendTail xs := xs
  wf := by simp

@[grind hom]
theorem DList.nil_toList : (.nil : DList α).toList = [] := by
  simp_all [nil, toList]

def DList.cons (x : α) (xs : DList α) : DList α where
  appendTail ys := x :: xs.appendTail ys
  wf ys := by
    simp only [List.cons_append, List.cons.injEq, true_and]
    apply xs.wf

@[grind hom]
theorem DList.cons_toList :
    (DList.cons x xs).toList = x :: xs.toList := by
  simp [cons, toList]

instance : Append (DList α) where
  append xs ys := {
    appendTail := xs.appendTail ∘ ys.appendTail
    wf zs := by
      have := xs.wf
      have := ys.wf
      grind
  }

@[grind hom]
theorem DList.append_toList {xs ys : DList α} :
    (xs ++ ys).toList = xs.toList ++ ys.toList := by
  apply xs.wf
```

Now, {tactic}`grind` can reason about properties of difference lists, as well as conversions between difference lists and ordinary lists:

```lean
variable (a b c : DList Nat)

example : (a ++ b) ++ c = a ++ (b ++ c) := by grind

example : a ++ .nil = a := by grind

example : .nil ++ a = a := by grind

example (h₁ : a.toList = [1,2]) (h₂ : b.toList = [3]) :
    (a ++ b).toList = [1,2,3] := by grind

example (h : a.toList = []) : a = .nil := by grind
```

```lean -show
-- The examples fail without hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : (a ++ b) ++ c = a ++ (b ++ c) := by grind -hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : a ++ .nil = a := by grind -hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : .nil ++ a = a := by grind -hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example (h₁ : a.toList = [1,2]) (h₂ : b.toList = [3]) :
    (a ++ b).toList = [1,2,3] := by grind -hom
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example (h : a.toList = []) : a = .nil := by grind -hom
```

Even more powerfully, additional {name}`List` lemmas can be used explicitly to reason about difference lists:

```lean
example (h : a ++ b = a ++ c) : b = c := by
  grind [List.append_cancel_left]

example (h : a ++ c = b ++ c) : a = b := by
  grind [List.append_cancel_right]

example (h : a ++ b = .nil) : a = .nil := by
  grind [List.append_eq_nil_iff]
```
:::
