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

#doc (Manual) "Associativity and Commutativity" =>
%%%
tag := "grind-ac"
%%%

When an operator is associative, {tactic}`grind` can efficiently rewrite terms that contain the operator to a normal form, making it easier to prove equalities that involve the operator.
This rewriting can make use of further facts about the operator, such as the fact that it is commutative or idempotent, or that certain values are identities.
Rewriting occurs both when adding terms to the “whiteboard” and in response to facts added by other solvers.
This solver is controlled using the `ac` flag, and it is on by default.
The `acSteps` option, which defaults to `1000`, controls how many `ac` rewriting steps are allowed.

:::example "Strings"
The `ac` solver can reason about strings.
It's common for string-processing code to compute a prefix, and then later append further values.
Using `ac`, these can be reasoned about more conveniently:
```lean
example (dir file p) (h : dir ++ "/" = p) :
    dir ++ ("/" ++ file) = p ++ file := by grind
```

```lean -show +error
-- To make sure it's AC solving this
example (dir file p) (h : dir ++ "/" = p) :
    dir ++ ("/" ++ file) = p ++ file := by grind -ac
```
:::

# Normal Forms

:::leanSection
```lean -show
variable {α : Type u} {op : α → α → α} [Std.Associative op] {u x y z : α}
```

The normal forms used by the `ac` solver depend on the properties that have been registered for the operator in question.

: Associativity

  Associative operators are normalized by reducing nested trees of the operator to lists of operands.
  If {lean}`op` is associative, then the normal form of both {lean}`op (op x y) z` and {lean}`op x (op y z)` is {lean}`[x, y, z]`.

: Commutativity

  Operators that are associative and commutative are normalized by sorting the operand lists.
  If {lean}`op` is associative and commutative, then the normal form of both {lean}`op z (op x y)` and {lean}`op (op x z) y` is {lean}`[x, y, z]`.
  In other words, the normal form is a multiset.

: Idempotence

  If the operator is idempotent, then runs of duplicate elements are collapsed in the operand list.
  If {lean}`op` is associative and idempotent, then the normal form of {lean}`op x (op x y)` is {lean}`[x, y]`, but the normal form of {lean}`op (op x y) x` is still {lean}`[x, y, x]`.
  This collapsing occurs after sorting the list if the operator is commutative, so if {lean}`op` is associative, commutative, and idempotent, then the normal form of {lean}`op (op x y) x` is also {lean}`[x, y]`.
  In other words, the normal form of an associative, commutative, and idempotent operator is a set.

: Identities

  If the operator has a unit, then it is removed from the normal form.
  That is, if {lean}`u` is a unit of the associative operator {lean}`op`, then the normal form of {lean}`op x (op u y)` is {lean}`[x, y]`.

:::


# Extension

The `ac` solver can be extended to support new operators by providing an instance of {name}`Std.Associative` for the operator.
Instances of {name}`Std.Commutative`, {name}`Std.IdempotentOp`, and {name}`Std.LawfulIdentity` further extend its capabilities by identifying more terms.

{docstring Std.Associative}

{docstring Std.Commutative}

{docstring Std.IdempotentOp}

{docstring Std.LawfulIdentity}

While extending the {lit}`ac` solver, it can be useful to observe its operation.
The option {option}`trace.grind.ac`, as well as the more specific options {option}`trace.grind.ac.assert`, {option}`trace.grind.ac.internalize`, and {option}`trace.grind.ac.basis`, can be used to observe its internal behavior.
In particular, {option}`trace.grind.ac.assert` displays the results of normalization that are added to the “whiteboard.”

{optionDocs trace.grind.ac}

{optionDocs trace.grind.ac.assert}

{optionDocs trace.grind.ac.internalize}

{optionDocs trace.grind.ac.basis}

:::example "Idempotence and Identity"

{name}`Flags` tracks a set of Boolean flags, each of which corresponds to a bit position.
Each flag is either set or clear, and all flags are clear when the bit value is {lean}`0`.
The union of two sets of flags is found by taking the bit-wise OR of their bit representations.
```lean
structure Flags where
  bits : Nat

namespace Flags

def union (a b : Flags) : Flags := ⟨a.bits ||| b.bits⟩
def none : Flags := ⟨0⟩

```
The union operation on flags is associative, commutative, and idempotent, and {name}`Flags.none` is an identity:
```lean
instance : Std.Associative union where
  assoc x y z := by simp only [union, mk.injEq]; grind
instance : Std.Commutative union where
  comm x y := by simp only [union, mk.injEq]; grind
instance : Std.IdempotentOp union where
  idempotent x := by simp [union]
instance : Std.LawfulIdentity union none where
  left_id a := by simp [union, none]
  right_id a := by simp [union, none]
```
With these instances, the `ac` solver can dispatch all of the following goals.
In the second example, idempotency can only be used due to commutativity, because the two identical arguments are not adjacent in the original term.
```lean
example : union a (union b c) = union (union c a) b := by grind
example : union (union a b) a = union a b := by grind
example : union a none = a := by grind
example :
    union (union a b) (union none (union b c))
      = union a (union b c) := by
  grind
```
The negated normal-form equality that is added to the context can be seen using {option}`trace.grind.ac.assert`:
```lean (name := traceAc)
set_option trace.grind.ac.assert true in
example : union (union a b) a = union a (union b none) := by grind
```
```leanOutput traceAc
[grind.ac.assert] a.union b ≠ a.union b
```

```lean -show
-- check solver
/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : union a (union b c) = union (union c a) b := by grind -ac

/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : union (union a b) a = union a b := by grind -ac

/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example : union a none = a := by grind -ac

/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example :
    union (union a b) (union none (union b c))
      = union a (union b c) := by grind -ac

```

:::

::::example "Difference Lists" (tag := "difference-lists-ac")

A {deftech}_difference list_ is a clever representation of lists as functions that avoids the quadratic overhead of appending to the end of lists.
Because Lean supports {ref "Array"}[efficient arrays], they are typically not useful in day-to-day code, but they effectively demonstrate how to extend the `ac` solver.

:::leanSection
```lean -show
variable {xs ys : List α}
```
A difference list is a function from lists to lists.
The list {lean}`xs` is represented by a function that, when applied to {lean}`ys`, returns {lean}`xs ++ ys`.
:::

```lean
def DList α := List α → List α
```

The empty list is the identity function.
An item is added to the beginning of a list by creating a function that adds the element.
Appending two lists is function composition.
```lean
def DList.empty : DList α := id

def DList.cons (x : α) (xs : DList α) : DList α :=
  fun ys => (x :: xs ys)

instance : Append (DList α) where
  append xs ys := xs ∘ ys
```

The proofs that appending two difference lists is associative and that the empty difference list is a left and right identity of the append operator succeed by reflexivity because definitional equality includes the β and η laws for functions:
```lean
instance : Std.Associative (α := DList α) (· ++ ·) where
  assoc xs ys zs := by rfl

instance : Std.LawfulIdentity (α := DList α) (· ++ ·) .empty where
  left_id xs := by rfl
  right_id xs := by rfl
```

Given these instances, {tactic}`grind` can dispatch many proofs.
```lean
variable (a b c d x y : DList Nat)
```

Because append is associative, terms can be rebracketed and units vanish:
```lean
example : ((a ++ b) ++ c) ++ d = a ++ (b ++ (c ++ d)) := by grind

example : (a ++ .empty) ++ (.empty ++ b) = a ++ b := by grind

example : (.empty ++ .empty : DList Nat) = .empty := by grind
```

While {ref "simp-rewrites"}[simplification lemmas] could easily solve those problems, {tactic}`grind`'s `ac` solver allows a greater degree of flexibility.
To use the hypotheses in these examples, it would not be sufficient to just rewrite goals and hypotheses to a normal form that reassociated an associative operator to the right:
```lean
example (h : a ++ b = x) : a ++ (b ++ c) = x ++ c := by grind

example (h : a ++ b = x) :
    (a ++ .empty) ++ (b ++ c) = x ++ c := by grind

example (h₁ : a ++ b = x) (h₂ : x ++ c = y) :
    a ++ (b ++ c) = y := by grind
```
Because appending difference lists is not commutative, order still matters:
```lean +error (name := grindErr)
example : a ++ b = b ++ a := by grind
```
```leanOutput grindErr
`grind` failed
case grind
a b c d x y : DList Nat
h : ¬a ++ b = b ++ a
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [assoc] Operator `HAppend.hAppend`
```
::::

# Exclusions

The `ac` solver does not apply to some built-in operators, namely {name}`And`, {name}`Or`, and {name}`Iff`.
They are better served by other {tactic}`grind` features.
When the operand type has {name}`Lean.Grind.CommRing` and/or {name}`Lean.Grind.CommSemiring` instances, `ac` omits its rules for certain operators that are usually better solved by {ref "grind-ring"}[the `ring` solver], namely `+`, `-`, `*`, `/`, and `^`.

```lean -show
-- `And` and `Or` have `Std.Associative` instances, so the exclusion is
-- what stops the `ac` solver from claiming them.
#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (a b c : Prop) : (a ∧ b) ∧ c ↔ a ∧ (b ∧ c) := by grind

#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (a b c : Prop) : (a ∨ b) ∨ c ↔ a ∨ (b ∨ c) := by grind

-- Likewise `+` and `*`, which are left to the arithmetic solvers.
#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (a b c : Nat) : a + (b + c) = (c + a) + b := by grind

#guard_msgs in
set_option trace.grind.debug.ac.op true in
example (a b c : Nat) : a * (b * c) = (c * a) * b := by grind
```
