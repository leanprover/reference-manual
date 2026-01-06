/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Annotating Libraries for `grind`" =>
%%%
tag := "grind-annotation"
%%%

To use {tactic}`grind` effectively with a library, it must be annotated by applying the {attr}`grind` attribute to suitable lemmas or declaring {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern`s.
These annotations direct {tactic}`grind`'s selection of theorems, which lead to further facts on the metaphorical whiteboard.
With too few annotations, {tactic}`grind` will fail to use the lemmas; with too many, it may become slow or it fail due to exhausting resource limitations.
Annotations should generally be conservative: only add an annotation if you expect that {tactic}`grind` should _always_ instantiate the theorem once the patterns are matched.

# Simp Lemmas

Typically, many theorems that are annotated with {attrs}`@[simp]` should also be annotated with {attrs}`@[grind =]`.
One significant exception is that typically we avoid having {attrs}`@[simp]` theorems that introduce an {keywordOf Lean.Parser.Term.if}`if` on the right hand side, instead preferring a pair of theorems with the positive and negative conditions as hypotheses.
Because {tactic}`grind` is designed to perform case splitting, it is generally better to instead annotate the single theorem introducing the {keywordOf Lean.Parser.Term.if}`if` with {attrs}`@[grind =]`.

Besides using {attrs}`@[grind =]` to encourage {tactic}`grind` to perform rewriting from left to right, you can also use {attrs}`@[grind _=_]` to “saturate”, allowing bidirectional rewriting whenever either side is encountered.

# Backwards and Forwards Reasoning

:::paragraph
Use {attrs}`@[grind ←]` (which generates patterns from the conclusion of the theorem) for backwards reasoning theorems, i.e. theorems that should be tried when their conclusion matches a goal.
Some examples of theorems in the standard library that are annotated with {attr}`grind ←` are:
* ```signature
  Array.not_mem_empty (a : α) : ¬ a ∈ #[]
  ```
* ```signature
  Array.getElem_filter {xs : Array α} {p : α → Bool} {i : Nat} (h : i < (xs.filter p).size) :
    p (xs.filter p)[i]
  ```
* ```signature
  List.Pairwise.tail : ∀ {l : List α} (h : Pairwise R l), Pairwise R l.tail
  ```
In each case, the lemma is relevant when its conclusion matches a proof goal.
:::

:::paragraph
Use {attrs}`@[grind →]` (which generates patterns from the hypotheses) for forwards reasoning theorems,
i.e. where facts should be propagated from existing facts on the whiteboard.
Some examples of theorems in the standard library that are annotated with {attr}`grind →` are:
* ```signature
  List.getElem_of_getElem? {l : List α} : l[i]? = some a → ∃ h : i < l.length, l[i] = a
  ```
* ```signature
  Array.mem_of_mem_erase [BEq α] {a b : α} {xs : Array α} (h : a ∈ xs.erase b) : a ∈ xs
  ```
* ```signature
  List.forall_none_of_filterMap_eq_nil (h : filterMap f xs = []) : ∀ x ∈ xs, f x = none
  ```
In these cases, the theorems' assumptions determine when they are relevant.
:::

There are many uses for custom patterns created with the {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern` command.
One common use is to introduce inequalities about terms, or membership propositions.

:::keepEnv
```lean -show
section
def count := @Array.count
theorem countP_le_size [BEq α] {a : α} {xs : Array α} : count a xs ≤ xs.size := Array.countP_le_size
notation "..." => countP_le_size
```

We might have
```lean
variable [BEq α]

theorem count_le_size {a : α} {xs : Array α} : count a xs ≤ xs.size :=
  ...

grind_pattern count_le_size => count a xs
```
```lean -show
variable {a : α} {xs : Array α}
```
which will register this inequality as soon as a {lean}`count a xs` term is encountered (even if the problem has not previously involved inequalities).

```lean -show
end
```
:::

We can also use multi-patterns to be more restrictive, e.g. only introducing an inequality about sizes if the whiteboard already contains facts about sizes:
```lean
theorem size_pos_of_mem {xs : Array α} (h : a ∈ xs) : 0 < xs.size :=
  sorry

grind_pattern size_pos_of_mem => a ∈ xs, xs.size
```
:::leanSection
```lean -show
variable {a : α} {xs : Array α}
```
Unlike a {attrs}`@[grind →]` attribute, which would cause this theorem to be instantiated whenever {lean}`a ∈ xs` is encountered, this pattern will only be used when {lean}`xs.size` is already on the whiteboard.
(Note that this grind pattern could also be produced using the {attrs}`@[grind <=]` attribute, which looks at the conclusion first, then backwards through the hypotheses to select patterns.
On the other hand, {attrs}`@[grind →]` would select only {lean}`a ∈ xs`.)
:::


::::keepEnv
:::leanSection
```lean -show
axiom R : Type
axiom sin : R → R
axiom cos : R → R
@[instance] axiom instAdd : Add R
@[instance] axiom instOfNatR : OfNat R n
@[instance] axiom instHPowR : HPow R Nat R
variable {x : R}
axiom sin_sq_add_cos_sq' : sin x ^ 2 + cos x ^ 2 = 1
notation "..." => sin_sq_add_cos_sq'
```
In Mathlib we might want to enable polynomial reasoning about the sine and cosine functions,
and so add a custom grind pattern
```lean
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 := ...

grind_pattern sin_sq_add_cos_sq => sin x, cos x
```
which will instantiate the theorem as soon as *both* {lean}`sin x` and {lean}`cos x` (with the same {lean}`x`) are encountered.
This theorem will then automatically enter the Gröbner basis module, and be used to reason about polynomial expressions involving both {lean}`sin x` and {lean}`cos x`.
One both alternatively, more aggressively, write two separate grind patterns so that this theorem instantiated when either {lean}`sin x` or {lean}`cos x` is encountered.
:::
::::
