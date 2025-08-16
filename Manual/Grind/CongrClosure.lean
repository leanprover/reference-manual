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

#doc (Manual) "Congruence Closure" =>
%%%
tag := "congruence-closure"
%%%

:::leanSection
```lean -show
variable {a a' : α} {b b' : β} {f : α → β → γ}
```
{deftech}_Congruence closure_ maintains equivalence classes of terms under the reflexive, symmetric, and transitive closure of “is equal to” _and_ the rule that equal arguments yield equal function results.
Formally, if {lean}`a = a'` and {lean}`b = b'`, then {lean}`f a b = f a' b'` is added.
The algorithm merges equivalence classes until a fixed point is reached.
If a contradiction is discovered, then the goal can be closed immediately.
:::

::::leanSection
```lean -show
variable {t₁ t₂ : α} {h : t₁ = t₂} {a : α} {f : α → β} {g : β → β}
```
:::paragraph
Using the analogy of the shared whiteboard:

1. Every hypothesis {typed}`h : t₁ = t₂` writes a line connecting {lean}`t₁` and {lean}`t₂`.

2. Whenever two terms are connected by one or more lines, they're considered to be equal.
   Soon, whole constellations ({lean}`f a`, {lean}`g (f a)`, …) are connected.

3. If two different constructors of the same inductive type are connected by one or more lines, then a contradiction is discovered and the goal is closed.
   For example, equating {lean}`True` and {lean}`False` or {lean  (type := "Option Nat")}`none` and {lean}`some 1` would be a contradiction.

:::
::::

:::example "Congruence Closure" (open := true)
This theorem is proved using congruence closure:
```lean
example {α} (f g : α → α) (x y : α)
    (h₁ : x = y) (h₂ : f y = g y) :
    f x = g x := by
  grind
```
Initially, `f y`, `g y`, `x`, and `y` are in separate equivalence classes.
The congruence closure engine uses `h₁` to merge `x` and `y`, after which the equivalence classes are `{x, y}`, `f y`, and `g y`.
Next, `h₂` is used to merge `f y` and `g y`, after which the classes are `{x, y}` and `{f y, g y}`.
This is sufficient to prove that `f x = g x`, because `y` and `x` are in the same class.

Similar reasoning is used for constructors:
```lean
example (a b c : Nat) (h : a = b) : (a, c) = (b, c) := by
  grind
```
Because the pair constructor {name}`Prod.mk` obeys congruence, the tuples become equal as soon as `a` and `b` are placed in the same class.
:::


# Congruence Closure vs. Simplification

::::leanSection
```lean -show
variable {t₁ t₂ : α} {h : t₁ = t₂} {a : α} {f : α → β} {g : β → β}
```
:::paragraph
Congruence closure is a fundamentally different operation from simplification:

* {tactic}`simp` _rewrites_ a goal, replacing occurrences of {lean}`t₁` with {lean}`t₂` as soon as it sees {typed}`h : t₁ = t₂`.
  The rewrite is directional and destructive.
* {tactic}`grind` _accumulates_ equalities bidirectionally.  No term is rewritten; instead, both representatives live in the same class.  All other engines ({TODO}[techterm] E‑matching, theory solvers, {tech (key := "constraint propagation")}[propagation]) can query these classes and add new facts, then the closure updates incrementally.

This makes congruence closure especially robust in the presence of symmetrical reasoning, mutual recursion, and large nestings of constructors where rewriting would duplicate work.
:::
::::
