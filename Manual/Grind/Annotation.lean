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

#doc (Manual) "Annotating libraries for `grind`" =>
%%%
tag := "grind annotation"
%%%

(work-in-progress, this needs examples)

Annotations should generally be conservative: only add an attribute or grind pattern when
you expect that {tactic}`grind` should always instantiate the theorem once the patterns are matched.

Typically, many theorems that are annotated with `@[simp]` will also be need to be annotated with `@[grind =]`.
One significant exception is that typically we avoid having `@[simp]` theorems that introduce an `if` on the right hand side,
instead preferring a pair of theorems with the positive and negative conditions as hypotheses.
Because `grind` is designed to perform case splitting, it is generally better to instead label the single theorem introducing the `if` with `@[grind =]`.

Besides using `@[grind =]` to encourage {tactic}`grind` to perform rewriting from left to right,
you can also use `@[grind _=_]` to "saturate", allowing bidirectional rewriting whenever either side is encountered.

Use `@[grind ←]` (which generates patterns from the conclusion of the theorem) for backwards reasoning theorems,
i.e. theorems that should be tried when their conclusion matches a goal.

Use `@[grind →]` (which generates patterns from the hypotheses) for forwards reasoning theorems,
i.e. where facts should be propagated from existing facts on the whiteboard.

There are many uses for custom patterns created with the `grind_pattern` command.
One common use is to introduce inequalities about terms, or membership propositions.

We might have
```
theorem count_le_size {a : α} {xs : Array α} : count a xs ≤ xs.size := countP_le_size

grind_pattern count_le_size => count a xs
```
which will register this inequality as soon as a `count a xs` term is encountered (even if the problem has not previously involved inequalities).

We can also use multi-patterns to be more restrictive,
e.g. only introducing an inequality about sizes if the whiteboard already contains facts about sizes:
```
theorem size_pos_of_mem {a : α} {xs : Array α} (h : a ∈ xs) : 0 < xs.size := sorry

grind_pattern size_pos_of_mem => a ∈ xs, xs.size
```
Unlike `@[grind →]` attribute, which would cause this theorem to be instantiated whenever `a ∈ xs` is encountered,
this pattern will only be used when `xs.size` is already on the whiteboard.
(Note that this grind pattern could also be produced using the `@[grind <=]` attribute, which looks at the conclusion first,
then backwards through the hypotheses to select patterns. On the other hand `@[grind →]` would select only `a ∈ xs`.)

In Mathlib we might want to enable polynomial reasoning about the sine and cosine functions,
and so add a custom grind pattern
```
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 := ...

grind_pattern sin_sq_add_cos_sq => sin x, cos x
```
which will instantiate the theorem as soon as *both* `sin x` and `cos x` (with the same `x`) are encountered.
This theorem will then automatically enter the Gröbner basis module,
and be used to reason about polynomial expressions involving both `sin x` and `cos x`.
One both alternatively, more aggressively, write two separate grind patterns so that this theorem instantiated when either `sin x` or `cos x` is encountered.
