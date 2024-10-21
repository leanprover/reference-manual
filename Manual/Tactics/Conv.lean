/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Targeted Rewriting with {tactic}`conv`" =>


The {tactic}`conv`, or conversion, tactic allows targeted rewriting within a goal.
The argument to {tactic}`conv` is written in a separate language that interoperates with the main tactic language; it features commands to navigate to specific subterms within the goal along with commands that allow these subterms to be rewritten.
{tactic}`conv` is useful when rewrites should only be applied in part of a goal (e.g. only on one side of an equality), rather than across the board, or when rewrites should be applied underneath a binder that prevents tactics like {tactic}`rw` from accessing the term.

The conversion tactic language is very similar to the main tactic language: it uses the same proof states, tactics work primarily on the main goal and may either fail or succeed with a sequence of new goals, and macro expansion is interleaved with tactic execution.
Unlike the main tactic language, in which tactics are intended to eventually solve goals, the {tactic}`conv` tactic is used to _change_ a goal so that it becomes amenable to further processing in the main tactic language.
Goals that are intended to be rewritten with {tactic}`conv` are shown with a vertical bar instead of a turnstile.

:::tactic "conv"
:::

::::example "Navigation and Rewriting with {tactic}`conv`"

In this example, there are multiple instances of addition, and {tactic}`rw` would by default rewrite the first instance that it encounters.
Using {tactic}`conv` to navigate to the specific subterm before rewriting leaves {tactic}`rw` no choice but to rewrite the correct term.

```lean
example (x y z : Nat) : x + (y + z) = (x + z) + y := by
  conv =>
    lhs
    arg 2
    rw [Nat.add_comm]
  rw [Nat.add_assoc]
```

::::

::::example "Rewriting Under Binders with {tactic}`conv`"

In this example, addition occurs under binders, so {tactic}`rw` can't be used.
However, after using {tactic}`conv` to navigate to the function body, it succeeds.
The nested use of {tactic}`conv` causes control to return to the current position in the term after performing further coversions on one of its subterms.
Because the goal is a reflexive equation after rewriting, {tactic}`conv` automatically closes it.

```lean
example : (fun (x y z : Nat) => x + (y + z)) = (fun x y z => (z + x) + y) := by
  conv =>
    lhs
    intro x y z
    conv =>
      arg 2
      rw [Nat.add_comm]
    rw [← Nat.add_assoc]
    arg 1
    rw [Nat.add_comm]
```

::::

# Control Structures


:::conv first show := "first"
:::

:::conv convTry_ show := "try"
:::

:::conv «conv_<;>_» show:="<;>"
:::

:::conv convRepeat_ show := "repeat"
:::

:::conv skip show:= "skip"
:::

:::conv nestedConv show:= "{ ... }"
:::

:::conv paren show:= "( ... )"
:::

:::conv convDone show:= "done"
:::

# Goal Selection

:::conv allGoals show:= "all_goals"
:::

:::conv anyGoals show:= "any_goals"
:::

:::conv case show:= "case ... => ..."
:::

:::conv case' show:= "case' ... => ..."
:::

:::conv «convNext__=>_» show:= "next ... => ..."
:::

:::conv focus show := "focus"
:::

:::conv «conv·._» show := ". ..."
:::

:::conv «conv·._» show := "· ..."
:::

:::conv failIfSuccess show := "fail_if_success"
:::


# Navigation

:::conv lhs show:= "lhs"
:::

:::conv rhs show:= "rhs"
:::

:::conv fun show:= "fun"
:::

:::conv congr show:= "congr"
:::

:::conv arg show:= "arg [@]i"
:::

:::syntax Lean.Parser.Tactic.Conv.enterArg
```grammar
$i:num
```
```grammar
@$i:num
```
```grammar
$x:ident
```
:::

:::conv «convEnter[_]» show := "enter"
:::


:::conv pattern show:= "pattern"
:::

:::conv ext show:= "ext"
:::

:::conv convArgs show := "args"
:::

:::conv convLeft show := "left"
:::

:::conv convRight show := "right"
:::

:::conv convIntro___ show := "intro"
:::

# Changing the Goal
## Reduction

:::conv whnf show:= "whnf"
:::

:::conv reduce show:= "reduce"
:::

:::conv zeta show:= "zeta"
:::

:::conv delta show:= "delta"
:::

:::conv unfold show:= "unfold"
:::

## Simplification
:::conv simp show:= "simp"
:::

:::conv dsimp show:= "dsimp"
:::

:::conv simpMatch show:= "simp_match"
:::

## Rewriting


:::conv change show:= "change"
:::

:::conv rewrite show:= "rewrite"
:::

:::conv convRw__ show := "rw"
:::

:::conv convErw_ show := "erw"
:::

:::conv convApply_ show := "apply"
:::


# Nested Tactics

:::tactic Lean.Parser.Tactic.Conv.convTactic
:::

:::conv nestedTactic show:= "tactic"
:::

:::conv nestedTacticCore show:= "tactic'"
:::

:::tactic Lean.Parser.Tactic.Conv.convTactic show:= "conv'"
:::

:::conv convConvSeq show := "conv => ..."
:::


# Debugging Utilities

:::conv convTrace_state show:= "trace_state"
:::


# Other

:::conv convRfl show:= "rfl"
:::

:::conv normCast show := "norm_cast"
:::
