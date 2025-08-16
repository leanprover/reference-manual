/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import Mathlib

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.unusedVariables false

set_option maxHeartbeats 0
set_option maxRecDepth 100000000000000000

open Lean.Elab.Tactic

#doc (Manual) "Algebra" =>

These tactics deal with algebraic calculations.

:::tactic Mathlib.Tactic.Abel.abel
:::

:::tactic Mathlib.Tactic.Group.group
:::

:::tactic Mathlib.Tactic.RingNF.ring
:::

:::tactic Mathlib.Tactic.NoncommRing.noncomm_ring
:::

:::tactic Mathlib.Tactic.Module.tacticModule
:::

:::tactic Mathlib.Tactic.LinearCombination.linearCombination
:::

:::tactic Mathlib.Tactic.FieldSimp.fieldSimp
:::

:::tactic cancelDenoms
:::

:::tactic Mathlib.Tactic.tacticAlgebraize__
:::

:::tactic Tactic.ReduceModChar.reduce_mod_char
:::

:::tactic Mathlib.Tactic.ComputeDegree.computeDegree
:::

:::tactic Mathlib.Tactic.ComputeDegree.monicityMacro
:::
