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

#doc (Manual) "Automation" =>

:::tactic Aesop.Frontend.Parser.aesopTactic
:::

:::tactic "omega"
:::

:::tactic Lean.Parser.Tactic.decide (show := "decide")
:::

:::tactic Lean.Parser.Tactic.simp
:::

::: tactic Lean.Parser.Tactic.simpAll
:::

:::tactic "infer_instance"
:::

:::tactic Mathlib.Tactic.Tauto.tauto
:::

:::tactic Lean.Parser.Tactic.bvDecide
:::

:::tactic "trivial"
:::

:::tactic Mathlib.Tactic.cc
:::

:::example "polyrith"
TODO
:::

:::tactic Mathlib.Tactic.linarith (show := "linarith")
:::
