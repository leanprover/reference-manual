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

#doc (Manual) "Analysis" =>

add intro text here

:::tactic Lean.Parser.Tactic.congr
:::

:::tactic Mathlib.Tactic.GCongr.tacticGcongr___With___
:::

:::tactic finiteness (show := "finiteness")
:::

:::tactic Mathlib.Tactic.Monotonicity.mono
:::

:::tactic Mathlib.Meta.FunProp.funPropTacStx
:::

:::tactic tacticContinuity
:::

:::example "bound"
TODO
:::

:::tactic Mathlib.Tactic.normNum
:::
