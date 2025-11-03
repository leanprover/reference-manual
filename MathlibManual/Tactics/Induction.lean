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

#doc (Manual) "Induction / case distinction" =>

:::tactic "induction"
:::

:::tactic "cases"
:::

:::tactic "rcases"
:::

:::tactic "by_cases"
:::

:::tactic Lean.Elab.Tactic.finCases
:::

:::tactic Mathlib.Tactic.intervalCases
:::

:::tactic "split"
:::

:::tactic Mathlib.Tactic.splitIfs
:::
