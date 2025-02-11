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

#doc (Manual) "Definitional equality" =>

These tactics modify the goal or assumptions in a way that remains
definitionally equal.

:::tactic Lean.Parser.Tactic.dsimp
:::

:::tactic "change"
:::

:::tactic "unfold"
:::

:::tactic Lean.Parser.Tactic.tacticShow_
:::
