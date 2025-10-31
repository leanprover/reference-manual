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

#doc (Manual) "Rewriting / `calc`" =>

These tactics are used for rewriting parts of a goal with something
that is equal (or equivalent/etc.)

:::tactic "calc"
:::

:::tactic "rw"
:::

:::tactic Mathlib.Tactic.tacticNth_rw_____
:::

:::tactic Mathlib.Tactic.tacticSimp_rw___
:::

The following Tactic is avoided in Mathlib

:::tactic "erw"
:::

:::tactic "grw"
:::
