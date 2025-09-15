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

#doc (Manual) "Basic tactics / assumptions" =>

:::tactic "rfl"
:::

:::tactic "symm"
:::

:::tactic Batteries.Tactic.tacticTrans___
:::

:::tactic Lean.Parser.Tactic.assumption
:::

:::tactic "exact"
:::

:::tactic Lean.Parser.Tactic.apply
:::

Note that `apply` and `apply at` are formally considered two distinct tactics
even though they appear to be one to the user.

:::tactic Mathlib.Tactic.tacticApply_At_ (show := "apply at")
:::

:::tactic "specialize"
:::

:::tactic "generalize"
:::

:::tactic Lean.Parser.Tactic.tacticHave__
:::

:::tactic Lean.Parser.Tactic.tacticLet__
:::

-- TODO: The `set` docstring ought to be on the `syntax`, not the `elab_rules`
-- remove the replace below once that's fixed
:::tactic Mathlib.Tactic.setTactic (replace := true)
:::

:::tactic Lean.Parser.Tactic.replace
:::

:::tactic Lean.Parser.Tactic.tacticSuffices_
:::

:::tactic Lean.Parser.Tactic.obtain
:::

:::tactic "refine"
:::

:::tactic Mathlib.Tactic.convert
:::

:::tactic "constructor"
:::

:::tactic "injection"
:::

:::tactic Lean.Parser.Tactic.intro
:::

:::tactic Lean.Parser.Tactic.revert
:::
