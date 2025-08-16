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

#doc (Manual) "Logic" =>

These tactics deal with statements in logic. Remember that
`tauto`, listed above, is also good a these.

:::tactic Mathlib.Tactic.Contrapose.contrapose
:::

:::tactic Mathlib.Tactic.PushNeg.tacticPush_neg_
:::

:::tactic Mathlib.Tactic.TFAE.tfaeHave
:::

:::tactic Mathlib.Tactic.TFAE.tfaeFinish
:::

:::tactic Mathlib.Tactic.useSyntax
:::

:::tactic Mathlib.Tactic.wlog
:::

:::tactic Mathlib.Tactic.Choose.choose
:::

:::tactic Mathlib.Tactic.Peel.peel
:::

:::tactic "left"
:::

:::tactic "right"
:::

:::tactic "contradiction"
:::

:::tactic "exfalso"
:::
