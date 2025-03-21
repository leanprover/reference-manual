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

#doc (Manual) "Simplification" =>
%%%
tag := "simp-tactics"
%%%

The simplifier is described in greater detail in {ref "the-simplifier"}[its dedicated chapter].

:::tactic "simp"
:::

:::tactic "simp!"
:::

:::tactic "simp?"
:::

:::tactic "simp?!"
:::

:::tactic "simp_arith"
:::

:::tactic "simp_arith!"
:::

:::tactic "dsimp"
:::

:::tactic "dsimp!"
:::

:::tactic "dsimp?"
:::

:::tactic "dsimp?!"
:::


:::tactic "simp_all"
:::

:::tactic "simp_all!"
:::

:::tactic "simp_all?"
:::

:::tactic "simp_all?!"
:::


:::tactic "simp_all_arith"
:::


:::tactic "simp_all_arith!"
:::


:::tactic "simpa"
:::


:::tactic "simpa!"
:::

:::tactic "simpa?"
:::

:::tactic "simpa?!"
:::

:::tactic "simp_wf"
:::
