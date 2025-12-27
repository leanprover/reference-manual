/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import MathlibManual.Util.AllTactics
import Mathlib

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

set_option maxHeartbeats 0
set_option maxRecDepth 10000000000000000000

section

open Lean.Elab.Tactic.Doc

#eval do
  let tacs ← allTacticDocs
  return s!"There are {tacs.size} tactics"

end

open Lean.Elab.Tactic

#doc (Manual) "All tactics" =>
%%%
tag := "all_tactics"
%%%

This list of tactics is automatically generated and contains all tactics known in Mathlib, regardless of which
package (Lean/Std/Batteries/Mathlib/etc.) defines them.

If you see two tactics which are almost identical, consider adding `tactic_alt TAC` to the variant version of a tactic to tell Lean to group them together.

:::all_tactics (to := "c")
:::

:::all_tactics (from := "c") (to := "e")
:::

:::all_tactics (from := "e") (to := "g")
:::

:::all_tactics (from := "g") (to := "i")
:::

:::all_tactics (from := "i") (to := "k")
:::

:::all_tactics (from := "k") (to := "m")
:::

:::all_tactics (from := "m") (to := "o")
:::

:::all_tactics (from := "o") (to := "q")
:::

:::all_tactics (from := "q") (to := "s")
:::

:::all_tactics (from := "s") (to := "u")
:::

:::all_tactics (from := "u") (to := "w")
:::

:::all_tactics (from := "w") (to := "y")
:::

:::all_tactics (from := "y")
:::

Hey, I'm only here as a hack. Please ignore me and that thing below.

-- TODO: without anything here verso gets a parsing error...?
{optionDocs trace.grind.split}
