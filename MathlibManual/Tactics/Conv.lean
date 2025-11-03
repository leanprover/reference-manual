/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import Mathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.unusedVariables false

set_option maxHeartbeats 0
set_option maxRecDepth 100000000000000000

open Lean.Elab.Tactic

#doc (Manual) "Conv mode" =>

:::tactic Lean.Parser.Tactic.Conv.conv
:::

TODO: a lot of tactics have a `conv`-equivalent. Add them here.
Meanwhile, try other tactics and see which work in `conv` mode.
