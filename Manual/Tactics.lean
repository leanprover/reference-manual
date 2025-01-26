/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import Mathlib

import Manual.Tactics.All
import Manual.Tactics.Algebra
import Manual.Tactics.Analysis
import Manual.Tactics.Assumptions
import Manual.Tactics.Automation
import Manual.Tactics.CategoryTheory
import Manual.Tactics.Coersions
import Manual.Tactics.CongrExt
import Manual.Tactics.Control
import Manual.Tactics.Conv
import Manual.Tactics.DefEq
import Manual.Tactics.Induction
import Manual.Tactics.Interactive
import Manual.Tactics.Logic
import Manual.Tactics.Miscellaneous
import Manual.Tactics.Rewriting
import Manual.Tactics.Test

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false


set_option maxHeartbeats 0
set_option maxRecDepth 100000000000000000

open Lean.Elab.Tactic

#doc (Manual) "Tactics" =>
%%%
tag := "tactics"
%%%

This chapter introduces many tactics that are used to proof theorems.
A tactic proof is started using `by`.

The {ref "all_tactics"}[last section] contains an automatically generated
list of all tactics known to Mathlib, the sections before that are manually
curated.

The displayed tactic names and docstring are automatically
extracted from the Lean code, so
if the information is wrong, you should directly create a PR to the repo
containing the tactic and change things there.

If a tactic is missing from any of the sections,
please PR to the [repository of this manual](https://github.com/leanprover-community/mathlib-manual).

{include 0 Manual.Tactics.Interactive}

{include 0 Manual.Tactics.Automation}

{include 0 Manual.Tactics.Algebra}

{include 0 Manual.Tactics.Analysis}

{include 0 Manual.Tactics.CategoryTheory}

{include 0 Manual.Tactics.Miscellaneous}

{include 0 Manual.Tactics.Induction}

{include 0 Manual.Tactics.Logic}

{include 0 Manual.Tactics.CongrExt}

{include 0 Manual.Tactics.Coersions}

{include 0 Manual.Tactics.DefEq}

{include 0 Manual.Tactics.Assumptions}

{include 0 Manual.Tactics.Conv}

{include 0 Manual.Tactics.Control}

{include 0 Manual.Tactics.Test}

{include 0 Manual.Tactics.All}
