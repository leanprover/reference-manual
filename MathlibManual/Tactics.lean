/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import Mathlib

import MathlibManual.Tactics.All
import MathlibManual.Tactics.Algebra
import MathlibManual.Tactics.Analysis
import MathlibManual.Tactics.Assumptions
import MathlibManual.Tactics.Automation
import MathlibManual.Tactics.CategoryTheory
import MathlibManual.Tactics.Coercions
import MathlibManual.Tactics.Control
import MathlibManual.Tactics.Conv
import MathlibManual.Tactics.DefEq
import MathlibManual.Tactics.Induction
import MathlibManual.Tactics.Interactive
import MathlibManual.Tactics.Logic
import MathlibManual.Tactics.Miscellaneous
import MathlibManual.Tactics.Rewriting
import MathlibManual.Tactics.Test

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

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

The section prior to the {ref "all_tactics"}[last section] are not final in any way.
Feel free to add/delete/rename/restructure any of these section and modify their content
freely to make them more useful! PR go to the [repository of this manual](https://github.com/leanprover-community/mathlib-manual).

{include 0 MathlibManual.Tactics.Interactive}

{include 0 MathlibManual.Tactics.Automation}

{include 0 MathlibManual.Tactics.Algebra}

{include 0 MathlibManual.Tactics.Analysis}

{include 0 MathlibManual.Tactics.Coercions}

{include 0 MathlibManual.Tactics.CategoryTheory}

{include 0 MathlibManual.Tactics.Logic}

{include 0 MathlibManual.Tactics.Induction}

{include 0 MathlibManual.Tactics.Assumptions}

{include 0 MathlibManual.Tactics.DefEq}

{include 0 MathlibManual.Tactics.Conv}

{include 0 MathlibManual.Tactics.Control}

{include 0 MathlibManual.Tactics.Test}

{include 0 MathlibManual.Tactics.Miscellaneous}

{include 0 MathlibManual.Tactics.All}
