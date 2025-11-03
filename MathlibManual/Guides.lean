/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import Mathlib

import MathlibManual.Guides.LocalDevDependency
import MathlibManual.Guides.SharedMathlib
import MathlibManual.Guides.StableDependencies

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

set_option maxHeartbeats 0
set_option maxRecDepth 100000000000000000

open Lean.Elab.Tactic

#doc (Manual) "Guides" =>
%%%
tag := "guides"
%%%

This chapter contains informal guides. Note that these are not the official recommendations
by Lean or Mathlib. Rather, they are notes by users.

If they don't work please ask on Zulip or contribute improvements to the guides here.

{include 0 MathlibManual.Guides.SharedMathlib}

{include 0 MathlibManual.Guides.StableDependencies}

{include 0 MathlibManual.Guides.LocalDevDependency}
