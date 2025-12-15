/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import Lean
import Manual.Meta.ErrorExplanation
import Manual.ErrorExplanations.CtorResultingTypeMismatch
import Manual.ErrorExplanations.InductiveParamMissing

open Lean
open Verso.Genre Manual

#doc (Manual) "Error Explanations" =>
%%%
number := false
htmlToc := false
%%%

This section provides explanations of errors and warnings that may be generated
by Lean when processing a source file. All error names listed below have the
`lean` package prefix.

{error_explanation_table}

{include 0 Manual.ErrorExplanations.CtorResultingTypeMismatch}

{include 0 Manual.ErrorExplanations.InductiveParamMissing}
