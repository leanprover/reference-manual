/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Tweaks
import Manual.Tactics
import Manual.Guides

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxRecDepth 1024


#doc (Manual) "Mathlib Manual" =>
%%%
tag := "mathlib-manual"
%%%

This document has been last updated at *{now}[]* using Lean *{versionString}[]* and Mathlib commit {mathlibCommit}[].

*Other resources*:
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/index.html):
  automatically generated collection of all declarations from Mathlib.
- The [Lean Language Reference](https://lean-lang.org/doc/reference/latest/) contains
  detailed information about Lean Code.

If you would like to contribute content, please create a PR using the two github links
at the bottom left of this page!

{include 0 Manual.Tactics}

{include 0 Manual.Guides}
