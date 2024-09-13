import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "The Simplifier" =>
%%%
tag := "the-simplifier"
%%%

:::planned
Describe {tactic}`simp` in detail, including:
 * The concept of {tactic}`simp` normal form and its importance
 * The `@[simp]` attribute
 * Simprocs
 * A comparison of how `simp` and `rw` use equality lemmas
:::
