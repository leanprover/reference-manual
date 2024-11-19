/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual hiding «example»
open Verso.Genre
open Verso.Genre.Manual
open Lean.Parser.Command (declModifiers «example»)

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "IO" =>

%%%
tag := "io"
%%%

:::planned 102
This chapter will describe features for writing programs that can have side effects on the real world.
:::
