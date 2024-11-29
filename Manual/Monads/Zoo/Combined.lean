/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Combined Monads" =>

{docstring EStateM}

{docstring EStateM.Result}

{docstring EStateM.dummyRestore}

{docstring EStateM.fromStateM}

{docstring EStateM.throw}

{docstring EStateM.bind}

{docstring EStateM.get}

{docstring EStateM.run}

{docstring EStateM.run'}

{docstring EStateM.orElse}

{docstring EStateM.set}

{docstring EStateM.dummySave}

{docstring EStateM.tryCatch}

{docstring EStateM.map}

{docstring EStateM.modifyGet}

{docstring EStateM.pure}

{docstring EStateM.orElse'}

{docstring EStateM.seqRight}

{docstring EStateM.adaptExcept}

:::TODO
Explain comment: `/-! Recall that `StateRefT` is a macro that infers `ω` from the `m`. -/`
:::

{docstring StateRefT'}
