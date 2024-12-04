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

#doc (Manual) "State" =>
%%%
tag := "state-monads"
%%%

{docstring MonadState}

{docstring get}

{docstring modify}

{docstring modifyGet}

{docstring getModify}

{docstring MonadStateOf}

{docstring getThe}

{docstring modifyThe}

{docstring modifyGetThe}

{docstring StateM}

{docstring StateT}

{docstring StateT.run}

{docstring StateT.get}

{docstring StateT.set}

{docstring StateT.orElse}

{docstring StateT.failure}

{docstring StateT.run'}

{docstring StateT.bind}

{docstring StateT.modifyGet}

{docstring StateT.lift}

{docstring StateT.map}

{docstring StateT.pure}

{docstring StateCpsT}

{docstring StateCpsT.lift}

{docstring StateCpsT.runK}

{docstring StateCpsT.run'}

{docstring StateCpsT.run}
