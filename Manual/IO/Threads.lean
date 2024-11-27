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

#doc (Manual) "Tasks and Threads" =>

{docstring Task}

{docstring Task.spawn}

{docstring Task.get}

{docstring IO.wait}

{docstring IO.waitAny}

{docstring EIO.mapTask}

{docstring IO.mapTask}

{docstring EIO.mapTasks}

{docstring IO.mapTasks}

{docstring EIO.bindTask}

{docstring IO.bindTask}

{docstring EIO.asTask}

{docstring IO.asTask}

{docstring IO.cancel}

{docstring IO.getTaskState}

{docstring IO.checkCanceled}

{docstring IO.hasFinished}
