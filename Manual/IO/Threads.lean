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

::: planned 90
A detailed description of the Lean multi-threading model, including:

 * {lean}`Task`s, priorities, and threads
 * Synchronization and communication primitives
    * {lean}`IO.Ref` as a lock
    * {lean}`IO.Mutex`
    * {lean}`IO.Channel`
    * {lean}`IO.Condvar`
    * {lean}`IO.Promise`
:::


{docstring Task}

{docstring Task.spawn}

{docstring Task.Priority}

{docstring Task.Priority.default}

{docstring Task.Priority.max}

{docstring Task.Priority.dedicated}

{docstring Task.get}

{docstring IO.wait}

{docstring IO.waitAny}

{docstring BaseIO.mapTask}

{docstring EIO.mapTask}

{docstring IO.mapTask}

{docstring BaseIO.mapTasks}

{docstring EIO.mapTasks}

{docstring IO.mapTasks}

{docstring BaseIO.bindTask}

{docstring EIO.bindTask}

{docstring IO.bindTask}

{docstring BaseIO.asTask}

{docstring EIO.asTask}

{docstring IO.asTask}

{docstring IO.cancel}

{docstring IO.getTaskState}

{docstring IO.checkCanceled}

{docstring IO.hasFinished}
