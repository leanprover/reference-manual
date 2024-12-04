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

#doc (Manual) "Exceptions" =>
%%%
tag := "exception-monads"
%%%

{docstring MonadExcept}

{docstring MonadExcept.ofExcept}

{docstring MonadExcept.orElse}

{docstring MonadExcept.orelse'}

{docstring MonadExceptOf}

{docstring throwThe}

{docstring tryCatchThe}

{docstring MonadFinally}

{docstring ExceptT}

{docstring ExceptT.lift}

{docstring ExceptT.run}

{docstring ExceptT.pure}

{docstring ExceptT.bind}

{docstring ExceptT.bindCont}

{docstring ExceptT.tryCatch}

{docstring ExceptT.mk}

{docstring ExceptT.map}

{docstring ExceptT.adapt}

{docstring Except}

{docstring Except.pure}

{docstring Except.bind}

{docstring Except.map}

{docstring Except.mapError}

{docstring Except.tryCatch}

{docstring Except.orElseLazy}

{docstring Except.isOk}

{docstring Except.toOption}

{docstring Except.toBool}

{docstring ExceptCpsT}

{docstring ExceptCpsT.runCatch}

{docstring ExceptCpsT.runK}

{docstring ExceptCpsT.run}

{docstring ExceptCpsT.lift}
