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

#doc (Manual) "Option" =>
%%%
tag := "option-monad"
%%%

Ordinarily, {lean}`Option` is thought of as data, similarly to a nullable type.
It can also be considered as a monad, and thus a way of performing computations.
The {lean}`Option` monad and its transformer {lean}`OptionT` can be understood as describing computations that may terminate early, discarding the results.
Callers can check for early termination and invoke a fallback if desired using {name}`OrElse.orElse` or by treating it as a {lean}`MonadExcept Unit`.

{docstring OptionT}

{docstring OptionT.run}

{docstring OptionT.lift}

{docstring OptionT.mk}

{docstring OptionT.pure}

{docstring OptionT.bind}

{docstring OptionT.fail}

{docstring OptionT.orElse}

{docstring OptionT.tryCatch}
