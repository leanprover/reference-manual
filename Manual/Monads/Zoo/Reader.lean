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

#doc (Manual) "Reader" =>
%%%
tag := "reader-monad"
%%%

{docstring MonadReader}

{docstring MonadReaderOf}

{docstring readThe}

{docstring MonadWithReader}

{docstring MonadWithReaderOf}

{docstring withTheReader}

{docstring ReaderT}

{docstring ReaderM (allowMissing := true)}

{docstring ReaderT.run}

{docstring ReaderT.read}

{docstring ReaderT.adapt}

{docstring ReaderT.pure}

{docstring ReaderT.bind}

{docstring ReaderT.orElse (allowMissing := true)}

{docstring ReaderT.failure (allowMissing := true)}
