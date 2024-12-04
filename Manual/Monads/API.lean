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

#doc (Manual) "API Reference" =>

::: TODO
All the stuff that works in any monad. Sorted by purpose rather than constraint, because who can remember which things are Monad vs Applicative?

Include a remark about the various `mapM` included with each datatype's API
:::

{docstring andM}

{docstring orM}

{docstring notM}

{docstring guard}

{docstring optional}

{docstring discard}

{docstring Functor.mapRev}

{docstring Bind.kleisliLeft}

{docstring Bind.bindLeft}

{docstring Bind.kleisliRight}
