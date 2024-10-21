/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


#doc (Manual) "Logical Model" =>

{docstring String}

The logical model of strings in Lean is a structure that contains a single field, which is a list of characters.
This is convenient when specifying and proving properties of string-processing fuctions at a low level.
