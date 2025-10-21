/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Raw Positions" =>
%%%
tag := "string-api-pos"
%%%


{docstring String.Pos.Raw}

# Validity

{docstring String.Pos.Raw.isValid}

{docstring String.Pos.Raw.isValidForSlice}

# Boundaries

{docstring String.endPos}

{docstring String.Pos.Raw.atEnd}

# Comparisons

{docstring String.Pos.Raw.min}

{docstring String.Pos.Raw.byteDistance}

{docstring String.Pos.Raw.substrEq}

# Adjustment

{docstring String.Pos.Raw.prev}

{docstring String.Pos.Raw.next}

{docstring String.Pos.Raw.next'}

{docstring String.Pos.Raw.nextUntil}

{docstring String.Pos.Raw.nextWhile}

{docstring String.Pos.Raw.inc}

{docstring String.Pos.Raw.increaseBy}

{docstring String.Pos.Raw.offsetBy}

{docstring String.Pos.Raw.dec}

{docstring String.Pos.Raw.decreaseBy}

{docstring String.Pos.Raw.unoffsetBy}

# String Lookups

{docstring String.Pos.Raw.extract}

{docstring String.Pos.Raw.get}

{docstring String.Pos.Raw.get!}

{docstring String.Pos.Raw.get'}

{docstring String.Pos.Raw.get?}

# String Modifications

{docstring String.Pos.Raw.set}

{docstring String.Pos.Raw.modify}
