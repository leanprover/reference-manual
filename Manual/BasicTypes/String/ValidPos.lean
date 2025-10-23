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

#doc (Manual) "Positions" =>
%%%
tag := "string-api-valid-pos"
%%%


{docstring String.ValidPos}

# In Strings

{docstring String.startValidPos}

{docstring String.endValidPos}

{docstring String.pos}

{docstring String.pos?}

{docstring String.pos!}

# Lookups

{docstring String.ValidPos.get}

{docstring String.ValidPos.get!}

{docstring String.ValidPos.get?}

{docstring String.ValidPos.set}

{docstring String.ValidPos.extract +allowMissing}

# Modifications

{docstring String.ValidPos.modify}

{docstring String.ValidPos.byte}

# Adjustment

{docstring String.ValidPos.prev}

{docstring String.ValidPos.prev!}

{docstring String.ValidPos.prev?}

{docstring String.ValidPos.next}

{docstring String.ValidPos.next!}

{docstring String.ValidPos.next?}

# Other Strings

{docstring String.ValidPos.cast}

{docstring String.ValidPos.ofCopy}

{docstring String.ValidPos.setOfLE}

{docstring String.ValidPos.modifyOfLE}

{docstring String.ValidPos.toSlice}
