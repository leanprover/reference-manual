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

#doc (Manual) "Sub-Arrays" =>
%%%
tag := "subarray"
%%%

{docstring Subarray}

{docstring Subarray.toArray}

{docstring Subarray.empty}

# Size

{docstring Subarray.size}

# Resizing

{docstring Subarray.drop}

{docstring Subarray.take}

{docstring Subarray.popFront}

{docstring Subarray.split}

# Lookups

{docstring Subarray.get}

{docstring Subarray.get!}

{docstring Subarray.getD}

# Iteration

{docstring Subarray.foldl}

{docstring Subarray.foldlM}

{docstring Subarray.foldr}

{docstring Subarray.foldrM}

{docstring Subarray.forM}

{docstring Subarray.forRevM}

{docstring Subarray.forIn}

# Element Predicates

{docstring Subarray.findRev?}

{docstring Subarray.findRevM?}

{docstring Subarray.findSomeRevM?}

{docstring Subarray.all}

{docstring Subarray.allM}

{docstring Subarray.any}

{docstring Subarray.anyM}
