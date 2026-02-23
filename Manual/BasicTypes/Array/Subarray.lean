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

#doc (Manual) "Subarrays" =>
%%%
tag := "subarray"
%%%

The type Subarrays are abbreviations for {name}`Std.Slice`.
This means that, in addition to the operators in this section, {tech}[generalized field notation] can be used to call functions in the `Std.Slice` namespace, such as {name}`Std.Slice.foldl`.

{docstring Subarray}

{docstring Subarray.empty}

# Array Data

{docstring Subarray.array}

{docstring Subarray.start}

{docstring Subarray.stop}

{docstring Subarray.start_le_stop}

{docstring Subarray.stop_le_array_size}

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
