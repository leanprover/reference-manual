/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


import Std.Data.TreeSet
import Std.Data.TreeSet.Raw

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Tree-Based Sets" =>
%%%
tag := "TreeSet"
%%%

{docstring Std.TreeSet (hideStructureConstructor := true) (hideFields := true)}

# Creation

{docstring Std.TreeSet.empty}

# Properties

{docstring Std.TreeSet.isEmpty}

{docstring Std.TreeSet.size}

# Queries

{docstring Std.TreeSet.contains}

{docstring Std.TreeSet.get}

{docstring Std.TreeSet.get!}

{docstring Std.TreeSet.get?}

{docstring Std.TreeSet.getD}

## Ordering-Based Queries

{docstring Std.TreeSet.atIdx}

{docstring Std.TreeSet.atIdx!}

{docstring Std.TreeSet.atIdx?}

{docstring Std.TreeSet.atIdxD}

{docstring Std.TreeSet.getGE}

{docstring Std.TreeSet.getGE!}

{docstring Std.TreeSet.getGE?}

{docstring Std.TreeSet.getGED}

{docstring Std.TreeSet.getGT}

{docstring Std.TreeSet.getGT!}

{docstring Std.TreeSet.getGT?}

{docstring Std.TreeSet.getGTD}

{docstring Std.TreeSet.getLE}

{docstring Std.TreeSet.getLE!}

{docstring Std.TreeSet.getLE?}

{docstring Std.TreeSet.getLED}

{docstring Std.TreeSet.getLT}

{docstring Std.TreeSet.getLT!}

{docstring Std.TreeSet.getLT?}

{docstring Std.TreeSet.getLTD}


{docstring Std.TreeSet.min}

{docstring Std.TreeSet.min!}

{docstring Std.TreeSet.min?}

{docstring Std.TreeSet.minD}

{docstring Std.TreeSet.max}

{docstring Std.TreeSet.max!}

{docstring Std.TreeSet.max?}

{docstring Std.TreeSet.maxD}

# Modification


{docstring Std.TreeSet.insert}

{docstring Std.TreeSet.insertMany}

{docstring Std.TreeSet.containsThenInsert}

{docstring Std.TreeSet.erase}

{docstring Std.TreeSet.eraseMany}

{docstring Std.TreeSet.filter}

{docstring Std.TreeSet.merge}

{docstring Std.TreeSet.partition}


# Iteration

{docstring Std.TreeSet.all}

{docstring Std.TreeSet.any}

{docstring Std.TreeSet.foldl}

{docstring Std.TreeSet.foldlM}

{docstring Std.TreeSet.foldr}

{docstring Std.TreeSet.foldrM}

{docstring Std.TreeSet.forIn}

{docstring Std.TreeSet.forM}


# Conversion

{docstring Std.TreeSet.toList}

{docstring Std.TreeSet.ofList}

{docstring Std.TreeSet.toArray}

{docstring Std.TreeSet.ofArray}

## Unbundled Variants

Unbundled sets separate well-formedness proofs from data.
This is primarily useful when defining {ref "raw-data"}[nested inductive types].
To use these variants, import the module `Std.TreeSet.Raw`.

{docstring Std.TreeSet.Raw}

{docstring Std.TreeSet.Raw.WF}
