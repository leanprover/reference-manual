/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


import Std.Data.TreeMap
import Std.Data.TreeMap.Raw


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 250000


#doc (Manual) "Tree-Based Maps" =>
%%%
tag := "TreeMap"
%%%


The declarations in this section should be imported using `import Std.TreeMap`.

{docstring Std.TreeMap +hideFields +hideStructureConstructor}

# Creation

{docstring Std.TreeMap.empty}

# Properties

{docstring Std.TreeMap.size}

{docstring Std.TreeMap.isEmpty}


# Queries

{docstring Std.TreeMap.contains}

{docstring Std.TreeMap.get}

{docstring Std.TreeMap.get!}

{docstring Std.TreeMap.get?}

{docstring Std.TreeMap.getD}

{docstring Std.TreeMap.getKey}

{docstring Std.TreeMap.getKey!}

{docstring Std.TreeMap.getKey?}

{docstring Std.TreeMap.getKeyD}

{docstring Std.TreeMap.keys}

{docstring Std.TreeMap.keysArray}

{docstring Std.TreeMap.values}

{docstring Std.TreeMap.valuesArray}

## Ordering-Based Queries

{docstring Std.TreeMap.entryAtIdx}

{docstring Std.TreeMap.entryAtIdx!}

{docstring Std.TreeMap.entryAtIdx?}

{docstring Std.TreeMap.entryAtIdxD}

{docstring Std.TreeMap.getEntryGE}

{docstring Std.TreeMap.getEntryGE!}

{docstring Std.TreeMap.getEntryGE?}

{docstring Std.TreeMap.getEntryGED}

{docstring Std.TreeMap.getEntryGT}

{docstring Std.TreeMap.getEntryGT!}

{docstring Std.TreeMap.getEntryGT?}

{docstring Std.TreeMap.getEntryGTD}

{docstring Std.TreeMap.getEntryLE}

{docstring Std.TreeMap.getEntryLE!}

{docstring Std.TreeMap.getEntryLE?}

{docstring Std.TreeMap.getEntryLED}

{docstring Std.TreeMap.getEntryLT}

{docstring Std.TreeMap.getEntryLT!}

{docstring Std.TreeMap.getEntryLT?}

{docstring Std.TreeMap.getEntryLTD}

{docstring Std.TreeMap.getKeyGE}

{docstring Std.TreeMap.getKeyGE!}

{docstring Std.TreeMap.getKeyGE?}

{docstring Std.TreeMap.getKeyGED}

{docstring Std.TreeMap.getKeyGT}

{docstring Std.TreeMap.getKeyGT!}

{docstring Std.TreeMap.getKeyGT?}

{docstring Std.TreeMap.getKeyGTD}

{docstring Std.TreeMap.getKeyLE}

{docstring Std.TreeMap.getKeyLE!}

{docstring Std.TreeMap.getKeyLE?}

{docstring Std.TreeMap.getKeyLED}

{docstring Std.TreeMap.getKeyLT}

{docstring Std.TreeMap.getKeyLT!}

{docstring Std.TreeMap.getKeyLT?}

{docstring Std.TreeMap.getKeyLTD}

{docstring Std.TreeMap.keyAtIdx}

{docstring Std.TreeMap.keyAtIdx!}

{docstring Std.TreeMap.keyAtIdx?}

{docstring Std.TreeMap.keyAtIdxD}

{docstring Std.TreeMap.minEntry}

{docstring Std.TreeMap.minEntry!}

{docstring Std.TreeMap.minEntry?}

{docstring Std.TreeMap.minEntryD}

{docstring Std.TreeMap.minKey}

{docstring Std.TreeMap.minKey!}

{docstring Std.TreeMap.minKey?}

{docstring Std.TreeMap.minKeyD}

{docstring Std.TreeMap.maxEntry}

{docstring Std.TreeMap.maxEntry!}

{docstring Std.TreeMap.maxEntry?}

{docstring Std.TreeMap.maxEntryD}

{docstring Std.TreeMap.maxKey}

{docstring Std.TreeMap.maxKey!}

{docstring Std.TreeMap.maxKey?}

{docstring Std.TreeMap.maxKeyD}


# Modification

{docstring Std.TreeMap.alter}

{docstring Std.TreeMap.modify}

{docstring Std.TreeMap.containsThenInsert}

{docstring Std.TreeMap.containsThenInsertIfNew}

{docstring Std.TreeMap.erase}

{docstring Std.TreeMap.eraseMany}

{docstring Std.TreeMap.filter}

{docstring Std.TreeMap.filterMap}

{docstring Std.TreeMap.insert}

{docstring Std.TreeMap.insertIfNew}

{docstring Std.TreeMap.getThenInsertIfNew?}

{docstring Std.TreeMap.insertMany}

{docstring Std.TreeMap.insertManyIfNewUnit}

{docstring Std.TreeMap.mergeWith}

{docstring Std.TreeMap.partition}


# Iteration

{docstring Std.TreeMap.map}

{docstring Std.TreeMap.all}

{docstring Std.TreeMap.any}

{docstring Std.TreeMap.foldl}

{docstring Std.TreeMap.foldlM}

{docstring Std.TreeMap.foldr}

{docstring Std.TreeMap.foldrM}

{docstring Std.TreeMap.forIn}

{docstring Std.TreeMap.forM}

# Conversion

{docstring Std.TreeMap.ofList}

{docstring Std.TreeMap.toList}

{docstring Std.TreeMap.ofArray}

{docstring Std.TreeMap.toArray}

{docstring Std.TreeMap.unitOfArray}

{docstring Std.TreeMap.unitOfList}

## Unbundled Variants

Unbundled maps separate well-formedness proofs from data.
This is primarily useful when defining {ref "raw-data"}[nested inductive types].
To use these variants, import the module `Std.TreeMap.Raw`.

{docstring Std.TreeMap.Raw}

{docstring Std.TreeMap.Raw.WF}
