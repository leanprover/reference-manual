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

#doc (Manual) "Raw Substrings" =>
%%%
tag := "string-api-substring"
%%%

Raw substrings are a low-level type that groups a string together with byte positions that delimit a region in the string.
Most code should use {ref "string-api-slice"}[slices] instead, because they are safer and more convenient.

{docstring String.toRawSubstring}

{docstring String.toRawSubstring'}

{docstring Substring.Raw}

# Properties

{docstring Substring.Raw.isEmpty}

{docstring Substring.Raw.bsize}

# Positions

{docstring Substring.Raw.atEnd}

{docstring Substring.Raw.posOf}

{docstring Substring.Raw.next}

{docstring Substring.Raw.nextn}

{docstring Substring.Raw.prev}

{docstring Substring.Raw.prevn}


# Folds and Aggregation

{docstring Substring.Raw.foldl}

{docstring Substring.Raw.foldr}

{docstring Substring.Raw.all}

{docstring Substring.Raw.any}

# Comparisons

{docstring Substring.Raw.beq}

{docstring Substring.Raw.sameAs}

# Prefix and Suffix

{docstring Substring.Raw.commonPrefix}

{docstring Substring.Raw.commonSuffix}

{docstring Substring.Raw.dropPrefix?}

{docstring Substring.Raw.dropSuffix?}

# Lookups

{docstring Substring.Raw.get}

{docstring Substring.Raw.contains}

{docstring Substring.Raw.front}


# Modifications

{docstring Substring.Raw.drop}

{docstring Substring.Raw.dropWhile}

{docstring Substring.Raw.dropRight}

{docstring Substring.Raw.dropRightWhile}


{docstring Substring.Raw.take}

{docstring Substring.Raw.takeWhile}

{docstring Substring.Raw.takeRight}

{docstring Substring.Raw.takeRightWhile}

{docstring Substring.Raw.extract}

{docstring Substring.Raw.trim}

{docstring Substring.Raw.trimLeft}

{docstring Substring.Raw.trimRight}

{docstring Substring.Raw.splitOn}

{docstring Substring.Raw.repair}

# Conversions

{docstring Substring.Raw.toString}

{docstring Substring.Raw.isNat}

{docstring Substring.Raw.toNat? +allowMissing}

{docstring Substring.Raw.toLegacyIterator}

{docstring Substring.Raw.toName}
