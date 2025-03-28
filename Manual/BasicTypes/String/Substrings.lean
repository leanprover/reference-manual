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

#doc (Manual) "Substrings" =>
%%%
tag := "string-api-substring"
%%%


{docstring String.toSubstring}

{docstring String.toSubstring'}

{docstring Substring}

# Properties

{docstring Substring.isEmpty}

{docstring Substring.bsize}

# Positions

{docstring Substring.atEnd}

{docstring Substring.posOf}

{docstring Substring.next}

{docstring Substring.nextn}

{docstring Substring.prev}

{docstring Substring.prevn}


# Folds and Aggregation

{docstring Substring.foldl}

{docstring Substring.foldr}

{docstring Substring.all}

{docstring Substring.any}

# Comparisons

{docstring Substring.beq}

{docstring Substring.sameAs}

# Prefix and Suffix

{docstring Substring.commonPrefix}

{docstring Substring.commonSuffix}

{docstring Substring.dropPrefix?}

{docstring Substring.dropSuffix?}

# Lookups

{docstring Substring.get}

{docstring Substring.contains}

{docstring Substring.front}


# Modifications

{docstring Substring.drop}

{docstring Substring.dropWhile}

{docstring Substring.dropRight}

{docstring Substring.dropRightWhile}


{docstring Substring.take}

{docstring Substring.takeWhile}

{docstring Substring.takeRight}

{docstring Substring.takeRightWhile}

{docstring Substring.extract}

{docstring Substring.trim}

{docstring Substring.trimLeft}

{docstring Substring.trimRight}

{docstring Substring.splitOn}


# Conversions

{docstring Substring.toString}

{docstring Substring.isNat}

{docstring Substring.toNat? (allowMissing := true)}

{docstring Substring.toIterator}

{docstring Substring.toName}
