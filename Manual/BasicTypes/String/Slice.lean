/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "String Slices" =>
%%%
tag := "string-api-slice"
%%%

{docstring String.Slice}

{docstring String.toSlice}

{docstring String.replaceStart}

{docstring String.replaceEnd}

{docstring String.Slice.Pos}

# API Reference

## Copying

{docstring String.Slice.copy}

## Size

{docstring String.Slice.isEmpty}

{docstring String.Slice.utf8ByteSize}

## Boundaries

{docstring String.Slice.pos}

{docstring String.Slice.pos!}

{docstring String.Slice.pos?}

{docstring String.Slice.startPos}

{docstring String.Slice.endPos}

{docstring String.Slice.rawEndPos}


### Adjustment

{docstring String.Slice.replaceStart}

{docstring String.Slice.replaceStartEnd}

{docstring String.Slice.replaceStartEnd!}

{docstring String.Slice.drop}

{docstring String.Slice.dropEnd}

{docstring String.Slice.dropEndWhile}

{docstring String.Slice.dropPrefix}

{docstring String.Slice.dropPrefix?}

{docstring String.Slice.dropSuffix}

{docstring String.Slice.dropSuffix?}

{docstring String.Slice.dropWhile}

{docstring String.Slice.take}

{docstring String.Slice.takeEnd}

{docstring String.Slice.takeEndWhile}

{docstring String.Slice.takeWhile}

## Characters

{docstring String.Slice.front}

{docstring String.Slice.front?}

{docstring String.Slice.back}

{docstring String.Slice.back?}

## Bytes

{docstring String.Slice.getUTF8Byte}

{docstring String.Slice.getUTF8Byte!}

## Positions

{docstring String.Slice.findNextPos}

## Searching

{docstring String.Slice.contains}

{docstring String.Slice.startsWith}

{docstring String.Slice.endsWith}

{docstring String.Slice.all}

{docstring String.Slice.find?}

{docstring String.Slice.revFind?}

## Manipulation

{docstring String.Slice.split}

{docstring String.Slice.splitInclusive}

{docstring String.Slice.lines}

{docstring String.Slice.replaceEnd}

{docstring String.Slice.trimAscii}

{docstring String.Slice.trimAsciiEnd}

{docstring String.Slice.trimAsciiStart}

## Iteration

{docstring String.Slice.chars}

{docstring String.Slice.revChars}

{docstring String.Slice.positions}

{docstring String.Slice.revPositions}

{docstring String.Slice.bytes}

{docstring String.Slice.revBytes}

{docstring String.Slice.revSplit}

{docstring String.Slice.foldl}

{docstring String.Slice.foldr}

## Conversions

{docstring String.Slice.isNat}

{docstring String.Slice.toNat!}

{docstring String.Slice.toNat?}


## Equality

{docstring String.Slice.beq}

{docstring String.Slice.eqIgnoreAsciiCase}


# Patterns

String slices feature generalized search patterns.
Rather than being defined to work only for characters or for strings, many operations on slices accept arbitrary patterns.
New types can be made into patterns by defining instances of the classes in this section.
The Lean standard library instances that allow the following types to be used for both forward and backward searching:

:::table +header
* * Pattern Type
  * Meaning
* * {name}`Char`
  * Matches the provided character
*
  * {lean}`Char → Bool`
  * Matches any character that satisfies the predicate
* * {lean}`String`
  * Matches occurrences of the given string
* * {lean}`String.Slice`
  * Matches occurrences of the string represented by the slice
:::

{docstring String.Slice.Pattern.ToForwardSearcher}

{docstring String.Slice.Pattern.ForwardPattern}

{docstring String.Slice.Pattern.ToBackwardSearcher}

{docstring String.Slice.Pattern.BackwardPattern +allowMissing}

# Positions

## Lookups

Because they retain a reference to the slice from which they were drawn, slice positions allow individual characters or bytes to be looked up.

{docstring String.Slice.Pos.byte}

{docstring String.Slice.Pos.get}

{docstring String.Slice.Pos.get!}

{docstring String.Slice.Pos.get?}

## Incrementing and Decrementing

{docstring String.Slice.Pos.prev}

{docstring String.Slice.Pos.prev!}

{docstring String.Slice.Pos.prev?}

{docstring String.Slice.Pos.prevn}

{docstring String.Slice.Pos.next}

{docstring String.Slice.Pos.next!}

{docstring String.Slice.Pos.next?}

{docstring String.Slice.Pos.nextn}

## Other Strings or Slices

{docstring String.Slice.Pos.cast}

{docstring String.Slice.Pos.ofSlice}

{docstring String.Slice.Pos.str}

{docstring String.Slice.Pos.toCopy}

{docstring String.Slice.Pos.ofReplaceStart}

{docstring String.Slice.Pos.toReplaceStart}
