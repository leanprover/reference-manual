/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.String.Logical
import Manual.BasicTypes.String.Literals
import Manual.BasicTypes.String.FFI
import Manual.BasicTypes.String.Substrings
import Manual.BasicTypes.String.Slice

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 250000


#doc (Manual) "Strings" =>
%%%
tag := "String"
%%%


Strings represent Unicode text.
Strings are specially supported by Lean:
 * They have a _logical model_ that specifies their behavior in terms of {name}`ByteArray`s that contain UTF-8 scalar values.
 * In compiled code, they have a run-time representation that additionally includes a cached length, measured as the number of scalar values.
   The Lean runtime provides optimized implementations of string operations.
 * There is {ref "string-syntax"}[string literal syntax] for writing strings.

UTF-8 is a variable-width encoding.
A character may be encoded as a one, two, three, or four byte code unit.
The fact that strings are UTF-8-encoded byte arrays is visible in the API:
 * There is no operation to project a particular character out of the string, as this would be a performance trap. {ref "string-iterators"}[Use an iterator] in a loop instead of a {name}`Nat`.
 * Strings are indexed by {name}`String.ValidPos`, which internally records _byte counts_ rather than _character counts_, and thus takes constant time.
   {name}`String.ValidPos` includes a proof that the byte count in fact points at the beginning of a UTF-8 code unit.
   Aside from `0`, these should not be constructed directly, but rather updated using {name}`String.next` and {name}`String.prev`.

{include 0 Manual.BasicTypes.String.Logical}

# Run-Time Representation
%%%
tag := "string-runtime"
%%%

:::figure "Memory layout of strings" (tag := "stringffi")
![Memory layout of strings](/static/figures/string.svg)
:::

Strings are represented as {tech}[dynamic arrays] of bytes, encoded in UTF-8.
After the object header, a string contains:

: byte count

  The number of bytes that currently contain valid string data

: capacity

  The number of bytes presently allocated for the string

: length

  The length of the encoded string, which may be shorter than the byte count due to UTF-8 multi-byte characters

: data

  The actual character data in the string, null-terminated

Many string functions in the Lean runtime check whether they have exclusive access to their argument by consulting the reference count in the object header.
If they do, and the string's capacity is sufficient, then the existing string can be mutated rather than allocating fresh memory.
Otherwise, a new string must be allocated.


## Performance Notes
%%%
tag := "string-performance"
%%%

Despite the fact that they appear to be an ordinary constructor and projection, {name}`String.ofByteArray` and {name}`String.bytes` take *time linear in the length of the string*.
This is because byte arrays and strings do not have an identical representation, so the contents of the byte array must be copied to a new object.


{include 0 Manual.BasicTypes.String.Literals}

# API Reference
%%%
tag := "string-api"
%%%


## Constructing
%%%
tag := "string-api-build"
%%%


{docstring String.singleton}

{docstring String.append}

{docstring String.join}

{docstring String.intercalate}

## Conversions
%%%
tag := "string-api-convert"
%%%


{docstring String.toList}

{docstring String.isNat}

{docstring String.toNat?}

{docstring String.toNat!}

{docstring String.isInt}

{docstring String.toInt?}

{docstring String.toInt!}

{docstring String.toFormat}

## Properties
%%%
tag := "string-api-props"
%%%

{docstring String.isEmpty}

{docstring String.length}

## Positions
%%%
tag := "string-api-valid-pos"
%%%

{docstring String.ValidPos}

### In Strings

{docstring String.startValidPos}

{docstring String.endValidPos}

{docstring String.pos}

{docstring String.pos?}

{docstring String.pos!}

### Lookups

{docstring String.ValidPos.get}

{docstring String.ValidPos.get!}

{docstring String.ValidPos.get?}

{docstring String.ValidPos.set}

{docstring String.ValidPos.extract +allowMissing}

### Modifications

{docstring String.ValidPos.modify}

{docstring String.ValidPos.byte}

### Adjustment

{docstring String.ValidPos.prev}

{docstring String.ValidPos.prev!}

{docstring String.ValidPos.prev?}

{docstring String.ValidPos.next}

{docstring String.ValidPos.next!}

{docstring String.ValidPos.next?}

### Other Strings

{docstring String.ValidPos.cast}

{docstring String.ValidPos.ofCopy}

{docstring String.ValidPos.toSetOfLE}

{docstring String.ValidPos.toModifyOfLE}

{docstring String.ValidPos.toSlice}

## Raw Positions
%%%
tag := "string-api-pos"
%%%

{docstring String.Pos.Raw}

### Validity

{docstring String.Pos.Raw.isValid}

{docstring String.Pos.Raw.isValidForSlice}

### Boundaries

{docstring String.rawEndPos}

{docstring String.Pos.Raw.atEnd}

### Comparisons

{docstring String.Pos.Raw.min}

{docstring String.Pos.Raw.byteDistance}

{docstring String.Pos.Raw.substrEq}

### Adjustment

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

### String Lookups

{docstring String.Pos.Raw.extract}

{docstring String.Pos.Raw.get}

{docstring String.Pos.Raw.get!}

{docstring String.Pos.Raw.get'}

{docstring String.Pos.Raw.get?}

### String Modifications

{docstring String.Pos.Raw.set}

{docstring String.Pos.Raw.modify}

## Lookups and Modifications
%%%
tag := "string-api-lookup"
%%%

{docstring String.take}

{docstring String.takeWhile}

{docstring String.takeRight}

{docstring String.takeRightWhile}

{docstring String.drop}

{docstring String.dropWhile}

{docstring String.dropRight}

{docstring String.dropRightWhile}

{docstring String.dropPrefix?}

{docstring String.stripPrefix}

{docstring String.dropSuffix?}

{docstring String.stripSuffix}

{docstring String.trim}

{docstring String.trimLeft}

{docstring String.trimRight}

{docstring String.removeLeadingSpaces}

{docstring String.front}

{docstring String.back}

{docstring String.posOf}

{docstring String.revPosOf}

{docstring String.contains}

{docstring String.offsetOfPos}

{docstring String.replace}

{docstring String.findLineStart}

{docstring String.find}

{docstring String.revFind}


## Folds and Aggregation
%%%
tag := "string-api-fold"
%%%

{docstring String.map}

{docstring String.foldl}

{docstring String.foldr}

{docstring String.all}

{docstring String.any}

## Comparisons
%%%
tag := "string-api-compare"
%%%

The {inst}`LT String` instance is defined by the lexicographic ordering on strings based on the {inst}`LT Char` instance.
Logically, this is modeled by the lexicographic ordering on the lists that model strings, so `List.Lex` defines the order.
It is decidable, and the decision procedure is overridden at runtime with efficient code that takes advantage of the run-time representation of strings.

{docstring String.le}

{docstring String.firstDiffPos}

{docstring String.isPrefixOf}

{docstring String.startsWith}

{docstring String.endsWith}

{docstring String.decEq}

{docstring String.hash}

## Manipulation
%%%
tag := "string-api-modify"
%%%

{docstring String.splitToList}

{docstring String.splitOn}

{docstring String.push}

{docstring String.pushn}

{docstring String.capitalize}

{docstring String.decapitalize}

{docstring String.toUpper}

{docstring String.toLower}

## Legacy Iterators
%%%
tag := "string-iterators"
%%%

For backwards compatiblity, Lean includes legacy string interators.
Fundamentally, a {name}`String.Legacy.Iterator` is a pair of a string and a valid position in the string.
Iterators provide functions for getting the current character ({name String.Legacy.Iterator.curr}`curr`), replacing the current character ({name String.Legacy.Iterator.setCurr}`setCurr`), checking whether the iterator can move to the left or the right ({name String.Legacy.Iterator.hasPrev}`hasPrev` and {name String.Legacy.Iterator.hasNext}`hasNext`, respectively), and moving the iterator ({name String.Legacy.Iterator.prev}`prev` and {name String.Legacy.Iterator.next}`next`, respectively).
Clients are responsible for checking whether they've reached the beginning or end of the string; otherwise, the iterator ensures that its position always points at a character.
However, {name}`String.Legacy.Iterator` does not include proofs of these well-formedness conditions, which can make it more difficult to use in verified code.

{docstring String.Legacy.Iterator}

{docstring String.Legacy.iter}

{docstring String.Legacy.mkIterator}

{docstring String.Legacy.Iterator.curr}

{docstring String.Legacy.Iterator.curr'}

{docstring String.Legacy.Iterator.hasNext}

{docstring String.Legacy.Iterator.next}

{docstring String.Legacy.Iterator.next'}

{docstring String.Legacy.Iterator.forward}

{docstring String.Legacy.Iterator.nextn}

{docstring String.Legacy.Iterator.hasPrev}

{docstring String.Legacy.Iterator.prev}

{docstring String.Legacy.Iterator.prevn}

{docstring String.Legacy.Iterator.atEnd}

{docstring String.Legacy.Iterator.toEnd}

{docstring String.Legacy.Iterator.setCurr}

{docstring String.Legacy.Iterator.find}

{docstring String.Legacy.Iterator.foldUntil}

{docstring String.Legacy.Iterator.extract}

{docstring String.Legacy.Iterator.remainingToString}

{docstring String.Legacy.Iterator.remainingBytes}

{docstring String.Legacy.Iterator.pos}

{docstring String.Legacy.Iterator.toString}

{include 2 Manual.BasicTypes.String.Slice}

{include 2 Manual.BasicTypes.String.Substrings}





## Metaprogramming
%%%
tag := "string-api-meta"
%%%

{docstring String.toName}

{docstring String.quote}


## Encodings
%%%
tag := "string-api-encoding"
%%%

{docstring String.getUTF8Byte}

{docstring String.utf8ByteSize}

{docstring String.utf8EncodeChar}

{docstring String.fromUTF8}

{docstring String.fromUTF8?}

{docstring String.fromUTF8!}

{docstring String.toUTF8}

{docstring String.crlfToLf}


{include 0 Manual.BasicTypes.String.FFI}
