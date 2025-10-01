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

#doc (Manual) "Strings" =>
%%%
tag := "String"
%%%


Strings represent Unicode text.
Strings are specially supported by Lean:
 * They have a _logical model_ that specifies their behavior in terms of {name}`ByteArray`s that contain UTF-8 scalar values.
 * In compiled code, they have a run-time representation that additionally includes a cached length, measured as the number of scalar values.
   Additionally, the Lean runtime contains optimized implementations of string operations.
 * There is {ref "string-syntax"}[string literal syntax] for writing strings.

UTF-8 is a variable-width encoding.
A character may be encoded as a one, two, three, or four byte code unit.
The fact that strings are UTF-8-encoded byte arrays is visible in the API:
 * There is no operation to project a particular character out of the string, as this would be a performance trap. {ref "string-iterators"}[Use a {name}`String.Iterator`] in a loop instead of a {name}`Nat`.
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


Despite the fact that they appear to be an ordinary constructor and projection, {name}`String.mk` and {name}`String.data` take *time linear in the length of the string*.
This is because they must implement the conversions between lists of characters and packed arrays of bytes, which must necessarily visit each character.

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
tag := "string-api-pos"
%%%

{docstring String.Pos}

{docstring String.Pos.isValid}

{docstring String.Pos.isValidForSlice}

{docstring String.atEnd}

{docstring String.endPos}

{docstring String.next}

{docstring String.next'}

{docstring String.nextWhile}

{docstring String.nextUntil}

{docstring String.prev}

{docstring String.Pos.min}

{docstring String.Pos.inc}

{docstring String.Pos.dec}

## Lookups and Modifications
%%%
tag := "string-api-lookup"
%%%

{docstring String.get}

{docstring String.get?}

{docstring String.get!}

{docstring String.get'}

{docstring String.extract}

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

{docstring String.set}

{docstring String.modify}

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

{docstring String.substrEq}

{docstring String.isPrefixOf}

{docstring String.startsWith}

{docstring String.endsWith}

{docstring String.decEq}

{docstring String.hash}

## Manipulation
%%%
tag := "string-api-modify"
%%%

{docstring String.split}

{docstring String.splitOn}

{docstring String.push}

{docstring String.pushn}

{docstring String.capitalize}

{docstring String.decapitalize}

{docstring String.toUpper}

{docstring String.toLower}

## Iterators
%%%
tag := "string-iterators"
%%%

Fundamentally, a {name}`String.Iterator` is a pair of a string and a valid position in the string.
Iterators provide functions for getting the current character ({name String.Iterator.curr}`curr`), replacing the current character ({name String.Iterator.setCurr}`setCurr`), checking whether the iterator can move to the left or the right ({name String.Iterator.hasPrev}`hasPrev` and {name String.Iterator.hasNext}`hasNext`, respectively), and moving the iterator ({name String.Iterator.prev}`prev` and {name String.Iterator.next}`next`, respectively).
Clients are responsible for checking whether they've reached the beginning or end of the string; otherwise, the iterator ensures that its position always points at a character.

{docstring String.Iterator}

{docstring String.iter}

{docstring String.mkIterator}

{docstring String.Iterator.curr}

{docstring String.Iterator.curr'}

{docstring String.Iterator.hasNext}

{docstring String.Iterator.next}

{docstring String.Iterator.next'}

{docstring String.Iterator.forward}

{docstring String.Iterator.nextn}

{docstring String.Iterator.hasPrev}

{docstring String.Iterator.prev}

{docstring String.Iterator.prevn}

{docstring String.Iterator.atEnd}

{docstring String.Iterator.toEnd}

{docstring String.Iterator.setCurr}

{docstring String.Iterator.find}

{docstring String.Iterator.foldUntil}

{docstring String.Iterator.extract}

{docstring String.Iterator.remainingToString}

{docstring String.Iterator.remainingBytes}

{docstring String.Iterator.pos}

{docstring String.Iterator.toString}


{include 2 Manual.BasicTypes.String.Substrings}

{include 2 Manual.BasicTypes.String.Slice}



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

{docstring String.getUtf8Byte}

{docstring String.utf8ByteSize}

{docstring String.utf8EncodeChar}

{docstring String.utf8DecodeChar?}

{docstring String.fromUTF8}

{docstring String.fromUTF8?}

{docstring String.fromUTF8!}

{docstring String.toUTF8}

{docstring String.validateUTF8}

{docstring String.crlfToLf}


{include 0 Manual.BasicTypes.String.FFI}
