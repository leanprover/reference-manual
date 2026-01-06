/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true -- TODO remove after docstrings are merged

example := Char

#doc (Manual) "Byte Arrays" =>
%%%
tag := "ByteArray"
%%%

Byte arrays are a specialized array type that can only contain elements of type {name}`UInt8`.
Due to this restriction, they can use a much more efficient representation, with no pointer indirections.
Like other arrays, byte arrays are represented in compiled code as {tech}[dynamic arrays], and the Lean runtime specially optimizes array operations.
The operations that modify byte arrays first check the array's {ref "reference-counting"}[reference count], and if there are no other references to the array, it is modified in place.

There is no literal syntax for byte arrays.
{name}`List.toByteArray` can be used to construct an array from a list literal.

{docstring ByteArray}

# API Reference

## Constructing Byte Arrays

{docstring ByteArray.empty}

{docstring ByteArray.emptyWithCapacity}

{docstring ByteArray.append}

{docstring ByteArray.fastAppend}

{docstring ByteArray.copySlice}

## Size

{docstring ByteArray.size}

{docstring ByteArray.usize}

{docstring ByteArray.isEmpty}

## Lookups

{docstring ByteArray.get}

{docstring ByteArray.uget}

{docstring ByteArray.get!}

{docstring ByteArray.extract}

## Conversions

{docstring ByteArray.toList}

{docstring ByteArray.toUInt64BE!}

{docstring ByteArray.toUInt64LE!}

### UTF-8

{docstring ByteArray.utf8Decode?}

{docstring ByteArray.utf8DecodeChar?}

{docstring ByteArray.utf8DecodeChar}

## Modification

{docstring ByteArray.push}

{docstring ByteArray.set}

{docstring ByteArray.uset}

{docstring ByteArray.set!}

## Iteration

{docstring ByteArray.foldl}

{docstring ByteArray.foldlM}

{docstring ByteArray.forIn}

## Iterators

{docstring ByteArray.iter}

{docstring ByteArray.Iterator}

{docstring ByteArray.Iterator.pos}

{docstring ByteArray.Iterator.atEnd}

{docstring ByteArray.Iterator.hasNext}

{docstring ByteArray.Iterator.hasPrev}

{docstring ByteArray.Iterator.curr}

{docstring ByteArray.Iterator.curr'}

{docstring ByteArray.Iterator.next}

{docstring ByteArray.Iterator.next'}

{docstring ByteArray.Iterator.forward}

{docstring ByteArray.Iterator.nextn}

{docstring ByteArray.Iterator.prev}

{docstring ByteArray.Iterator.prevn}

{docstring ByteArray.Iterator.remainingBytes}

{docstring ByteArray.Iterator.toEnd}

## Slices

{docstring ByteArray.toByteSlice}

{docstring ByteSlice}

{docstring ByteSlice.beq}

{docstring ByteSlice.byteArray}

{docstring ByteSlice.contains}

{docstring ByteSlice.empty}

{docstring ByteSlice.foldr}

{docstring ByteSlice.foldrM}

{docstring ByteSlice.forM}

{docstring ByteSlice.get}

{docstring ByteSlice.get!}

{docstring ByteSlice.getD}

{docstring ByteSlice.ofByteArray}

{docstring ByteSlice.size}

{docstring ByteSlice.slice}

{docstring ByteSlice.start}

{docstring ByteSlice.stop}

{docstring ByteSlice.toByteArray}


## Element Predicates

{docstring ByteArray.findIdx?}

{docstring ByteArray.findFinIdx?}
