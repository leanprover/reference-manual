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

open Verso.Genre Manual InlineLean

set_option pp.rawOnError true

example := Char

#doc (Manual) "Arrays" =>
%%%
tag := "Array"
%%%

The {lean}`Array` type represents sequences of elements, addressable by their position in the sequence.
Arrays are specially supported by Lean:
 * They have a _logical model_ that specifies their behavior in terms of lists of elements, which specifies the meaning of each operation on arrays.
 * They have an optimized run-time representation in compiled code as {tech}[dynamic arrays], and the Lean runtime specially optimizes array operations.
 * There is {ref "array-syntax"}[array literal syntax] for writing arrays.

Arrays can be vastly more efficient than lists or other sequences in compiled code.
In part, this is because they offer good locality: because all the elements of the sequence are next to each other in memory, the processor's caches can be used efficiently.
Even more importantly, if there is only a single reference to an array, operations that might otherwise copy or allocate a data structure can be implemented via mutation.
Lean code that uses an array in such a way that there's only ever one unique reference (that is, uses it {deftech}_linearly_) avoids the performance overhead of persistent data structures while still being as convenient to write, read, and prove things about as ordinary pure functional programs.

# Logical Model

{docstring Array}

The logical model of arrays is a structure that contains a single field, which is a list of elements.
This is convenient when specifying and proving properties of array-processing functions at a low level.

# Run-Time Representation
%%%
tag := "array-runtime"
%%%

Lean's arrays are {deftech}_dynamic arrays_, which are blocks of continuous memory with a defined capacity, not all of which is typically in use.
As long as the number of elements in the array is less than the capacity, new items can be added to the end without reallocating or moving the data.
Adding items to an array that has no extra space results in a reallocation that doubles the capacity.
The amortized overhead scales linearly with the size of the array.
The values in the array are represented as described in the {ref "inductive-types-ffi"}[section on the foreign function interface].

:::figure "Memory layout of arrays" (tag := "arrayffi")
![Memory layout of arrays](/static/figures/array.svg)
:::

After the object header, an array contains:

: size

  The number of objects currently stored in the array

: capacity

  The number of objects that fit in the memory allocated for the array

: data

  The values in the array

Many array functions in the Lean runtime check whether they have exclusive access to their argument by consulting the reference count in the object header.
If they do, and the array's capacity is sufficient, then the existing array can be mutated rather than allocating fresh memory.
Otherwise, a new array must be allocated.

## Performance Notes
%%%
tag := "array-performance"
%%%


Despite the fact that they appear to be an ordinary constructor and projection, {name}`Array.mk` and {name}`Array.toList` take *time linear in the size of the array* in compiled code.
This is because converting between linked lists and packed arrays must necessarily visit each element.

Mutable arrays can be used to write very efficient code.
However, they are a poor persistent data structure.
Updating a shared array rules out mutation, and requires time linear in the size of the array.
When using arrays in performance-critical code, it's important to ensure that they are used {tech}[linearly].

# Syntax
%%%
tag := "array-syntax"
%%%

Array literals allow arrays to be written directly in code.
They may be used in expression or pattern contexts.

:::syntax term (title := "Array Literals")
Array literals begin with `#[` and contain a comma-separated sequence of terms, terminating with `]`.

```grammar
#[$t,*]
```
:::

::::keepEnv
:::example "Array Literals"
Array literals may be used as expressions or as patterns.

```lean
def oneTwoThree : Array Nat := #[1, 2, 3]

#eval
  match oneTwoThree with
  | #[x, y, z] => some ((x + z) / y)
  | _ => none
```
:::
::::

Additionally, {ref "subarray"}[sub-arrays] may be extracted using the following syntax:
:::syntax term (title := "Sub-Arrays")
A start index followed by a colon constructs a sub-array that contains the values from the start index onwards (inclusive):
```grammar
$t[$t:term :]
```

Providing start and end indices  constructs a sub-array that contains the values from the start index (inclusive) to the end index (exclusive):
```grammar
$t[$t:term : $_:term]
```
:::

::::keepEnv
:::example "Sub-Array Syntax"

The array {lean}`ten` contains the first ten natural numbers.
```lean
def ten : Array Nat :=
  .range 10
```

A sub-array that represents the second half of {lean}`ten` can be constructed using the sub-array syntax:
```lean (name := subarr1)
#eval ten[5:]
```
```leanOutput subarr1
#[5, 6, 7, 8, 9].toSubarray
```

Similarly, sub-array that contains two through five can be constructed by providing a stopping point:
```lean (name := subarr2)
#eval ten[2:6]
```
```leanOutput subarr2
#[2, 3, 4, 5].toSubarray
```

Because sub-arrays merely store the start and end indices of interest in the underlying array, the array itself can be recovered:
```lean (name := subarr3)
#eval ten[2:6].array == ten
```
```leanOutput subarr3
true
```
:::
::::

# API Reference
%%%
tag := "array-api"
%%%

## Constructing Arrays

{docstring Array.empty}

{docstring Array.emptyWithCapacity}

{docstring Array.singleton}

{docstring Array.range}

{docstring Array.range'}

{docstring Array.finRange}

{docstring Array.ofFn}

{docstring Array.replicate}

{docstring Array.append}

{docstring Array.appendList}

{docstring Array.leftpad}

{docstring Array.rightpad}

## Size

{docstring Array.size}

{docstring Array.usize}

{docstring Array.isEmpty}

## Lookups

{docstring Array.extract}

{docstring Array.getD}

{docstring Array.uget}

{docstring Array.back}

{docstring Array.back?}

{docstring Array.back!}

{docstring Array.getMax?}

## Queries

{docstring Array.count}

{docstring Array.countP}

{docstring Array.idxOf}

{docstring Array.idxOf?}

{docstring Array.finIdxOf?}

## Conversions

{docstring Array.toList}

{docstring Array.toListRev}

{docstring Array.toListAppend}

{docstring Array.toVector}

{docstring Array.toSubarray}

{docstring Array.ofSubarray}


## Modification

{docstring Array.push}

{docstring Array.pop}

{docstring Array.popWhile}

{docstring Array.erase}

{docstring Array.eraseP}

{docstring Array.eraseIdx}

{docstring Array.eraseIdx!}

{docstring Array.eraseIdxIfInBounds}

{docstring Array.eraseReps}

{docstring Array.swap}

{docstring Array.swapIfInBounds}

{docstring Array.swapAt}

{docstring Array.swapAt!}

{docstring Array.replace}

{docstring Array.set}

{docstring Array.set!}

{docstring Array.setIfInBounds}

{docstring Array.uset}

{docstring Array.modify}

{docstring Array.modifyM}

{docstring Array.modifyOp}

{docstring Array.insertIdx}

{docstring Array.insertIdx!}

{docstring Array.insertIdxIfInBounds}

{docstring Array.reverse}

{docstring Array.take}

{docstring Array.takeWhile}

{docstring Array.drop}

{docstring Array.shrink}

{docstring Array.flatten}

{docstring Array.getEvenElems}

## Sorted Arrays

{docstring Array.qsort}

{docstring Array.qsortOrd}

{docstring Array.insertionSort}

{docstring Array.binInsert}

{docstring Array.binInsertM}

{docstring Array.binSearch}

{docstring Array.binSearchContains}

## Iteration

{docstring Array.foldr}

{docstring Array.foldrM}

{docstring Array.foldl}

{docstring Array.foldlM}

{docstring Array.forM}

{docstring Array.forRevM}

{docstring Array.firstM}

{docstring Array.sum}

## Transformation

{docstring Array.map}

{docstring Array.mapMono}

{docstring Array.mapM}

{docstring Array.mapM'}

{docstring Array.mapMonoM}

{docstring Array.mapIdx}

{docstring Array.mapIdxM}

{docstring Array.mapFinIdx}

{docstring Array.mapFinIdxM}

{docstring Array.flatMap}

{docstring Array.flatMapM}

{docstring Array.zip}

{docstring Array.zipWith}

{docstring Array.zipWithAll}

{docstring Array.zipIdx}

{docstring Array.unzip}


## Filtering

{docstring Array.filter}

{docstring Array.filterM}

{docstring Array.filterRevM}

{docstring Array.filterMap}

{docstring Array.filterMapM}

{docstring Array.filterSepElems}

{docstring Array.filterSepElemsM}

## Partitioning

{docstring Array.partition}

{docstring Array.groupByKey}


## Element Predicates

{docstring Array.contains}

{docstring Array.elem}

{docstring Array.find?}

{docstring Array.findRev?}

{docstring Array.findIdx}

{docstring Array.findIdx?}

{docstring Array.findIdxM?}

{docstring Array.findFinIdx?}

{docstring Array.findM?}

{docstring Array.findRevM?}

{docstring Array.findSome?}

{docstring Array.findSome!}

{docstring Array.findSomeM?}

{docstring Array.findSomeRev?}

{docstring Array.findSomeRevM?}

{docstring Array.all}

{docstring Array.allM}

{docstring Array.any}

{docstring Array.anyM}

{docstring Array.allDiff}

{docstring Array.isEqv}

## Comparisons

{docstring Array.isPrefixOf}

{docstring Array.lex}

## Termination Helpers

{docstring Array.attach}

{docstring Array.attachWith}

{docstring Array.unattach}

{docstring Array.pmap}

{include 1 Manual.BasicTypes.Array.Subarray}

{include 0 Manual.BasicTypes.Array.FFI}
