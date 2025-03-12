/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


#doc (Manual) "Linked Lists" =>
%%%
tag := "List"
%%%

Linked lists, implemented as the {tech}[inductive type] {name}`List`, contain an ordered sequence of elements.
Unlike {ref "Array"}[arrays], Lean compiles lists according to the ordinary rules for inductive types; however, some operations on lists are replaced by tail-recursive equivalents in compiled code using the {attr}`csimp` mechanism.{TODO}[Write and xref from here]
Lean provides syntax for both literal lists and the constructor {name}`List.cons`.

{docstring List}

# Syntax
%%%
tag := "list-syntax"
%%%

List literals are written in square brackets, with the elements of the list separated by commas.
The constructor {name}`List.cons` that adds an element to the front of a list is represented by the infix operator {keywordOf «term_::_»}`::`.
The syntax for lists can be used both in ordinary terms and in patterns.

:::syntax term (title := "List Literals")
```grammar
[$_,*]
```

{includeDocstring «term[_]»}

:::

:::syntax term (title := "List Construction")
```grammar
$_ :: $_
```

{includeDocstring «term_::_»}

:::

:::example "Constructing Lists"
All of these examples are equivalent:
```lean
example : List Nat := [1, 2, 3]
example : List Nat := 1 :: [2, 3]
example : List Nat := 1 :: 2 :: [3]
example : List Nat := 1 :: 2 :: 3 :: []
example : List Nat := 1 :: 2 :: 3 :: .nil
example : List Nat := 1 :: 2 :: .cons 3 .nil
example : List Nat := .cons 1 (.cons 2 (.cons 3 .nil))
```
:::

:::example "Pattern Matching and Lists"
All of these functions are equivalent:
```lean
def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: x' :: xs =>
    let (ys, zs) := split xs
    (x :: ys, x' :: zs)
```
```lean
def split' : List α → List α × List α
  | .nil => (.nil, .nil)
  | x :: [] => (.singleton x, .nil)
  | x :: x' :: xs =>
    let (ys, zs) := split xs
    (x :: ys, x' :: zs)
```
```lean
def split'' : List α → List α × List α
  | .nil => (.nil, .nil)
  | .cons x .nil=> (.singleton x, .nil)
  | .cons x (.cons x' xs) =>
    let (ys, zs) := split xs
    (.cons x ys, .cons x' zs)
```
```lean (show := false)
-- Test claim
example : @split = @split' := by
  funext α xs
  induction xs using split.induct <;> simp [split, split', List.singleton]

example : @split = @split'' := by
  funext α xs
  induction xs using split.induct <;> simp [split, split'', List.singleton]
```
:::


# Performance Notes
%%%
tag := "list-performance"
%%%

The representation of lists is not overridden or modified by the compiler: they are linked lists, with a pointer indirection for each element.
Calculating the length of a list requires a full traversal, and modifying an element in a list requires a traversal and reallocation of the prefix of the list that is prior to the element being modified.
Due to Lean's reference-counting-based memory management, operations such as {name}`List.map` that traverse a list, allocating a new {name}`List.cons` constructor for each in the prior list, can re-use the original list's memory when there are no other references to it.

Because of the important role played by lists in specifications, most list functions are written as straightforwardly as possible using structural recursion.
This makes it easier to write proofs by induction, but it also means that these operations consume stack space proportional to the length of the list.
There are tail-recursive versions of many list functions that are equivalent to the non-tail-recursive versions, but more are difficult to use when reasoning.
In compiled code, the tail-recursive versions are automatically used instead of the non-tail-recursive versions.

# API Reference
%%%
tag := "list-api-reference"
%%%

## Predicates and Relations

{docstring List.IsPrefix}

:::syntax term (title := "List Prefix")
```grammar
$_ <+: $_
```

{includeDocstring List.«term_<+:_»}

:::

{docstring List.IsSuffix}

:::syntax term (title := "List Suffix")
```grammar
$_ <:+ $_
```

{includeDocstring List.«term_<:+_»}

:::

{docstring List.IsInfix}

:::syntax term (title := "List Infix")
```grammar
$_ <:+: $_
```

{includeDocstring List.«term_<:+:_»}

:::

{docstring List.Sublist}

::: syntax term (title := "Sublists") (namespace := List)
```grammar
$_ <+ $_
```

{includeDocstring List.«term_<+_»}

This syntax is only available when the `List` namespace is opened.
:::

{docstring List.Perm}

:::syntax term (title := "List Permutation") (namespace := List)
```grammar
$_ ~ $_
```

{includeDocstring List.«term_~_»}

This syntax is only available when the `List` namespace is opened.
:::

{docstring List.Pairwise}

{docstring List.Nodup}

{docstring List.Lex}

{docstring List.Mem}


## Constructing Lists

{docstring List.singleton}

{docstring List.concat}

{docstring List.replicate}

{docstring List.replicateTR}

{docstring List.ofFn}

{docstring List.append}

{docstring List.appendTR}

{docstring List.range}

{docstring List.range'}

{docstring List.range'TR}

{docstring List.finRange}

## Length

{docstring List.length}

{docstring List.lengthTR}

{docstring List.isEmpty}

## Head and Tail

{docstring List.head}

{docstring List.head?}

{docstring List.headD}

{docstring List.head!}

{docstring List.tail}

{docstring List.tail!}

{docstring List.tail?}

{docstring List.tailD}


## Lookups

{docstring List.get}

{docstring List.getD}

{docstring List.getLast}

{docstring List.getLast?}

{docstring List.getLastD}

{docstring List.getLast!}

{docstring List.lookup}

{docstring List.max?}

{docstring List.min?}

### Queries

{docstring List.count}

{docstring List.countP}

{docstring List.idxOf}

{docstring List.idxOf?}

{docstring List.finIdxOf?}

{docstring List.find?}

{docstring List.findFinIdx?}

{docstring List.findIdx}

{docstring List.findIdx?}

{docstring List.findM?}

{docstring List.findSome?}

{docstring List.findSomeM?}

## Conversions

{docstring List.asString}

{docstring List.toArray}

{docstring List.toArrayImpl}

{docstring List.toByteArray}

{docstring List.toFloatArray}

{docstring List.toString}

## Modification

{docstring List.set}

{docstring List.setTR}

{docstring List.modify}

{docstring List.modifyTR}

{docstring List.modifyHead}

{docstring List.modifyTailIdx}

{docstring List.erase}

{docstring List.eraseTR}

{docstring List.eraseDups}

{docstring List.eraseIdx}

{docstring List.eraseIdxTR}

{docstring List.eraseP}

{docstring List.erasePTR}

{docstring List.eraseReps}

{docstring List.extract}

{docstring List.removeAll}

{docstring List.replace}

{docstring List.replaceTR}

{docstring List.reverse}

{docstring List.flatten}

{docstring List.flattenTR}

{docstring List.rotateLeft}

{docstring List.rotateRight}

{docstring List.leftpad}

{docstring List.leftpadTR}

{docstring List.rightpad}

### Insertion


{docstring List.insert}

{docstring List.insertIdx}

{docstring List.insertIdxTR}

{docstring List.intersperse}

{docstring List.intersperseTR}

{docstring List.intercalate}

{docstring List.intercalateTR}

## Sorting

{docstring List.mergeSort}

{docstring List.merge}

## Iteration

{docstring List.forA}

{docstring List.forM}

{docstring List.firstM}

{docstring List.sum}

### Folds

:::paragraph
Folds are operators that combine the elements of a list using a function.
They come in two varieties, named after the nesting of the function calls:

: {deftech}[Left folds]

  Left folds combine the elements from the head of the list towards the end.
  The head of the list is combined with the initial value, and the result of this operation is then combined with the next value, and so forth.

: {deftech}[Right folds]

  Right folds combine the elements from the end of the list towards the start, as if each {name List.cons}`cons` constructor were replaced by a call to the combining function and {name List.nil}`nil` were replaced by the initial value.

Monadic folds, indicated with an `-M` suffix, allow the combining function to use effects in a {tech}[monad], which may include stopping the fold early.
:::

{docstring List.foldl}

{docstring List.foldlM}

{docstring List.foldlRecOn}

{docstring List.foldr}

{docstring List.foldrM}

{docstring List.foldrRecOn}

{docstring List.foldrTR}


## Transformation

{docstring List.map}

{docstring List.mapTR}

{docstring List.mapM}

{docstring List.mapM'}

{docstring List.mapA}

{docstring List.mapFinIdx}

{docstring List.mapFinIdxM}

{docstring List.mapIdx}

{docstring List.mapIdxM}

{docstring List.mapMono}

{docstring List.mapMonoM}

{docstring List.flatMap}

{docstring List.flatMapTR}

{docstring List.flatMapM}

{docstring List.zip}

{docstring List.zipIdx}

{docstring List.zipIdxTR}

{docstring List.zipWith}

{docstring List.zipWithTR}

{docstring List.zipWithAll}

{docstring List.unzip}

{docstring List.unzipTR}


## Filtering

{docstring List.filter}

{docstring List.filterTR}

{docstring List.filterM}

{docstring List.filterRevM}

{docstring List.filterMap}

{docstring List.filterMapTR}

{docstring List.filterMapM}


## Partitioning

{docstring List.take}

{docstring List.takeTR}

{docstring List.takeWhile}

{docstring List.takeWhileTR}

{docstring List.drop}

{docstring List.dropWhile}

{docstring List.dropLast}

{docstring List.dropLastTR}

{docstring List.splitAt}

{docstring List.span}

{docstring List.splitBy}

{docstring List.partition}

{docstring List.partitionM}

{docstring List.partitionMap}

{docstring List.groupByKey}

## Element Predicates

{docstring List.contains}

{docstring List.elem}

{docstring List.all}

{docstring List.allM}

{docstring List.any}

{docstring List.anyM}

{docstring List.and}

{docstring List.or}

## Comparisons

{docstring List.beq}

{docstring List.isEqv}

{docstring List.isPerm}

{docstring List.isPrefixOf}

{docstring List.isPrefixOf?}

{docstring List.isSublist}

{docstring List.isSuffixOf}

{docstring List.isSuffixOf?}

{docstring List.le}

{docstring List.lt}

{docstring List.lex}

## Termination Helpers

{docstring List.attach}

{docstring List.attachWith}

{docstring List.unattach}

{docstring List.pmap}
