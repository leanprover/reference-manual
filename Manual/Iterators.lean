/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Std.Data.Iterators
import Std.Data.TreeMap

import Manual.Meta
import Manual.Interaction.FormatRepr

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Std.Iterators
open Std (TreeMap)

#doc (Manual) "Iterators" =>
%%%
tag := "iterators"
%%%

An {deftech}_iterator_ provides sequential access to each element of some source of data.
Typical iterators allow the elements in a collection, such as a list, array, or {name Std.TreeMap}`TreeMap` to be accessed one by one, but they can also provide access to data by carrying out some effect, such as reading files.
Iterators provide a common interface to all of these operations.
Code that is written to the iterator API can be agnostic as to the source of the data.

Because Lean is a pure functional language, consuming an iterator does not invalidate it, but instead copies it.
As usual, {tech (key := "reference count")}[reference counting] is used to optimize programs that use values only once into programs that destructively modify values.

To use iterators, import {module}`Std.Data.Iterators`.

:::TODO
A couple basic iterator examples
:::

:::keepEnv
```lean -show
structure Coll : Type u where
structure Elem : Type u where
def Coll.iter (c : Coll) := (#[].iter : Iter Elem)
```
Each built-in collection for which it makes sense to do so can be iterated over.
By convention, a collection type {name}`Coll` provides a function {name}`Coll.iter` that returns an iterator over the elements of a collection.
Examples include {name}`List.iter`, {name}`Array.iter`, and {name}`TreeMap.iter`.
Additionally, other built-in types such as ranges support iteration using the same convention.
:::

Iterators can be transformed using combinators such as {name}`Iter.map` or {name}`Iter.filter` that take one or more iterators and return a new iterator.
The resulting iterators do not actually iterate over the underlying collection until they themselves are consumed.

# Steps

Fundamentally, an iterator is a data structure that takes a step when requested, returning a {name}`Iter.Step`.
This step is a wrapper around {name}`IterStep`, with additional proofs that are used to track termination behavior.

{docstring IterStep}

{docstring Iter.Step}

{docstring IterM.Step}

An {name}`Iter.Step` or {name}`IterM.Step` can be analyzed using the three {ref "match_pattern-functions"}[match pattern functions] {name}`PlausibleIterStep.yield`, {name}`PlausibleIterStep.skip`, and {name}`PlausibleIterStep.done`.
These functions pair the information in the underlying {name}`IterStep` with the surrounding proof object.

{docstring PlausibleIterStep.yield}

{docstring PlausibleIterStep.skip}

{docstring PlausibleIterStep.done}



# Varieties of Iterators

Iterators may be either monadic or pure, and they may be finite, productive, or potentially infinite.
{deftech (key:="monadic iterator")}_Monadic_ iterators use side effects in some {tech}[monad] to emit each value, and must therefore be used in the monad, while {deftech (key:="pure iterator")}_pure_ iterators do not require side effects.
For example, iterating over all files in a directory requires the {name}`IO` monad.
Pure iterators have type {name}`Iter`, while monadic iterators are represented by {name}`IterM`.

{docstring Iter}

{docstring IterM}

:::paragraph
Not all iterators are guaranteed to return a finite number of results; it is perfectly sensible to iterate over all of the natural numbers.
Similarly, not all iterators are guaranteed to either return a single result or terminate; iterators may be defined using arbitrary programs.
Thus, Lean divides iterators into three termination classes:
* {deftech (key:="finite iterator")}_Finite_ iterators are guaranteed to finish iterating after a finite number of steps. These iterators have a {name}`Finite` instance.
* {deftech (key:="productive iterator")}_Productive_ iterators are guaranteed to yield a value or terminate in finite time, but they may yield infinitely many values. These iterators have a {name}`Productive` instance.
* All other iterators, whose termination behavior is unknown. These iterators have neither instance.

All finite iterators are also productive.
:::

{docstring Finite +allowMissing}

{docstring Productive +allowMissing}

Sometimes, a needed {name}`Finite` instance is not available because an iterator has not yet been proved finite.
In these cases, {name}`Iter.allowNontermination` can be used to bypass a finiteness requirement.

{docstring Iter.allowNontermination}

# Basic Iterators

In addition to the iterators provided by collection types, there are a number of basic iterators. {TODO}[write more here]

{docstring Iter.empty}

{docstring Iter.repeat}

# Consuming Iterators

:::paragraph
There are three primary ways to consume an iterator:

: Converting it to a sequential data structure

  The functions {name}`Iter.toList`, {name}`Iter.toArray`, and their monadic equivalents {name}`IterM.toList` and {name}`IterM.toArray`, construct a lists or arrays that contain the values from the iterator, in order.
  Only {tech}[finite iterators] can be converted to sequential data structures.

: {keywordOf Lean.Parser.Term.doFor}`for` loops

  A {keywordOf Lean.Parser.Term.doFor}`for` loop can consume an iterator, making each value available in its body.

: Stepping through iterators

  Iterators can provide their values one-by-one, with client code explicitly requesting each new value in turn.
  When stepped through, iterators perform only enough computation to yield the requested value.
:::


:::example "Converting Iterators to Lists"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std.Iterators
```
In {name}`countdown`, an iterator over a range is transformed into an iterator over strings using {name}`Iter.map`.
This call to {name}`Iter.map` does not result in any iteration over the range until {name}`Iter.toList` is called, at which point each element of the range is produced and transformed into a string.
```lean (name := toListEx)
def countdown : String :=
  let steps : Iter String := (0...10).iter.map (s!"{10 - ·}!\n")
  String.join steps.toList

#eval IO.println countdown
```
```leanOutput toListEx
10!
9!
8!
7!
6!
5!
4!
3!
2!
1!
```
:::

:::example "Converting Infinite Iterators to Lists"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std.Iterators
```
Attempting to construct a list of all the natural numbers from an iterator fails:
```lean (name := toListInf) +error -keep
def allNats : List Nat :=
  let steps : Iter Nat := (0...*).iter
  steps.toList
```
The resulting error message states that there is no {name}`Finite` instance:
```leanOutput toListInf
failed to synthesize
  Finite (Std.Rxi.Iterator Nat) Id

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
If the failure to synthesize the instance is due to a missing proof, or if an infinite loop is desirable for an application, then the fact that consuming the iterator may not terminate can be hidden using {name}`Iter.allowNontermination`:
```lean
def allNats : List Nat :=
  let steps : Iter Nat := (0...*).iter
  steps.allowNontermination.toList
```

:::

:::example "Consuming Iterators in Loops"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std.Iterators
```
This program creates an iterator of strings from a range, and then consumes the strings in a {keywordOf Lean.Parser.Term.doFor}`for` loop:
```lean (name := iterFor)
def countdown (n : Nat) : IO Unit := do
  let steps : Iter String := (0...n).iter.map (s!"{n - ·}!")
  for i in steps do
    IO.println i
  IO.println "Blastoff!"

#eval countdown 5
```
```leanOutput iterFor
5!
4!
3!
2!
1!
Blastoff!
```
:::

:::example "Consuming Iterators Directly"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std.Iterators
```
The function {name}`countdown` calls the range iterator's {name Iter.step}`step` function directly, handling each of the three possible cases.
```lean
def countdown (n : Nat) : IO Unit := do
  let steps : Iter Nat := (0...n).iter
  go steps
where
  go iter := do
    match iter.step with
    | .done _ => pure ()
    | .skip iter' _ => go iter'
    | .yield iter' i _ => do
      IO.println s!"{i}!"
      if i == 2 then
        IO.println s!"Almost there..."
      go iter'
  termination_by iter.finitelyManySteps
```
:::

## Stepping Iterators

{docstring Std.Iterators.Iter.step}

### Termination

{docstring Iter.finitelyManySteps}

{docstring Iter.finitelyManySkips}

{docstring Iter.attachWith}

## Plausibility



## Consuming Iterators

### Consuming Pure Iterators

{docstring Iter.fold}

{docstring Iter.foldM}

{docstring Iter.count}

{docstring Iter.any}

{docstring Iter.anyM}

{docstring Iter.all}

{docstring Iter.allM}

{docstring Iter.find? +allowMissing}

{docstring Iter.findM? +allowMissing}

{docstring Iter.findSome? +allowMissing}

{docstring Iter.findSomeM? +allowMissing}

{docstring Iter.atIdx?}

{docstring Iter.atIdxSlow?}

### Consuming Monadic Iterators

{docstring IterM.fold}

{docstring IterM.foldM}

{docstring IterM.count}

{docstring IterM.any}

{docstring IterM.anyM}

{docstring IterM.all}

{docstring IterM.allM}

{docstring IterM.find? +allowMissing}

{docstring IterM.findM? +allowMissing}

{docstring IterM.findSome? +allowMissing}

{docstring IterM.findSomeM? +allowMissing}

{docstring IterM.atIdx?}

### Tabulating (TODO terminology)

{docstring Iter.toArray}

{docstring Iter.toList}

{docstring Iter.toListRev}

# Iterator Combinators

## Pure Combinators

{docstring Std.Iterators.Iter.toIterM}

{docstring Std.Iterators.Iter.take}

{docstring Std.Iterators.Iter.takeWhile}

{docstring Std.Iterators.Iter.toTake}

{docstring Std.Iterators.Iter.drop}

{docstring Std.Iterators.Iter.dropWhile}

{docstring Std.Iterators.Iter.stepSize}

{docstring Std.Iterators.Iter.map}

{docstring Std.Iterators.Iter.mapM}

{docstring Std.Iterators.Iter.mapWithPostcondition}

{docstring Std.Iterators.Iter.uLift}

{docstring Std.Iterators.Iter.flatMap}

{docstring Std.Iterators.Iter.flatMapM}

{docstring Std.Iterators.Iter.flatMapAfter}

{docstring Std.Iterators.Iter.flatMapAfterM}

{docstring Std.Iterators.Iter.filter}

{docstring Std.Iterators.Iter.filterM}

{docstring Std.Iterators.Iter.filterWithPostcondition}

{docstring Std.Iterators.Iter.filterMap}

{docstring Std.Iterators.Iter.filterMapM}

{docstring Std.Iterators.Iter.filterMapWithPostcondition}

{docstring Std.Iterators.Iter.zip}

## Monadic Combinators

{docstring Std.Iterators.IterM.take}

{docstring Std.Iterators.IterM.takeWhile}

{docstring Std.Iterators.IterM.toTake}

{docstring Std.Iterators.IterM.drop}

{docstring Std.Iterators.IterM.dropWhile}

{docstring Std.Iterators.IterM.stepSize}

{docstring Std.Iterators.IterM.map}

{docstring Std.Iterators.IterM.mapM}

{docstring Std.Iterators.IterM.mapWithPostcondition}

{docstring Std.Iterators.IterM.uLift}

{docstring Std.Iterators.IterM.flatMap}

{docstring Std.Iterators.IterM.flatMapM}

{docstring Std.Iterators.IterM.flatMapAfter}

{docstring Std.Iterators.IterM.flatMapAfterM}

{docstring Std.Iterators.IterM.filter}

{docstring Std.Iterators.IterM.filterM}

{docstring Std.Iterators.IterM.filterWithPostcondition}

{docstring Std.Iterators.IterM.filterMap}

{docstring Std.Iterators.IterM.filterMapM}

{docstring Std.Iterators.IterM.filterMapWithPostcondition}

{docstring Std.Iterators.IterM.zip}



Map etc

# Reasoning About Iterators

{docstring Iter.inductSkips}

{docstring Iter.inductSteps}

{docstring Std.Iterators.PostconditionT}

# Implementing Iterators
