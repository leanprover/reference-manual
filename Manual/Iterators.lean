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

:::example "Mixing Collections"
Combining a list and an array using {name}`List.zip` or {name}`Array.zip` would ordinarily require converting one of them into the other collection.
Using iterators, they can be processed without conversion:
```lean (name := zip)
def colors : Array String := #["purple", "gray", "blue"]
def codes : List String := ["aa27d1", "a0a0a0", "0000c5"]

#eval colors.iter.zip codes.iter |>.toArray
```
```leanOutput zip
#[("purple", "aa27d1"), ("gray", "a0a0a0"), ("blue", "0000c5")]
```
:::

::::example "Avoiding Intermediate Structures"
:::paragraph
In this example, an array of colors and a list of color codes are combined.
The program separates three intermediate stages:
1. The names and codes are combined into pairs.
2. The pairs are transformed into readable strings.
3. The strings are combined with newlines.
```lean (name := intermediate)
def colors : Array String := #["purple", "gray", "blue"]

def codes : List String := ["aa27d1", "a0a0a0", "0000c5"]

def go : IO Unit := do
  let colorCodes := colors.iter.zip codes.iter
  let colorCodes := colorCodes.map fun (name, code) =>
    s!"{name} ↦ #{code}"
  let colorCodes := colorCodes.fold (init := "") fun x y =>
    if x.isEmpty then y else x ++ "\n" ++ y
  IO.println colorCodes

#eval go
```
```leanOutput intermediate
purple ↦ #aa27d1
gray ↦ #a0a0a0
blue ↦ #0000c5
```
:::

The intermediate stages of the computation do not allocate new data structures.
Instead, all the steps of the transformation are fused into a single loop, with {name}`Iter.fold` carrying out one step at a time.
In each step, a single color and color code are combined into a pair, rewritten to a string, and added to the result string.
::::

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


# Iterator Definitions

Iterators may be either monadic or pure, and they may be finite, productive, or potentially infinite.
{deftech (key:="monadic iterator")}_Monadic_ iterators use side effects in some {tech}[monad] to emit each value, and must therefore be used in the monad, while {deftech (key:="pure iterator")}_pure_ iterators do not require side effects.
For example, iterating over all files in a directory requires the {name}`IO` monad.
Pure iterators have type {name}`Iter`, while monadic iterators are represented by {name}`IterM`.

{docstring Iter}

{docstring IterM}

The types {name}`Iter` and {name}`IterM` are merely wrappers around an internal state.
The actual process of iteration consists of producing a sequence of iteration steps when requested.
Each step returns an updated iterator with a new internal state along with either a data value, an indicator that the caller should request a data value again, or an indication that iteration is finished.
Steps taken by {name}`Iter` and {name}`IterM` are respectively represented by the types {name}`Iter.Step` and {name}`IterM.Step`.
Both types of step are wrappers around {name}`IterStep` that include additional proofs that are used to track termination behavior.

{docstring IterStep}

{docstring Iter.Step}

{docstring IterM.Step}

Steps are produced from iterators using {name}`Iterator.step`, which is a method of the {name}`Iterator` type class.
{name}`Iterator` is used for both pure and monadic iterators; pure iterators can be completely polymorphic in the choice of monad, which allows callers to instantiate it with {name}`Id`.

{docstring Iterator +allowMissing}

In addition to the step function, instances of {name}`Iterator` include a relation {name}`Iterator.IsPlausibleStep`.
This relation exists because most iterators both maintain invariants over their internal state and yield values in a predictable manner.
For example, array iterators track both an array and a current index into it.
Stepping an array iterator results in an iterator over the same underlying array; it yields a value when the index is small enough, or is done otherwise.
The {deftech}_plausible steps_ from an iterator state are those which are related to it via the iterator's implementation of {name Iterator.IsPlausibleStep}`IsPlausibleStep`.
Tracking plausibility at the logical level makes it feasible to reason about termination behavior in many more cases.

Both {name}`Iter.Step` and {name}`IterM.Step` are defined in terms of {name}`PlausibleIterStep`; thus, both types can be used with {tech}[leading dot notation] for its namespace.
An {name}`Iter.Step` or {name}`IterM.Step` can be analyzed using the three {ref "match_pattern-functions"}[match pattern functions] {name}`PlausibleIterStep.yield`, {name}`PlausibleIterStep.skip`, and {name}`PlausibleIterStep.done`.
These functions pair the information in the underlying {name}`IterStep` with the surrounding proof object.

{docstring PlausibleIterStep}

{docstring PlausibleIterStep.yield}

{docstring PlausibleIterStep.skip}

{docstring PlausibleIterStep.done}

:::paragraph
Not all iterators are guaranteed to return a finite number of results; it is perfectly sensible to iterate over all of the natural numbers.
Similarly, not all iterators are guaranteed to either return a single result or terminate; iterators may be defined using arbitrary programs.
Thus, Lean divides iterators into three termination classes:
* {deftech (key:="finite iterator")}_Finite_ iterators are guaranteed to finish iterating after a finite number of steps. These iterators have a {name}`Finite` instance.
* {deftech (key:="productive iterator")}_Productive_ iterators are guaranteed to yield a value or terminate in finite time, but they may yield infinitely many values. These iterators have a {name}`Productive` instance.
* All other iterators, whose termination behavior is unknown. These iterators have neither instance.

All finite iterators are necessarily productive.
:::

{docstring Finite +allowMissing}

{docstring Productive +allowMissing}

Sometimes, a needed {name}`Finite` instance is not available because an iterator has not yet been proved finite.
In these cases, {name}`Iter.allowNontermination` can be used to bypass a finiteness requirement.

{docstring Iter.allowNontermination}

::::example "Iterating Over `Nat`"
:::paragraph
To write an iterator that yields each natural number in turn, the first step is to implement its internal state.
This iterator only needs to remember the next natural number:
```lean
structure Nats where
  next : Nat
```
:::
:::paragraph
This iterator will only ever yield the next natural number.
Thus, its step function will never return {name IterStep.skip}`skip` or {name IterStep.done}`done`.
Whenever it yields a value, the value will be the internal state's {name Nats.next}`next` field, and the successor iterator's {name Nats.next}`next` field will be one greater.
The {tactic}`grind` tactic suffices to show that the step is indeed plausible:
```lean
instance [Pure m] : Iterator Nats m Nat where
  IsPlausibleStep it
    | .yield it' n =>
      n = it.internalState.next ∧
      it'.internalState.next = n + 1
    | _ => False
  step it :=
    let n := it.internalState.next
    pure <| .deflate <|
      .yield { it with internalState.next := n + 1 } n (by grind)
```
:::

:::paragraph
```lean -show
section
variable [Pure m] [inst : Iterator Nats m Nat] (it it' : IterM (α := Nats) m Nat)
```
This {name Iterator.step}`step` function is productive because it never returns {name IterStep.skip}`skip`.
Thus, the proof that each chain of {name IterStep.skip}`skip`s has finite length can rely on the fact that when {lean}`it` is a {name}`Nats` iterator, {lean}`Iterator.IsPlausibleStep it (.skip it') = False`:
```lean -show
end
```
```lean
instance [Pure m] : Productive Nats m where
  wf := .intro <| fun _ => .intro _ nofun
```
Because there are infinitely many {name}`Nat`s, the iterator is not finite.
:::


:::paragraph
A {name}`Nats` iterator can be created using this function:
```lean
def Nats.iter : Iter (α := Nats) Nat :=
  toIterM { next := 0 } Id Nat |>.toIter
```
:::

:::paragraph
This iterator is useful with combinators such as {name}`Iter.zip`:
```lean (name := natzip)
#eval show IO Unit from do
  let xs : List String := ["cat", "dog", "pachycephalosaurus"]
  for (x, y) in Nats.iter.zip xs.iter do
    IO.println s!"{x}: {y}"
```
```leanOutput natzip
0: cat
1: dog
2: pachycephalosaurus
```
:::
::::

::::example "Iterating Over Triples"
The type {name}`Triple` contains three values of the same type:
```lean
structure Triple α where
  fst : α
  snd : α
  thd : α
```

The internal state of an iterator over {name}`Triple` can consist of a triple paired with a current position.
This position may either be one of the fields or an indication that iteration is finished.
```lean
inductive TriplePos where
  | fst | snd | thd | done
```

Positions can be used to look up elements:

```lean
def Triple.get? (xs : Triple α) (pos : TriplePos) : Option α :=
  match pos with
  | .fst => some xs.fst
  | .snd => some xs.snd
  | .thd => some xs.thd
  | _ => none
```

Each field's position has a successor position:
```lean
def TriplePos.next? : TriplePos → Option TriplePos
  | .fst => some .snd
  | .snd => some .thd
  | .thd => some .done
  | .done => none

@[grind, grind cases]
inductive TriplePos.Succ : TriplePos → TriplePos → Prop where
  | fst : Succ .fst .snd
  | snd : Succ .snd .thd
  | thd : Succ .thd .done

theorem TriplePos.next?_Succ {pos pos' : TriplePos} :
    (pos.next? = some pos') = pos.Succ pos' := by
  cases pos <;> grind [next?]
```

The iterator itself pairs a triple with the position of the next element:
```lean
structure TripleIterator α where
  triple : Triple α
  pos : TriplePos
```

Iteration begins at {name TriplePos.fst}`fst`:
```lean
def Triple.iter (xs : Triple α) : Iter (α := TripleIterator α) α :=
  toIterM {triple := xs, pos := .fst : TripleIterator α} Id α |>.toIter
```

There are two plausible steps: either the iterator's position has a successor, in which case the next iterator is one that points at the same triple with the successor position, or it does not, in which case iteration is complete.
```lean
@[grind]
inductive TripleIterator.IsPlausibleStep :
    @IterM (TripleIterator α) m α →
    IterStep (@IterM (TripleIterator α) m α) α →
    Prop where
  | yield :
    it.internalState.triple = it'.internalState.triple →
    it.internalState.pos.Succ it'.internalState.pos →
    it.internalState.triple.get? it.internalState.pos = some out →
    IsPlausibleStep it (.yield it' out)
  | done :
    it.internalState.pos = .done →
    IsPlausibleStep it .done
```

The corresponding step function yields the iterator and value describe by the relation:
```lean
instance [Pure m] : Iterator (TripleIterator α) m α where
  IsPlausibleStep := TripleIterator.IsPlausibleStep
  step
    | ⟨xs, pos⟩ =>
      pure <| .deflate <|
      match pos with
      | .fst => .yield ⟨xs, .snd⟩ xs.fst ?_
      | .snd => .yield ⟨xs, .thd⟩ xs.snd ?_
      | .thd => .yield ⟨xs, .done⟩ xs.thd ?_
      | .done => .done <| ?_
where finally
  all_goals grind [Triple.get?]
```

This iterator cannot yet be converted to an array, because it is missing a {name}`Finite` instance and an {name}`IteratorCollect` instance:
```lean
def abc : Triple Char := ⟨'a', 'b', 'c'⟩
```
```lean (name := noAbc) +error
#eval abc.iter.toArray
```
```leanOutput noAbc
failed to synthesize
  Finite (TripleIterator Char) Id

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

To prove finiteness, it's easiest to start at {name}`TriplePos.done` and work backwards toward {name}`TriplePos.fst`, showing that each position in turn has a finite chain of successors:

```lean
@[grind! .]
theorem acc_done [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .done : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | _, ⟨_, ⟨_, h⟩⟩ => by
      cases h <;> grind [IterStep.successor_done]

@[grind! .]
theorem acc_thd [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .thd : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

@[grind! .]
theorem acc_snd [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .snd : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

@[grind! .]
theorem acc_fst [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .fst : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

instance [Pure m] : Finite (TripleIterator α) m where
  wf := .intro <| fun
    | { internalState := { triple, pos } } => by
      cases pos <;> grind
```

With the {name}`Finite` instance in place, the default implementation of {name}`IteratorCollect` can be used:

```lean
instance [Iterator (TripleIterator α) m α] [Monad n] :
    IteratorCollect (TripleIterator α) m n :=
  IteratorCollect.defaultImplementation
```

{name}`Iter.toArray` now works:
```lean (name := abcToArray)
#eval abc.iter.toArray
```
```leanOutput abcToArray
#['a', 'b', 'c']
```

To enable the iterator in {keywordOf Lean.Parser.Term.doFor}`for` loops, instances of {name}`IteratorLoopPartial` and {name}`IteratorLoop` are needed:
```lean
instance [Monad m] [Monad n] :
    IteratorLoopPartial (TripleIterator α) m n :=
  .defaultImplementation

instance [Monad m] [Monad n] :
    IteratorLoop (TripleIterator α) m n :=
  .defaultImplementation
```
```lean (name := abc)
#eval show IO Unit from do
  for x in abc.iter do
    IO.println x
```
```leanOutput abc
a
b
c
```
::::

::::example "Iterators and Effects"
One way to iterate over the contents of a file is to read a specified number of bytes from a {name IO.FS.Stream}`Stream` at each step.
When EOF is reached, the iterator can close the file by letting its reference count drop to zero:
```lean
structure FileIterator where
  stream? : Option IO.FS.Stream
  count : USize := 8192
```

An iterator can be created by opening a file and converting its handle to a stream:
```lean
def iterFile
    (path : System.FilePath)
    (count : USize := 8192) :
    IO (IterM (α := FileIterator) IO ByteArray) := do
  let h ← IO.FS.Handle.mk path .read
  let stream? := some (IO.FS.Stream.ofHandle h)
  return toIterM { stream?, count } IO ByteArray
```

For this iterator, a {name IterStep.yield}`yield` is plausible when the file is still open, and {name IterStep.done}`done` is plausible when the file is closed.
The actual step function performs a read and closes the file if no bytes were returned:
```lean
instance : Iterator FileIterator IO ByteArray where
  IsPlausibleStep it
    | .yield .. =>
      it.internalState.stream?.isSome
    | .skip .. => False
    | .done => it.internalState.stream?.isNone
  step it := do
    let { stream?, count } := it.internalState
    match stream? with
    | none => return .deflate <| .done rfl
    | some stream =>
      let bytes ← stream.read count
      let it' :=
        { it with internalState.stream? :=
          if bytes.size == 0 then none else some stream
        }
      return .deflate <| .yield it' bytes (by grind)
```

To use it in loops, {name}`IteratorLoop` and {name}`IteratorLoopPartial` instances will be necessary.
In practice, the latter is most important: because file streams may be infinite, the iterator itself may be infinite.
```lean
instance [Monad n] : IteratorLoop FileIterator IO n :=
  .defaultImplementation

instance [Monad n] : IteratorLoopPartial FileIterator IO n :=
  .defaultImplementation
```

This is enough support code to use the iterator to calculate file sizes:
```lean
def fileSize (name : System.FilePath) : IO Nat := do
  let mut size := 0
  let f := (← iterFile name).allowNontermination
  for bytes in f do
    size := size + bytes.size
  return size
```

::::

## Universe Levels

To make the {tech}[universe levels] of iterators more flexible, a wrapper type {name Std.Shrink}`Shrink` is applied around the result of {name}`Iterator.step`.
This type is presently a placeholder.
It is present to reduce the scope of the breaking change when the full implementation is available.

{docstring Std.Shrink}

{docstring Std.Shrink.inflate}

{docstring Std.Shrink.deflate}


## Basic Iterators

In addition to the iterators provided by collection types, there are two basic iterators that are not connected to any underlying data structure.
{name}`Iter.empty` finishes iteration immediately after yielding no data, and {name}`Iter.repeat` yields the same element forever.
These iterators are primarily useful as parts of larger iterators built with combinators.

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

### Collecting Contents

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
