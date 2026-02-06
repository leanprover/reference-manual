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

open Std.Iterators Types
open Std (TreeMap Iter IterM IterStep Iterator PlausibleIterStep IteratorLoop IteratorAccess LawfulIteratorLoop)

#doc (Manual) "Iterators" =>
%%%
tag := "iterators"
%%%

An {deftech}_iterator_ provides sequential access to each element of some source of data.
Typical iterators allow the elements in a collection, such as a list, array, or {name Std.TreeMap}`TreeMap` to be accessed one by one, but they can also provide access to data by carrying out some {tech (key := "monad")}[monadic] effect, such as reading files.
Iterators provide a common interface to all of these operations.
Code that is written to the iterator API can be agnostic as to the source of the data.

Each iterator maintains an internal state that enables it to determine the next value.
Because Lean is a pure functional language, consuming an iterator does not invalidate it, but instead copies it with an updated state.
As usual, {tech (key := "reference count")}[reference counting] is used to optimize programs that use values only once into programs that destructively modify values.

To use iterators, import {module}`Std.Data.Iterators`.

:::example "Mixing Collections"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
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
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
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

The Lean standard library provides three kinds of iterator operations.
{deftech}_Producers_ create a new iterator from some source of data.
They determine which data is to be returned by an iterator, and how this data is to be computed, but they are not in control of _when_ the computations occur.
{deftech}_Consumers_ use the data in an iterator for some purpose.
Consumers request the iterator's data, and the iterator computes only enough data to satisfy a consumer's requests.
{deftech (key := "iterator combinator")}_Combinators_ are both consumers and producers: they create new iterators from existing iterators.
Examples include {name}`Iter.map` and {name}`Iter.filter`.
The resulting iterators produce data by consuming their underlying iterators, and do not actually iterate over the underlying collection until they themselves are consumed.


:::keepEnv
```lean -show
/-- A collection type. -/
structure Coll : Type u where
/-- The elements of the collection `Coll`. -/
structure Elem : Type u where
/-- Returns an iterator for `c`. -/
def Coll.iter (c : Coll) := (#[].iter : Iter Elem)
```
Each built-in collection for which it makes sense to do so can be iterated over.
In other words, the collection libraries include iterator {tech}[producers].
By convention, a collection type {name}`Coll` provides a function {name}`Coll.iter` that returns an iterator over the elements of a collection.
Examples include {name}`List.iter`, {name}`Array.iter`, and {name}`TreeMap.iter`.
Additionally, other built-in types such as ranges support iteration using the same convention.
:::

# Run-Time Considerations

For many use cases, using iterators can give a performance benefit by avoiding allocating intermediate data structures.
Without iterators, zipping a list with an array requires first converting one of them to the other type, allocating an intermediate structure, and then using the appropriate {name List.zip}`zip` function.
Using iterators, the intermediate structure can be avoided.

When an iterator is consumed, the resulting computation should be thought of as a single loop, even if the iterator itself is built using combinators from a number of underlying iterators.
One step of the loop may carry out multiple steps from the underlying iterators.
In many cases, the Lean compiler can optimize iterator computations, removing the intermediate overhead, but this is not guaranteed.
When profiling shows that significant time is taken by a tight loop that involves multiple sources of data, it can be necessary to inspect the compiler's IR to see whether the iterators' operations were fused.
In particular, if the IR contains many pattern matches over steps, then it can be a sign of a failure to inline or specialize.
If this is the case, it may be necessary to write a tail-recursive function by hand rather than using the higher-level API.

# Iterator Definitions

Iterators may be either monadic or pure, and they may be finite, productive, or potentially infinite.
{deftech (key:="monadic iterator")}_Monadic_ iterators use side effects in some {tech}[monad] to emit each value, and must therefore be used in the monad, while {deftech (key:="pure iterator")}_pure_ iterators do not require side effects.
For example, iterating over all files in a directory requires the {name}`IO` monad.
Pure iterators have type {name}`Iter`, while monadic iterators are represented by {name}`IterM`.

{docstring Iter}

{docstring IterM}

The types {name}`Iter` and {name}`IterM` are merely wrappers around an internal state.
This inner state type is the implicit parameter to the iterator types.
For basic producer iterators, like the one that results from {name}`List.iter`, this type is fairly simple; however, iterators that result from {tech (key := "iterator combinator")}[combinators] use polymorphic state types that can grow large.
Because Lean elaborates the specified return type of a function before elaborating its body, it may not be possible to automatically determine the internal state type of an iterator type returned by a function.
In these cases, it can be helpful to omit the return type from the signature and instead place a type annotation on the definition's body, which allows the specific iterator combinators invoked from the body to be used to determine the state type.

:::example "Iterator State Types"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators.Types (ListIterator ArrayIterator Map)
```

Writing the internal state type explicitly for list and array iterators is feasible:
```lean
def reds := ["red", "crimson"]

example : @Iter (ListIterator String) String := reds.iter

example : @Iter (ArrayIterator String) String := reds.toArray.iter
```
However, the internal state type of a use of the {name}`Iter.map` combinator is quite complicated:
```lean
example :
    @Iter
      (Map (ListIterator String) Id Id @id fun x : String =>
        pure x.length)
      Nat :=
  reds.iter.map String.length
```
Omitting the state type leads to an error:
```lean +error (name := noStateType)
example : Iter Nat := reds.iter.map String.length
```
```leanOutput noStateType
don't know how to synthesize implicit argument `α`
  @Iter ?m.1 Nat
context:
⊢ Type

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
```
Rather than writing the state type by hand, it can be convenient to omit the return type and instead provide the annotation around the term:
```lean
example := (reds.iter.map String.length : Iter Nat)

example :=
  show Iter Nat from
  reds.iter.map String.length
```
:::

The actual process of iteration consists of producing a sequence of iteration steps when requested.
Each step returns an updated iterator with a new internal state along with either a data value (in {name}`IterStep.yield`), an indicator that the caller should request a data value again ({name}`IterStep.skip`), or an indication that iteration is finished ({name}`IterStep.done`).
Without the ability to {name IterStep.skip}`skip`, it would be much more difficult to work with iterator combinators such as {name}`Iter.filter` that do not yield values for all of those yielded by the underlying iterator.
With {name IterStep.skip}`skip`, the implementation of {name Iter.filter}`filter` doesn't need to worry about whether the underlying iterator is {tech (key:="finite iterator")}[finite] in order to be a well-defined function, and reasoning about its finiteness can be carried out in separate proofs.
Additionally, {name Iter.filter}`filter` would require an inner loop, which is much more difficult for the compiler to inline.

{docstring IterStep}

Steps taken by {name}`Iter` and {name}`IterM` are respectively represented by the types {name}`Iter.Step` and {name}`IterM.Step`.
Both types of step are wrappers around {name}`IterStep` that include {ref "iterator-plausibility"}[additional proofs] that are used to track termination behavior.

{docstring Iter.Step}

{docstring IterM.Step}

Steps are produced from iterators using {name}`Iterator.step`, which is a method of the {name}`Iterator` type class.
{name}`Iterator` is used for both pure and monadic iterators; pure iterators can be completely polymorphic in the choice of monad, which allows callers to instantiate it with {name}`Id`.

{docstring Iterator +allowMissing}

## Plausibility
%%%
tag := "iterator-plausibility"
%%%

In addition to the step function, instances of {name}`Iterator` include a relation {name}`Iterator.IsPlausibleStep`.
This relation exists because most iterators both maintain invariants over their internal state and yield values in a predictable manner.
For example, array iterators track both an array and a current index into it.
Stepping an array iterator results in an iterator over the same underlying array; it yields a value when the index is small enough, or is done otherwise.
The {deftech}_plausible steps_ from an iterator state are those which are related to it via the iterator's implementation of {name Iterator.IsPlausibleStep}`IsPlausibleStep`.
Tracking plausibility at the logical level makes it feasible to reason about termination behavior for monadic iterators.

Both {name}`Iter.Step` and {name}`IterM.Step` are defined in terms of {name}`PlausibleIterStep`; thus, both types can be used with {tech}[leading dot notation] for its namespace.
An {name}`Iter.Step` or {name}`IterM.Step` can be analyzed using the three {ref "match_pattern-functions"}[match pattern functions] {name}`PlausibleIterStep.yield`, {name}`PlausibleIterStep.skip`, and {name}`PlausibleIterStep.done`.
These functions pair the information in the underlying {name}`IterStep` with the surrounding proof object.

{docstring PlausibleIterStep}

{docstring PlausibleIterStep.yield}

{docstring PlausibleIterStep.skip}

{docstring PlausibleIterStep.done}

## Finite and Productive Iterators

:::paragraph
Not all iterators are guaranteed to return a finite number of results; it is perfectly sensible to iterate over all of the natural numbers.
Similarly, not all iterators are guaranteed to either return a single result or terminate; iterators may be defined using arbitrary programs.
Thus, Lean divides iterators into three termination classes:
* {deftech (key:="finite iterator")}_Finite_ iterators are guaranteed to finish iterating after a finite number of steps. These iterators have a {name}`Finite` instance.
* {deftech (key:="productive iterator")}_Productive_ iterators are guaranteed to yield a value or terminate in finitely many steps, but they may yield infinitely many values. These iterators have a {name}`Productive` instance.
* All other iterators, whose termination behavior is unknown. These iterators have neither instance.

All finite iterators are necessarily productive.
:::

{docstring Finite}

{docstring Productive}

Lean's standard library provides many functions that iterate over an iterator. These consumer functions usually do not
make any assumptions about the underlying iterator. In particular, such functions may run forever for certain iterators.

Sometimes, it is of utmost importance that a function does terminate.
For these cases, the combinator {name}`Iter.ensureTermination` results in an iterator that provides variants of consumers that are guaranteed to terminate.
They usually require proof that the involved iterator is finite.

{docstring Iter.ensureTermination}

{docstring IterM.ensureTermination}

::::example "Iterating Over `Nat`"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Productive)
```
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

Whenever an iterator is defined, an {name}`IteratorLoop` instance should be provided.
They are required for most consumers of iterators such as {name}`Iter.toList` or the `for` loops.
One can use their default implementations as follows:

```lean
instance [Pure m] [Monad n] : IteratorLoop Nats m n :=
  .defaultImplementation
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
  ⟨{ next := 0 }⟩
```
:::

:::paragraph
One can print all natural numbers by running the following function:
```lean
def f : IO Unit := do
  for x in Nats.iter do
    IO.println s!"{x}"
```
This function never terminates, printing all natural numbers in increasing order, one
after another.
:::

:::paragraph
This iterator is most useful with combinators such as {name}`Iter.zip`:
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

:::paragraph
In contrast to the previous example, this loop terminates because `xs.iter` is a finite iterator,
One can make sure that a loop actually terminates by providing a {name}`Finite` instance:
```lean (name := natfin)
#check type_of% (Nats.iter.zip ["cat", "dog"].iter).internalState

#synth Finite (Zip Nats Id (ListIterator String) String) Id
```
```leanOutput natfin
Zip Nats Id (ListIterator String) String : Type
```
```leanOutput natfin
Zip.instFinite₂
```
In contrast, `Nats.iter` has no `Finite` instance because it yields infinitely many values:
```lean (name := natinf) +error
#synth Finite Nats Id
```
```leanOutput natinf
failed to synthesize
  Finite Nats Id

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

Because there are infinitely many {name}`Nat`s, using {name}`Iter.ensureTermination` results in an error:
```lean (name := natterm) +error
#eval show IO Unit from do
  for x in Nats.iter.ensureTermination do
    IO.println s!"{x}"
```
```leanOutput natterm
failed to synthesize instance for 'for_in%' notation
  ForIn (EIO IO.Error) (Iter.Total Nat) ?m.12
```
:::
::::

::::example "Iterating Over Triples"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Finite)
```
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
@[grind, grind cases]
inductive TriplePos.Succ : TriplePos → TriplePos → Prop where
  | fst : Succ .fst .snd
  | snd : Succ .snd .thd
  | thd : Succ .thd .done
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
  ⟨{triple := xs, pos := .fst : TripleIterator α}⟩
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

This iterator can now be converted to an array:
```lean
def abc : Triple Char := ⟨'a', 'b', 'c'⟩
```
```lean (name := abcToArray)
#eval abc.iter.toArray
```
```leanOutput abcToArray
#['a', 'b', 'c']
```

In general, `Iter.toArray` might run forever. One can prove that `abc` is finite, and the above example will terminate after finitely many steps, by
constructing a `Finite (Triple Char) Id` instance.
It's easiest to start at {name}`TriplePos.done` and work backwards toward {name}`TriplePos.fst`, showing that each position in turn has a finite chain of successors:

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

To enable the iterator in {keywordOf Lean.Parser.Term.doFor}`for` loops, an instance of {name}`IteratorLoop` are needed:
```lean
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
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
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
  return ⟨{ stream?, count }⟩
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

To use it in loops, an {name}`IteratorLoop` instance will be necessary.
```lean
instance [Monad n] : IteratorLoop FileIterator IO n :=
  .defaultImplementation
```

This is enough support code to use the iterator to calculate file sizes:
```lean
def fileSize (name : System.FilePath) : IO Nat := do
  let mut size := 0
  let f := (← iterFile name)
  for bytes in f do
    size := size + bytes.size
  return size
```

::::

## Accessing Elements

Some iterators support efficient random access.
For example, an array iterator can skip any number of elements in constant time by incrementing the index that it maintains into the array.

{docstring IteratorAccess +allowMissing}

{docstring IterM.nextAtIdx?}

## Loops

{docstring IteratorLoop +allowMissing}

{docstring IteratorLoop.defaultImplementation}

{docstring LawfulIteratorLoop +allowMissing}

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

{docstring IterM.empty}

{docstring Iter.repeat}


# Consuming Iterators

:::paragraph
There are three primary ways to consume an iterator:

: Converting it to a sequential data structure

  The functions {name}`Iter.toList`, {name}`Iter.toArray`, and their monadic equivalents {name}`IterM.toList` and {name}`IterM.toArray`, construct a lists or arrays that contain the values from the iterator, in order.
  Only {tech}[finite iterators] can be converted to sequential data structures.

: {keywordOf Lean.Parser.Term.doFor}`for` loops

  A {keywordOf Lean.Parser.Term.doFor}`for` loop can consume an iterator, making each value available in its body.
  This requires that the iterator have an instance of {name}`IteratorLoop` for the loop's monad.

: Stepping through iterators

  Iterators can provide their values one-by-one, with client code explicitly requesting each new value in turn.
  When stepped through, iterators perform only enough computation to yield the requested value.
:::


:::example "Converting Iterators to Lists"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
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
open Std
```
Attempting to construct a list of all the natural numbers from an iterator will produce an endless loop:
```lean (name := toListInf) -keep
def allNats : List Nat :=
  let steps : Iter Nat := (0...*).iter
  steps.toList
```
The combinator {lean}`Iter.ensureTermination` results in an iterator where non-termination is ruled out.
These iterators are guaranteed to terminate after finitely many steps, and thus cannot be used when Lean cannot prove the iterator finite.
```lean (name := toListInf) +error -keep
def allNats : List Nat :=
  let steps := (0...*).iter.ensureTermination
  steps.toList
```
The resulting error message states that there is no {name}`Finite` instance:
```leanOutput toListInf
failed to synthesize instance of type class
  Finite (Rxi.Iterator Nat) Id

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

:::example "Consuming Iterators in Loops"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
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
open Std
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

Iterators are manually stepped using {name}`Iter.step` or {name}`IterM.step`.

{docstring Iter.step}

{docstring IterM.step}

### Termination

When manually stepping an finite iterator, the termination measures {name Iter.finitelyManySteps}`finitelyManySteps` and {name Iter.finitelyManySkips}`finitelyManySkips` can be used to express that each step brings iteration closer to the end.
The proof automation for {ref "well-founded-recursion"}[well-founded recursion] is pre-configured to prove that recursive calls after steps reduce these measures.

:::example "Finitely Many Skips"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Productive)
```
This function returns the first element of an iterator, if there is one, or {name}`none` otherwise.
Because the iterator must be productive, it is guaranteed to return an element after at most a finite number of {name PlausibleIterStep.skip}`skip`s.
This function terminates even for infinite iterators.
```lean
def getFirst {α β} [Iterator α Id β] [Productive α Id]
    (it : @Iter α β) : Option β :=
  match it.step with
  | .done .. => none
  | .skip it' .. => getFirst it'
  | .yield _ x .. => pure x
termination_by it.finitelyManySkips
```
:::

{docstring Iter.finitelyManySteps}

{docstring IterM.finitelyManySteps}

{docstring IterM.TerminationMeasures.Finite +allowMissing}

{docstring Iter.finitelyManySkips}

{docstring IterM.finitelyManySkips}

{docstring IterM.TerminationMeasures.Productive +allowMissing}

## Consuming Pure Iterators

{docstring Iter.fold}

{docstring Iter.foldM}

{docstring Iter.length}

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

## Consuming Monadic Iterators

{docstring IterM.drain}

{docstring IterM.fold}

{docstring IterM.foldM}

{docstring IterM.length}

{docstring IterM.any}

{docstring IterM.anyM}

{docstring IterM.all}

{docstring IterM.allM}

{docstring IterM.find? +allowMissing}

{docstring IterM.findM? +allowMissing}

{docstring IterM.findSome? +allowMissing}

{docstring IterM.findSomeM? +allowMissing}

{docstring IterM.atIdx?}

## Collectors

Collectors consume an iterator, returning all of its data in a list or array.
To be collected, an iterator must be finite.

{docstring Iter.toArray}

{docstring IterM.toArray}

{docstring Iter.toList}

{docstring IterM.toList}

{docstring Iter.toListRev}

{docstring IterM.toListRev}


# Iterator Combinators

The documentation for iterator combinators often includes {deftech}_marble diagrams_ that show the relationship between the elements returned by the underlying iterators and the elements returned by the combinator's iterator.
Marble diagrams provide examples, not full specifications.
These diagrams consist of a number of rows.
Each row shows an example of an iterator's output, where `-` indicates a {name PlausibleIterStep.skip}`skip`, a term indicates a value returned with {name PlausibleIterStep.yield}`yield`, and `⊥` indicates the end of iteration.
Spaces indicate that iteration did not occur.
Unbound identifiers in the marble diagram stand for arbitrary values of the iterator's element type.


Vertical alignment in the marble diagram indicates a causal relationship: when two elements are aligned, it means that consuming the iterator in the lower row results in the upper rows being consumed.
In particular, consuming up to the $`n`th column of the lower iterator results in the consumption of the first $`n` columns from the upper iterator.

:::paragraph
A marble diagram for an identity iterator combinator that returns each element from the underlying iterator looks like this:
```
it    ---a-----b---c----d⊥
it.id ---a-----b---c----d⊥
```
:::
:::paragraph
A marble diagram for an iterator combinator that duplicates each element of the underlying iterator looks like this:
```
it           ---a  ---b  ---c  ---d⊥
it.double    ---a-a---b-b---c-c---d-d⊥
```
:::
:::paragraph
The marble diagram for {name}`Iter.filter` shows how some elements of the underlying iterator do not occur in the filtered iterator, but also that stepping the filtered iterator results in a {name PlausibleIterStep.skip}`skip` when the underlying iterator returns a value that doesn't satisfy the predicate:
```
it            ---a--b--c--d-e--⊥
it.filter     ---a-----c-------⊥
```
The diagram requires an explanatory note:
> (given that `f a = f c = true` and `f b = f d = d e = false`)
:::
:::paragraph
The diagram for {name}`Iter.zip` shows how consuming the combined iterator consumes the underlying iterators:
```
left               --a        ---b        --c
right                 --x         --y        --⊥
left.zip right     -----(a, x)------(b, y)-----⊥
```
The zipped iterator emits {name PlausibleIterStep.skip}`skip`s so long as `left` does.
When `left` emits `a`, the zipped iterator emits one more {name PlausibleIterStep.skip}`skip`.
After this, the zipped iterator switches to consuming `right`, and it emits {name PlausibleIterStep.skip}`skip`s so long as `right` does.
When `right` emits `x`, the zipped iterator emits the pair `(a, x)`.
This interleaving of `left` and `right` continues until one of them stops, at which point the zipped iterator stops.
Blank spaces in the upper rows of the marble diagram indicate that the iterator is not being consumed at that step.
:::


## Pure Combinators

{docstring IterM.mk}

{docstring Iter.toIterM}

{docstring Iter.take}

{docstring Iter.takeWhile}

{docstring Iter.toTake}

{docstring Iter.drop}

{docstring Iter.dropWhile}

{docstring Iter.stepSize}

{docstring Iter.map}

{docstring Iter.mapM}

{docstring Iter.mapWithPostcondition}

{docstring Iter.uLift}

{docstring Iter.flatMap}

{docstring Iter.flatMapM}

{docstring Iter.flatMapAfter}

{docstring Iter.flatMapAfterM}

{docstring Iter.filter}

{docstring Iter.filterM}

{docstring Iter.filterWithPostcondition}

{docstring Iter.filterMap}

{docstring Iter.filterMapM}

{docstring Iter.filterMapWithPostcondition}

{docstring Iter.zip}

{docstring Iter.attachWith}


## Monadic Combinators

{docstring IterM.toIter}

{docstring IterM.take}

{docstring IterM.takeWhile}

{docstring IterM.takeWhileM}

{docstring IterM.takeWhileWithPostcondition}

{docstring IterM.toTake}

{docstring IterM.drop}

{docstring IterM.dropWhile}

{docstring IterM.dropWhileM}

{docstring IterM.dropWhileWithPostcondition}

{docstring IterM.stepSize}

{docstring IterM.map}

{docstring IterM.mapM}

{docstring IterM.mapWithPostcondition}

{docstring IterM.uLift}

{docstring IterM.flatMap}

{docstring IterM.flatMapM}

{docstring IterM.flatMapAfter}

{docstring IterM.flatMapAfterM}

{docstring IterM.filter}

{docstring IterM.filterM}

{docstring IterM.filterWithPostcondition}

{docstring IterM.filterMap}

{docstring IterM.filterMapM}

{docstring IterM.filterMapWithPostcondition}

{docstring IterM.zip}

{docstring IterM.attachWith}

# Reasoning About Iterators

## Reasoning About Consumers

The iterator library provides a large number of useful lemmas.
Most theorems about finite iterators can be proven by rewriting the statement to one about lists, using the fact that the correspondence between iterator combinators and corresponding list operations has already been proved.
In practice, many of these theorems are already registered as {tactic}`simp` lemmas.

:::paragraph
The lemmas have a very predictable naming system, and many are in the {tech}[default simp set].
Some of the most important include:

 * Consumer lemmas such as {name}`Iter.all_toList`, {name}`Iter.any_toList`, and {name}`Iter.foldl_toList` that introduce lists as a model.

 * Simplification lemmas such as {name}`Iter.toList_map` that {name}`Iter.toList_filter` push the list model “inwards” in the goal.

 * Producer lemmas such as {name}`List.toList_iter` and {name}`Array.toList_iter` that replace a producer with a list model, removing iterators from the goal entirely.

The latter two categories are typically automatic with {tactic}`simp`.
:::

:::example "Reasoning via Lists"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
Every element returned by an iterator that multiplies the numbers consumed some other iterator by two is even.
To prove this statement, {name}`Iter.all_toList`, {name}`Iter.toList_map`, and {name}`Array.toList_iter` are used to replace the statement about iterators with one about lists, after which {tactic}`simp` discharges the goal:
```lean
example (l : Array Nat) :
    (l.iter.map (· * 2)).all (· % 2 = 0) := by
  rw [← Iter.all_toList]
  rw [Iter.toList_map]
  rw [Array.toList_iter]
  simp
```

In fact, because most of the needed lemmas are in the {tech}[default simp set], the proof can be quite short:
```lean
example (l : Array Nat) :
    (l.iter.map (· * 2)).all (· % 2 = 0) := by
  simp [← Iter.all_toList]
```
:::

## Stepwise Reasoning

When there are not enough lemmas to prove a property by rewriting to a list model, it can be necessary to prove things about iterators by reasoning directly about their step functions.
The induction principles in this section are useful for stepwise reasoning.

{docstring Iter.inductSkips}

{docstring IterM.inductSkips}

{docstring Iter.inductSteps}

{docstring IterM.inductSteps}

The standard library also includes lemmas for the stepwise behavior of all the producers and combinators.
Examples include {name}`List.step_iter_nil`, {name}`List.step_iter_cons`, {name}`IterM.step_map`.

## Monads for Reasoning

{docstring Std.Iterators.PostconditionT}

{docstring Std.Iterators.PostconditionT.run}

{docstring Std.Iterators.PostconditionT.lift}

{docstring Std.Iterators.PostconditionT.liftWithProperty}

{docstring Iter.IsPlausibleIndirectOutput +allowMissing}

{docstring HetT}

{docstring IterM.stepAsHetT}

{docstring HetT.lift}

{docstring HetT.prun}

{docstring HetT.pure}

{docstring HetT.map}

{docstring HetT.pmap}

{docstring HetT.bind}

{docstring HetT.pbind}

## Equivalence

Iterator equivalence is defined in terms of the observable behavior of iterators, rather than their implementations.
In particular, the internal state is ignored.

{docstring Iter.Equiv}

{docstring IterM.Equiv}
