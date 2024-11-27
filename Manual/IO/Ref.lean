/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Mutable References" =>


While ordinary {tech}[state monads] encode stateful computations with tuples that track the contents of the state along with the computation's value, Lean's runtime system also provides mutable references that are always backed by mutable memory cells.
Mutable references have a type {lean}`IO.Ref` that indicates that a cell is mutable, and reads and writes must be explicit.
{lean}`IO.Ref` is implemented using {lean}`ST.Ref`, so the entire {ref "mutable-st-references"}[{lean}`ST.Ref` API] may also be used with {lean}`IO.Ref`.

{docstring IO.Ref}

{docstring IO.mkRef}



# State Transformers
%%%
tag := "mutable-st-references"
%%%


Mutable references are often useful in contexts where arbitrary side effects are undesired.
They can give a significant speedup when Lean is unable to optimize pure operations into mutation, and some algorithms are more easily expressed using mutable references than with state monads.
Additionally, it has a property that other side effects do not have: if all of the mutable references used by a piece of code are created during its execution, and no mutable references from the code escape to other code, then the result of evaluation is deterministic.

The {lean}`ST` monad is a restricted version of {lean}`IO` in which mutable state is the only side effect, and mutable references cannot escape.{margin}[{lean}`ST` was first described by {citehere launchbury94}[].]
{lean}`ST` takes a type parameter that is never used to classify any terms.
The {lean}`runST` function, which allow escape from {lean}`ST`, requires that the {lean}`ST` action that is passed to it can instantiate this type parameter with _any_ type.
This unknown type does not exist except as a parameter to a function, which means that values whose types are “marked” by it cannot escape its scope.

{docstring ST}

{docstring runST}

As with {lean}`IO` and {lean}`EIO`, there is also a variation of {lean}`ST` that takes a custom error type as a parameter.
Here, {lean}`ST` is analogous to {lean}`BaseIO` rather than {lean}`IO`, because {lean}`ST` cannot result in errors being thrown.

{docstring EST}

{docstring runEST}

{docstring ST.Ref}

{docstring ST.mkRef}

## Reading and Writing

{docstring ST.Ref.get}

{docstring ST.Ref.set}

::::example "Data races with {name ST.Ref.get}`get` and {name ST.Ref.set}`set`"
:::ioExample
```ioLean
def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      if cost < (← balance.get) then
        IO.sleep (← IO.rand 10 100).toUInt32
        balance.set ((← balance.get) - cost)
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance is negative!"
  else
    IO.println "Final balance is zero or positive."
```
```stdout
Sending out orders...
```
```stderr
Final balance is negative!
```
:::
::::

{docstring ST.Ref.modify}

::::example "Avoiding data races with {name ST.Ref.modify}`modify`"

This program launches 100 threads.
Each thread simulates a purchase attempt: it generates a random price, and if the account balance is sufficient, it decrements it by the price.
The balance check and the computation of the new value occur in an atomic call to {name}`ST.Ref.modify`.

:::ioExample
```ioLean
def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      balance.modify fun b =>
        if cost < b then
          b - cost
        else b
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance negative!"
  else
    IO.println "Final balance is zero or positive."
```
```stdout
Sending out orders...
Final balance is zero or positive.
```
```stderr
```
:::
::::

{docstring ST.Ref.modifyGet}

## Comparisons

{docstring ST.Ref.ptrEq}

## Concurrency

Mutable references can be used as a locking mechanism.
_Taking_ the contents of the reference causes attempts to take it or to read from it to block until it is {name ST.Ref.set}`set` again.
This is a low-level feature that can be used to implement other synchronization mechanisms; it's usually better to rely on higher-level abstractions when possible.

{docstring ST.Ref.take}

{docstring ST.Ref.swap}

{docstring ST.Ref.toMonadStateOf}


::::example "Reference Cells as Locks"
This program launches 100 threads.
Each thread simulates a purchase attempt: it generates a random price, and if the account balance is sufficient, it decrements it by the price.
If the balance is not sufficient, then it is not decremented.
Because each thread {name ST.Ref.take}`take`s the balance cell prior to checking it and only returns it when it is finished, the cell acts as a lock.
Unlike using {name}`ST.Ref.modify`, which atomically modifies the contents of the cell using a pure function, other {name}`IO` actions may occur in the critical section
This program's `main` function is marked {keywordOf Lean.Parser.Command.declaration}`unsafe` because {name ST.Ref.take}`take` itself is unsafe.

:::ioExample
```ioLean
unsafe def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)
  let validationUsed ← IO.mkRef false

  let mut orders := #[]

  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      let b ← balance.take
      if cost ≤ b then
        balance.set (b - cost)
      else
        balance.set b
        validationUsed.set true
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← validationUsed.get) then
    IO.println "Validation prevented a negative balance."

  if (← balance.get) < 0 then
    IO.eprintln "Final balance negative!"
  else
    IO.println "Final balance is zero or positive."
```

The program's output is:
```stdout
Sending out orders...
Validation prevented a negative balance.
Final balance is zero or positive.
```
:::
::::
