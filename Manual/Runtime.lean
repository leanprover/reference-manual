/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta
import Manual.Papers

open Manual
open Verso.Genre Manual InlineLean

#doc (Manual) "Run-Time Code" =>
%%%
tag := "runtime"
%%%

Compiled Lean code uses services provided by the Lean runtime.
The runtime contains efficient, low-level primitives that bridge the gap between the Lean language and the supported platforms.
These services include:

 : Memory management

    Lean does not require programmers to manually manage memory.
    Space is allocated when needed to store a value, and values that can no longer be reached (and are thus irrelevant) are deallocated.
    In particular, Lean uses {tech key:="reference count"}[reference counting], where each allocated object maintains a count of incoming references.
    The compiler emits calls to memory management routines that allocate memory and modify reference counts, and these routines are provided by the runtime, along with the data structures that represent Lean values in compiled code.

 : Multiple Threads

    The {name}`Task` API provides the ability to write parallel and concurrent code.
    The runtime is responsible for scheduling Lean tasks across operating-system threads.

 : Primitive operators

    Many built-in types, including {lean}`Nat`, {lean}`Array`, {lean}`String`, and fixed-width integers, have special representations for reasons of efficiency.
    The runtime provides implementations of these types' primitive operators that take advantage of these optimized representations.


There are many primitive operators.
They are described in their respective sections under {ref "basic-types"}[Basic Types].


# Reference Counting
%%%
tag := "reference-counting"
%%%

Lean uses {deftech key:="reference count"}_reference counting_ for memory management.
Each allocated object maintains a count of how many other objects refer to it.
When a new reference is added, the count is incremented, and when a reference is dropped, the count is decremented.
When a reference count reaches zero, the object is no longer reachable and can play no part in the further execution of the program.
It is deallocated and all of its references to other objects are dropped, which may trigger further deallocations.

:::paragraph
Reference counting provides a number of benefits:

 : Re-Use of Memory

    If an object's reference count drops to zero just as another of the same size is to be allocated, then the original object's memory can be safely re-used for the new object.
    As a result, many common data-structure traversals (such as {name}`List.map`) do not need to allocate memory when there is exactly one reference to the data structure to be traversed.

 : Opportunistic In-Place Updates

    Primitive types, such as {ref "String"}[strings] and {ref "Array"}[arrays], may provide operations that copy shared data but modify unshared data in-place.
    As long as they hold the only reference to the value being modified, many operations on these primitive types will modify it rather than copy it.
    This can lead to substantial performance benefits.
    Carefully-written {lean}`Array` code avoids the performance overhead of immutable data structures while maintaining the ease of reasoning provided by pure functions.

 : Predictability

    Reference counts are decremented at predictable times.
    As a result, reference-counted objects can be used to manage other resources, such as file handles.
    In Lean, a {name IO.FS.Handle}`Handle` does not need to be explicitly closed because it is closed immediately when it is no longer accessible.

 : Simpler FFI

    Objects managed with reference counting don't need to be relocated as part of reclaiming unused memory.
    This greatly simplifies interaction with code written in other languages, such as C.

:::

The traditional drawbacks of reference counting include the performance overhead due to updating reference counts along with the inability to recognize and deallocate cyclic data.
The former drawback is minimized by an analysis based on _borrowing_ that allows many reference count updates to be elided.
Nevertheless, multi-threaded code requires that reference count updates are synchronized between threads, which also imposes a substantial overhead.
To reduce this overhead, Lean values are partitioned into those which are reachable from multiple threads and those which are not.
Single-threaded reference counts can be updated much faster than multi-threaded reference counts, and many values are accessed only on a single thread.
Together, these techniques greatly reduce the performance overhead of reference counting.
Because Lean cannot create cyclic data, no technique is needed to detect it.
{citet countingBeans}[] provide more details on the implementation of reference counting in Lean.

## Observing Uniqueness

Ensuring that arrays and strings are uniquely referenced is key to writing fast code in Lean.
The primitive {name}`dbgTraceIfShared` can be used to check whether a data structure is aliased.
When called, it returns its argument unchanged, printing the provided trace message if the argument's reference count is greater than one.

{docstring dbgTraceIfShared}

Due to the specifics of how {keywordOf Lean.Parser.Command.eval}`#eval` is implemented, using {name}`dbgTraceIfShared` with {keywordOf Lean.Parser.Command.eval}`#eval` can be misleading.
Instead, it should be used in code that's explicitly compiled and run.

::::example "Observing Uniqueness"
:::ioExample
This program reads a line of input from the user, printing it after replacing its first character with a space.
Replacing characters in a string uses an in-place update if the string is not shared and the characters are both contained in the 7-bit ASCII subset of Unicode.
The {name}`dbgTraceIfShared` call does nothing, indicating that the string will indeed be updated in place rather than copied.

```ioLean
def process (str : String) : IO Unit := do
  IO.println ((dbgTraceIfShared "String update" str).set 0 ' ')

def main : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trim
  process line
```

When run with this input:
```stdin
Here is input.
```

the program emits:
```stdout
 ere is input.
```
with an empty standard error output:
```stderr
```
:::

:::ioExample
This version of the program retains a reference to the original string, which necessitates copying the string in the call to {name}`String.set`.
This fact is visible in its standard error output.

```ioLean
def process (str : String) : IO Unit := do
  IO.println ((dbgTraceIfShared "String update" str).set 0 ' ')

def main : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trim
  process line
  IO.println "Original input:"
  IO.println line
```

When run with this input:
```stdin
Here is input.
```

the program emits:
```stdout
 ere is input.
Original input:
Here is input.
```

In its standard error, the message passed to {name}`dbgTraceIfShared` is visible.
```stderr
shared RC String update
```
:::
::::

## Compiler IR

The compiler option {option}`trace.compiler.ir.result` can be used to inspect the compiler's intermediate representation (IR) for a function.
In this intermediate representation, reference counting, allocation, and reuse are explicit:
 * The `isShared` operator checks whether a reference count is `1`.
 * `ctor_`$`n` allocates the $`n`th constructor of a type.
 * `proj_`$`n` retrieves the $`n`th field from a constructor value.
 * `set `$`x`﻿`[`$`n`﻿`]` mutates the $`n`th field of the constructor in $`x`.
 * `ret `$`x` returns the value in $`x`.

The specifics of reference count manipulations can depend on the results of optimization passes such as inlining.
While the vast majority of Lean code doesn't require this kind of attention to achieve good performance, knowing how to diagnose unique reference issues can be very important when writing performance-critical code.

{optionDocs trace.compiler.ir.result}

:::example "Reference Counts in IR"
Compiler IR can be used to observe when reference counts are incremented, which can help diagnose situations when a value is expected to have a unique incoming reference, but is in fact shared.
Here, {lean}`process` and {lean}`process'` each take a string as a parameter and modify it with {name}`String.set`, returning a pair of strings.
While {lean}`process` returns a constant string as the second element of the pair, {lean}`process'` returns the original string.

```lean
set_option trace.compiler.ir.result true
```
```lean (name := p1)
def process (str : String) : String × String :=
  (str.set 0 ' ', "")
```
```lean (name := p2)
def process' (str : String) : String × String:=
  (str.set 0 ' ', str)
```

The IR for {lean}`process` includes no `inc` or `dec` instructions.
If the incoming string `x_1` is a unique reference, then it is still a unique reference when passed to {name}`String.set`, which can then use in-place modification:
```leanOutput p1
[result]
def process._closed_1 : obj :=
  let x_1 : obj := "";
  ret x_1
def process (x_1 : obj) : obj :=
  let x_2 : u32 := 32;
  let x_3 : obj := 0;
  let x_4 : obj := String.set x_1 x_3 x_2;
  let x_5 : obj := process._closed_1;
  let x_6 : obj := ctor_0[Prod.mk] x_4 x_5;
  ret x_6
```

The IR for {lean}`process'`, on the other hand, increments the reference count of the string just before calling {name}`String.set`.
Thus, the modified string `x_4` is a copy, regardless of whether the reference to `x_1` is unique:
```leanOutput p2
[result]
def process' (x_1 : obj) : obj :=
  let x_2 : u32 := 32;
  let x_3 : obj := 0;
  inc x_1;
  let x_4 : obj := String.set x_1 x_3 x_2;
  let x_5 : obj := ctor_0[Prod.mk] x_4 x_1;
  ret x_5
```
:::

:::example "Memory Re-Use in IR"
The function {lean}`discardElems` is a simplified version of {name}`List.map` that replaces every element in a list with {lean}`()`.
Inspecting its intermediate representation demonstrates that it will re-use the list's memory when its reference is unique.

```lean (name := discardElems)
set_option trace.compiler.ir.result true

def discardElems : List α → List Unit
  | [] => []
  | x :: xs => () :: discardElems xs
```

This emits the following IR:

```leanOutput discardElems
[result]
def discardElems._rarg (x_1 : obj) : obj :=
  case x_1 : obj of
  List.nil →
    let x_2 : obj := ctor_0[List.nil];
    ret x_2
  List.cons →
    let x_3 : u8 := isShared x_1;
    case x_3 : u8 of
    Bool.false →
      let x_4 : obj := proj[1] x_1;
      let x_5 : obj := proj[0] x_1;
      dec x_5;
      let x_6 : obj := discardElems._rarg x_4;
      let x_7 : obj := ctor_0[PUnit.unit];
      set x_1[1] := x_6;
      set x_1[0] := x_7;
      ret x_1
    Bool.true →
      let x_8 : obj := proj[1] x_1;
      inc x_8;
      dec x_1;
      let x_9 : obj := discardElems._rarg x_8;
      let x_10 : obj := ctor_0[PUnit.unit];
      let x_11 : obj := ctor_1[List.cons] x_10 x_9;
      ret x_11
def discardElems (x_1 : ◾) : obj :=
  let x_2 : obj := pap discardElems._rarg;
  ret x_2
```

In the IR, the {name}`List.cons` case explicitly checks whether the argument value is shared (i.e. whether it's reference count is greater than one).
If the reference is unique, the reference count of the discarded list element `x_5` is decremented and the constructor value is reused.
If it is shared, a new {name}`List.cons` is allocated in `x_11` for the result.
:::


### More Topics
%%%
draft := true
%%%

:::planned 208

 * Compact regions

 * When should C code increment or decrement reference counts?

 * What is the meaning of the borrow annotation (`@&`)?

:::

# Multi-Threaded Execution

Lean includes primitives for parallel and concurrent programs, described using {tech}[tasks].
The Lean runtime system includes a task manager that assigns hardware resources to tasks.
Along with the API for defining tasks, this is described in detail in the {ref "concurrency"}[section on multi-threaded programs].
