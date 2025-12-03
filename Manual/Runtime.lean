/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta
import Manual.Meta.LexedText
import Manual.Papers

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

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
    In particular, Lean uses {tech (key := "reference count")}[reference counting], where each allocated object maintains a count of incoming references.
    The compiler emits calls to memory management routines that allocate memory and modify reference counts, and these routines are provided by the runtime, along with the data structures that represent Lean values in compiled code.

 : Multiple Threads

    The {name}`Task` API provides the ability to write parallel and concurrent code.
    The runtime is responsible for scheduling Lean tasks across operating-system threads.

 : Primitive operators

    Many built-in types, including {lean}`Nat`, {lean}`Array`, {lean}`String`, and fixed-width integers, have special representations for reasons of efficiency.
    The runtime provides implementations of these types' primitive operators that take advantage of these optimized representations.


There are many primitive operators.
They are described in their respective sections under {ref "basic-types"}[Basic Types].

# Boxing
%%%
tag := "boxing"
%%%

:::paragraph
Lean values may be represented at runtime in two ways:
* {deftech}_Boxed_ values may be pointers to heap values or require shifting and masking.
* {deftech}_Unboxed_ values are immediately available.
:::

Boxed values are either a pointer to an object, in which case the lowest-order bit is 0, or an immediate value, in which case the lowest-order bit is 1 and the value is found by shifting the representation to the right by one bit.

Types with an unboxed representation, such as {name}`UInt8` and {tech}[enum inductive] types, are represented as the corresponding C types in contexts where the compiler can be sure that the value has said type.
In some contexts, such as generic container types like {name}`Array`, otherwise-unboxed values must be boxed prior to storage.
In other words, {name}`Bool.not` is called with and returns unboxed `uint8_t` values because the {tech}[enum inductive] type {name}`Bool` has an unboxed representation, but the individual {name}`Bool` values in an {lean}`Array Bool` are boxed.
A field of type {lean}`Bool` in an inductive type's constructor is represented unboxed, while {lean}`Bool`s stored in polymorphic fields that are instantiated as {lean}`Bool` are boxed.


# Reference Counting
%%%
tag := "reference-counting"
%%%

Lean uses {deftech (key := "reference count")}_reference counting_ for memory management.
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
Because the verifiable fragment of Lean cannot create cyclic data, the Lean runtime does not have a technique to detect it.
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
def process (str : String) (h : str.startPos ≠ str.endPos) : IO Unit := do
  IO.println ((dbgTraceIfShared "String update" str).startPos.set ' ' h)

def main : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trimAscii.copy
  if h : line.startPos ≠ line.endPos then
    process line h
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
def process (str : String) (h : str.startPos ≠ str.endPos) : IO Unit := do
  IO.println ((dbgTraceIfShared "String update" str).startPos.set ' ' h)

def main : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trimAscii.copy
  if h : line.startPos ≠ line.endPos then
    process line h
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
```leanOutput p1 (allowDiff := 5)
[Compiler.IR] [result]
    def process._closed_0 : obj :=
      let x_1 : obj := "";
      ret x_1
    def process (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := process._closed_0;
      let x_6 : obj := ctor_0[Prod.mk] x_4 x_5;
      ret x_6
```

The IR for {lean}`process'`, on the other hand, increments the reference count of the string just before calling {name}`String.set`.
Thus, the modified string `x_4` is a copy, regardless of whether the original reference to `x_1` is unique:
```leanOutput p2
[Compiler.IR] [result]
    def process' (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      inc x_1;
      let x_4 : obj := String.set x_1 x_2 x_3;
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
[Compiler.IR] [result]
    def discardElems (x_1 : ◾) (x_2 : tobj) : tobj :=
      let x_3 : tobj := discardElems._redArg x_2;
      ret x_3
    def discardElems._redArg (x_1 : tobj) : tobj :=
      case x_1 : tobj of
      List.nil →
        let x_2 : tagged := ctor_0[List.nil];
        ret x_2
      List.cons →
        let x_3 : u8 := isShared x_1;
        case x_3 : u8 of
        Bool.false →
          let x_4 : tobj := proj[1] x_1;
          let x_5 : tobj := proj[0] x_1;
          dec x_5;
          let x_6 : tagged := ctor_0[PUnit.unit];
          let x_7 : tobj := discardElems._redArg x_4;
          set x_1[1] := x_7;
          set x_1[0] := x_6;
          ret x_1
        Bool.true →
          let x_8 : tobj := proj[1] x_1;
          inc x_8;
          dec x_1;
          let x_9 : tagged := ctor_0[PUnit.unit];
          let x_10 : tobj := discardElems._redArg x_8;
          let x_11 : obj := ctor_1[List.cons] x_9 x_10;
          ret x_11
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

# Foreign Function Interface
%%%
tag := "ffi"
%%%


*The current interface was designed for internal use in Lean and should be considered unstable*.
It will be refined and extended in the future.

Lean offers efficient interoperability with any language that supports the C ABI.
This support is, however, currently limited to transferring Lean data types; in particular, it is not yet possible to pass or return compound data structures such as C {c}`struct`s by value from or to Lean.

There are two primary attributes for interoperating with other languages:
  {TODO}[It can also be used with `def` to provide an internal definition, but ensuring consistency of both definitions is up to the user.]
* `@[export sym] def leanSym : ...`

:::syntax attr (title := "External Symbols")
```grammar
extern $s:str
```

Binds a Lean declaration to the specified external symbol.
:::

:::syntax attr (title := "Exported Symbols")
```grammar
export $x:ident
```
Exports a Lean constant with the unmangled symbol name `sym`.
:::


For simple examples of how to call foreign code from Lean and vice versa, see [the FFI](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/ffi) and [reverse FFI](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/reverse-ffi) examples in the Lean source repository.

## The Lean ABI

:::leanSection

```lean -show
variable {α₁ αₙ β αᵢ}
private axiom «α₂→…→αₙ₋₁».{u} : Type u
local macro "..." : term => ``(«α₂→…→αₙ₋₁»)
```

The Lean {deftech}_Application Binary Interface_ (ABI) describes how the signature of a Lean declaration is encoded in the platform-native calling convention.
It is based on the standard C ABI and calling convention of the target platform.
Lean declarations can be marked for interaction with foreign functions using either the attribute {attr}`extern "sym"`, which causes compiled code to use the C declaration {c}`sym` as the implementation, or the attribute {attr}`export sym`, which makes the declaration available as {c}`sym` to C.

In both cases, the C declaration's type is derived from the Lean type of the declaration with the attribute.
Let {lean}`α₁ → ... → αₙ → β` be the declaration's {tech (key := "normal form")}[normalized] type.
If `n` is 0, the corresponding C declaration is
```c
extern s sym;
```
where {c}`s` is the C translation of {lean}`β` as specified in {ref "ffi-types"}[the next section].
In the case of a definition marked {attr}`extern`, the symbol's value is only guaranteed to be initialized after calling the Lean module's initializer or that of an importing module.
The section on {ref "ffi-initialization"}[initialization] describes initializers in greater detail.

If `n` is greater than 0, the corresponding C declaration is
```c
s sym(t₁, ..., tₙ);
```
where the parameter types `tᵢ` are the C translations of the types {lean}`αᵢ`.
In the case of {attr}`extern`, all {tech}[irrelevant] types are removed first.
:::

### Translating Types from Lean to C
%%%
tag := "ffi-types"
%%%

```lean -show
universe u
variable (p : Prop)
private axiom «...» : Sort u
local macro "..." : term => ``(«...»)
```

In the {tech (key := "application binary interface")}[ABI], Lean types are translated to C types as follows:

* The integer types {lean}`UInt8`, …, {lean}`UInt64`, {lean}`USize` are represented by the C types {c}`uint8_t`, ..., {c}`uint64_t`, {c}`size_t`, respectively.
  If their {ref "fixed-int-runtime"}[run-time representation] requires {tech (key := "boxed")}[boxing], then they are unboxed at the FFI boundary.
* {lean}`Char` is represented by {c}`uint32_t`.
* {lean}`Float` is represented by {c}`double`.
* {name}`Nat` and {name}`Int` are represented by {c}`lean_object *`.
  Their runtime values is either a pointer to an opaque bignum object or, if the lowest bit of the "pointer" is 1 ({c}`lean_is_scalar`), an encoded natural number or integer ({c}`lean_box`/{c}`lean_unbox`).
* A universe {lean}`Sort u`, type constructor {lean}`... → Sort u`, or proposition {lean}`p`​` :`{lean}` Prop` is {tech}[irrelevant] and is either statically erased (see above) or represented as a {c}`lean_object *` with the runtime value {c}`lean_box(0)`
* The ABI for other inductive types that don't have special compiler support depends on the specifics of the type.
  It is the same as the {ref "run-time-inductives"}[run-time representation] of these types.
  Its runtime value is either a pointer to an object of a subtype of {c}`lean_object` (see the "Inductive types" section below) or it is the value {c}`lean_box(cidx)` for the {c}`cidx`th constructor of an inductive type if this constructor does not have any relevant parameters.

  ```lean -show
  variable (u : Unit)
  ```

:::example "`Unit` in the ABI"
The runtime value of {lean}`u`​` : `{lean}`Unit` is always `lean_box(0)`.
:::

### Borrowing
%%%
tag := "ffi-borrowing"
%%%

By default, all {c}`lean_object *` parameters of an {attr}`extern` function are considered {deftech}_owned_.
The external code is passed a “virtual RC token” and is responsible for passing this token along to another consuming function (exactly once) or freeing it via {c}`lean_dec`.
To reduce reference counting overhead, parameters can be marked as {deftech}_borrowed_ by prefixing their type with {keywordOf Lean.Parser.Term.borrowed}`@&`.
Borrowed objects must only be passed to other non-consuming functions (arbitrarily often) or converted to owned values using {c}`lean_inc`.
In `lean.h`, the {c}`lean_object *` aliases {c}`lean_obj_arg` and {c}`b_lean_obj_arg` are used to mark this difference on the C side.
Return values and `@[export]` parameters are always owned at the moment.

:::syntax term (title := "Borrowed Parameters")
```grammar
@& $_
```
Parameters may be marked as {tech}[borrowed] by prefixing their types with {keyword}`@&`.
:::

## Initialization
%%%
tag := "ffi-initialization"
%%%

When including Lean code in a larger program, modules must be {deftech (key := "initialize")}_initialized_ before accessing any of their declarations.
Module initialization entails:
* initialization of all “constant definitions” (nullary functions), including closed terms lifted out of other functions,
* execution of all code marked with the {attr}`init` attribute, and
* execution of all code marked with the {attr}`builtin_init` attribute, if the `builtin` parameter of the module initializer has been set.

The module initializer is automatically run with the `builtin` flag for executables compiled from Lean code and for “plugins” loaded with `lean --plugin`.
For all other modules imported by `lean`, the initializer is run without `builtin`.
In other words, {attr}`init` functions are run if and only if their module is imported, regardless of whether they have native code available, while {attr}`builtin_init` functions are only run for native executable or plugins, regardless of whether their module is imported.
The Lean compiler uses built-in initializers for purposes such as registering basic parsers that should be available even without importing their module, which is necessary for bootstrapping.

The initializer for module `A.B` is called {c}`initialize_A_B` and will automatically initialize any imported modules.
Module initializers are idempotent when run with the same `builtin` flag, but not thread-safe.
Together with initialization of the Lean runtime, code like the following should be run exactly once before accessing any Lean declarations:
```c
void lean_initialize_runtime_module();
void lean_initialize();
lean_object * initialize_A_B(uint8_t builtin, lean_object *);
lean_object * initialize_C(uint8_t builtin, lean_object *);
...

lean_initialize_runtime_module();
// Necessary (and replaces `lean_initialize_runtime_module`) for code that
// (indirectly) accesses the `Lean` package:
//lean_initialize();

lean_object * res;
// use same default as for Lean executables
uint8_t builtin = 1;
res = initialize_A_B(builtin, lean_io_mk_world());
if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
} else {
    lean_io_result_show_error(res);
    lean_dec(res);
    // do not access Lean declarations if initialization failed
    return ...;
}
res = initialize_C(builtin, lean_io_mk_world());
if (lean_io_result_is_ok(res)) {
...

// Necessary for code that (indirectly) uses `Task`
//lean_init_task_manager();
lean_io_mark_end_initialization();
```

In addition, any other thread not spawned by the Lean runtime itself must be initialized for Lean use by calling
```c
void lean_initialize_thread();
```
and should be finalized in order to free all thread-local resources by calling
```c
void lean_finalize_thread();
```

## `@[extern]` in the Interpreter

The Lean interpreter can run Lean declarations for which symbols are available in loaded shared libraries, which includes declarations that are marked {attr}`extern`.
To run this code (e.g. with {keywordOf Lean.Parser.Command.eval}`#eval`), the following steps are necessary:
  1. The module containing the declaration and its dependencies must be compiled into a shared library
  1. This shared library should be provided to `lean --load-dynlib=` to run code that imports the module.

It is not sufficient to load the foreign library containing the external symbol because the interpreter depends on code that is emitted for each {attr}`extern` declaration.
Thus it is not possible to interpret an {attr}`extern` declaration in the same file.
The Lean source repository contains an example of this usage in [`tests/compiler/foreign`](https://github.com/leanprover/lean4/tree/master/tests/compiler/foreign/).
