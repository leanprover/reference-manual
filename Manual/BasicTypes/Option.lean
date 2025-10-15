/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Optional Values" =>
%%%
tag := "option"
%%%

:::::leanSection

```lean -show
variable {α : Type u} (v : α) {β : Type v}
```

{lean}`Option α` is the type of values which are either {lean}`some v` for some {lean}`v`﻿` : `﻿{lean}`α`, or {lean  (type := "Option α")}`none`.
In functional programming, this type is used similarly to nullable types: {lean  (type := "Option α")}`none` represents the absence of a value.
Additionally, partial functions from {lean}`α` to {lean}`β` can be represented by the type {lean}`α → Option β`, where {lean  (type := "Option β")}`none` results when the function is undefined for some input.
Computationally, these partial functions represent the possibility of failure or errors, and they correspond to a program that can terminate early but not throw an informative exception.

{lean}`Option` can also be thought of as being similar to a list that contains at most one element.
From this perspective, iterating over {lean}`Option` consists of carrying out an operation only when a value is present.
The {lean}`Option` API makes frequent use of this perspective.

::::leanSection

:::example "Options as Nullability"

```imports
import Std
```

```lean -show
open Std (HashMap)
variable {Coll} [BEq α] [Hashable α] (a : α) (b : β) {xs : Coll} [GetElem Coll α β fun _ _ => True] {i : α} {m : HashMap α β}
```

The function {name}`Std.HashMap.get?` looks up a specified key `a : α` inside a {lean}`HashMap α β`:

```signature
Std.HashMap.get?.{u, v} {α : Type u} {β : Type v}
  [BEq α] [Hashable α]
  (m : HashMap α β) (a : α) :
  Option β
```
Because there is no way to know in advance whether the key is actually in the map, the return type is {lean}`Option β`, where {lean  (type := "Option β")}`none` means the key was not in the map, and {lean}`some b` means that the key was found and `b` is the value retrieved.

The {lean}`xs[i]` syntax, which is used to index into collections when there is an available proof that {lean}`i` is a valid index into {lean}`xs`, has a variant {lean}`xs[i]?` that returns an optional value depending on whether the given index is valid.
If {lean}`m`﻿` : `﻿{lean}`HashMap α β` and {lean}`a`﻿` : `﻿{lean}`α`, then {lean}`m[a]?` is equivalent to {lean}`HashMap.get? m a`.

:::
::::

:::example "Options as Safe Nullability"
In many programming languages, it is important to remember to check for the null value.
When using {name}`Option`, the type system requires these checks in the right places: {lean}`Option α` and {lean}`α` are not the same type, and converting from one to the other requires handling the case of {lean  (type := "Option α")}`none`.
This can be done via helpers such as {name}`Option.getD`, or with pattern matching.

```imports
import Std
```

```lean
def postalCodes : Std.HashMap Nat String :=
  .empty |>.insert 12345 "Schenectady"
```

```lean (name := getD)
#eval postalCodes[12346]?.getD "not found"
```
```leanOutput getD
"not found"
```

```lean (name := m)
#eval
  match postalCodes[12346]? with
  | none => "not found"
  | some city => city
```
```leanOutput m
"not found"
```

```lean (name := iflet)
#eval
  if let some city := postalCodes[12345]? then
    city
  else
    "not found"
```
```leanOutput iflet
"Schenectady"
```

:::

:::::

{docstring Option}


# Coercions

```lean -show
section
variable {α : Type u} (line : String)
```

There is a {tech}[coercion] from {lean}`α` to {lean}`Option α` that wraps a value in {lean}`some`.
This allows {name}`Option` to be used in a style similar to nullable types in other languages, where values that are missing are indicated by {name}`none` and values that are present are not specially marked.

:::example "Coercions and {name}`Option`"
In {lean}`getAlpha`, a line of input is read.
If the line consists only of letters (after removing whitespace from the beginning and end of it), then it is returned; otherwise, the function returns {name}`none`.

```lean
def getAlpha : IO (Option String) := do
  let line := (← (← IO.getStdin).getLine).trim
  if line.length > 0 && line.all Char.isAlpha then
    return line
  else
    return none
```

In the successful case, there is no explicit {name}`some` wrapped around {lean}`line`.
The {name}`some` is automatically inserted by the coercion.

:::

```lean -show
end
```


# API Reference

## Extracting Values

{docstring Option.get}

{docstring Option.get!}

{docstring Option.getD}

{docstring Option.getDM}

{docstring Option.getM}

{docstring Option.elim}

{docstring Option.elimM}

{docstring Option.merge}


## Properties and Comparisons

{docstring Option.isNone}

{docstring Option.isSome}

{docstring Option.isEqSome}

:::leanSection
```lean -show
variable {α} [DecidableEq α] [LT α] [Min α] [Max α]
```
Ordering of optional values typically uses the {inst}`DecidableEq (Option α)`, {inst}`LT (Option α)`, {inst}`Min (Option α)`, and {inst}`Max (Option α)` instances.
:::

{docstring Option.min}

{docstring Option.max}

{docstring Option.lt}

{docstring Option.decidableEqNone}

## Conversion

{docstring Option.toArray}

{docstring Option.toList}

{docstring Option.repr}

{docstring Option.format}

## Control

{name}`Option` can be thought of as describing a computation that may fail to return a value.
The {inst}`Monad Option` instance, along with {inst}`Alternative Option`, is based on this understanding.
Returning {name}`none` can also be thought of as throwing an exception that contains no interesting information, which is captured in the {inst}`MonadExcept Unit Option` instance.

{docstring Option.guard}

{docstring Option.bind}

{docstring Option.bindM}

{docstring Option.join}

{docstring Option.sequence}

{docstring Option.tryCatch}

{docstring Option.or}

{docstring Option.orElse}


## Iteration

{name}`Option` can be thought of as a collection that contains at most one value.
From this perspective, iteration operators can be understood as performing some operation on the contained value, if present, or doing nothing if not.

{docstring Option.all}

{docstring Option.any}

{docstring Option.filter}

{docstring Option.forM}

{docstring Option.map}

{docstring Option.mapA}

{docstring Option.mapM}

## Recursion Helpers

{docstring Option.attach}

{docstring Option.attachWith}

{docstring Option.unattach}

## Reasoning

{docstring Option.choice}

{docstring Option.pbind}

{docstring Option.pelim}

{docstring Option.pmap}
