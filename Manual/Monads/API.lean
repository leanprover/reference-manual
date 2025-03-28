/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "API Reference" =>

In addition to the general functions described here, there are some functions that are conventionally defined as part of the API of in the namespace of each collection type:
 * `mapM` maps a monadic function.
 * `forM` maps a monadic function, throwing away the result.
 * `filterM` filters using a monadic predicate, returning the values that satisfy it.


::::example "Monadic Collection Operations"
{name}`Array.filterM` can be used to write a filter that depends on a side effect.

:::ioExample
```ioLean
def values := #[1, 2, 3, 5, 8]
def main : IO Unit := do
  let filtered ← values.filterM fun v => do
    repeat
      IO.println s!"Keep {v}? [y/n]"
      let answer := (← (← IO.getStdin).getLine).trim
      if answer == "y" then return true
      if answer == "n" then return false
    return false
  IO.println "These values were kept:"
  for v in filtered do
    IO.println s!" * {v}"
```
```stdin
y
n
oops
y
n
y
```
```stdout
Keep 1? [y/n]
Keep 2? [y/n]
Keep 3? [y/n]
Keep 3? [y/n]
Keep 5? [y/n]
Keep 8? [y/n]
These values were kept:
 * 1
 * 3
 * 8
```
:::
::::

# Discarding Results

The {name}`discard` function is especially useful when using an action that returns a value only for its side effects.

{docstring discard}

# Control Flow

{docstring guard}

{docstring optional}

# Lifting Boolean Operations

{docstring andM}

{docstring orM}

{docstring notM}

# Kleisli Composition

{deftech}_Kleisli composition_ is the composition of monadic functions, analogous to {name}`Function.comp` for ordinary functions.

{docstring Bind.kleisliRight}

{docstring Bind.kleisliLeft}

# Re-Ordered Operations

Sometimes, it can be convenient to partially apply a function to its second argument.
These functions reverse the order of arguments, making it this easier.

{docstring Functor.mapRev}

{docstring Bind.bindLeft}
