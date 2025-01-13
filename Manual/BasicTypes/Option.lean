/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Optional Values" =>
%%%
tag := "option"
%%%

{docstring Option}


# Coercions

```lean (show := false)
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

```lean (show := false)
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

{docstring Option.liftOrGet}

{docstring Option.merge}


## Properties and Comparisons

{docstring Option.isNone}

{docstring Option.isSome}

{docstring Option.isEqSome}

{docstring Option.min}

{docstring Option.max}

{docstring Option.lt}

{docstring Option.decidable_eq_none}

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
