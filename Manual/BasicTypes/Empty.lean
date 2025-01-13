/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "The Empty Type" =>
%%%
tag := "empty"
%%%

:::planned 170
 * What is {lean}`Empty`?
 * Contrast with {lean}`Unit` and {lean}`False`
 * Definitional equality
:::

The empty type {name}`Empty` represents impossible values.
It is an inductive type with no constructors whatsoever.

While the trivial type {name}`Unit`, which has a single constructor that takes no parameters, can be used to model computations where a result is unwanted or uninteresting, {name}`Empty` can be used in situations where no computation should be possible at all.
Instantiating a polymorphic type with {name}`Empty` can mark some of its constructors—those with a parameter of the corresponding type—as impossible; this can rule out certain code paths that are not desired.

The presence of a term with type {name}`Empty` indicates that an impossible code path has been reached.
There will never be a value with this type, due to the lack of constructors.
On an impossible code path, there's no reason to write further code; the function {name}`Empty.elim` can be used to escape an impossible path.

The universe-polymorphic equivalent of {name}`Empty` is {name}`PEmpty`.

{docstring Empty}

{docstring PEmpty}


:::example "Impossible Code Paths"

The type signature of the function {lean}`f` indicates that it might throw exceptions, but allows the exception type to be anything:
```lean
def f (n : Nat) : Except ε Nat := pure n
```

Instantiating {lean}`f`'s exception type with {lean}`Empty` exploits the fact that {lean}`f` never actually throws an exception to convert it to a function whose type indicates that no exceptions will be thrown.
In particular, it allows {lean}`Empty.elim` to be used to avoid handing the impossible exception value.

```lean
def g (n : Nat) : Nat :=
  match f (ε := Empty) n with
  | .error e =>
    Empty.elim e
  | .ok v => v
```
:::

# API Reference

{docstring Empty.elim}

{docstring PEmpty.elim}
