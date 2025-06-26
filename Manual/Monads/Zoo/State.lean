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
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "State" =>
%%%
tag := "state-monads"
%%%

{tech}[State monads] provide access to a mutable value.
The underlying implementation may use a tuple to simulate mutability, or it may use something like {name}`ST.Ref` to ensure mutation.
Even those implementations that use a tuple may in fact use mutation at run-time due to Lean's use of mutation when there are unique references to values, but this requires a programming style that prefers {name}`modify` and {name}`modifyGet` over {name}`get` and {name}`set`.

# General State API

{docstring MonadState}

{docstring get}

{docstring modify}

{docstring modifyGet}

{docstring getModify}

{docstring MonadStateOf}

{docstring getThe}

{docstring modifyThe}

{docstring modifyGetThe}

# Tuple-Based State Monads

```lean (show := false)
variable {α σ : Type u}
```

The tuple-based state monads represent a computation with states that have type {lean}`σ` yielding values of type {lean}`α` as functions that take a starting state and yield a value paired with a final state, e.g. {lean}`σ → α × σ`.
The {name}`Monad` operations thread the state correctly through the computation.

{docstring StateM}

{docstring StateT}

{docstring StateT.run}

{docstring StateT.get}

{docstring StateT.set}

{docstring StateT.orElse}

{docstring StateT.failure}

{docstring StateT.run'}

{docstring StateT.bind}

{docstring StateT.modifyGet}

{docstring StateT.lift}

{docstring StateT.map}

{docstring StateT.pure}

# State Monads in Continuation Passing Style

Continuation-passing-style state monads represent stateful computations as functions that, for any type whatsoever, take an initial state and a continuation (modeled as a function) that accepts a value and an updated state.
An example of such a type is {lean}`(δ : Type u) → σ → (α → σ → δ) → δ`, though {lean}`StateCpsT` is a transformer that can be applied to any monad.
State monads in continuation passing style have different performance characteristics than tuple-based state monads; for some applications, it may be worth benchmarking them.


```lean (show := false)
/-- info: (δ : Type u) → σ → (α → σ → Id δ) → δ -/
#check_msgs in
#reduce (types := true) StateCpsT σ Id α
```
{docstring StateCpsT}

{docstring StateCpsT.lift}

{docstring StateCpsT.runK}

{docstring StateCpsT.run'}

{docstring StateCpsT.run}

# State Monads from Mutable References

```lean (show := false)
variable {m : Type → Type} {σ ω : Type} [STWorld σ m]
```

The monad {lean}`StateRefT σ m` is a specialized state monad transformer that can be used when {lean}`m` is a monad to which {name}`ST` computations can be lifted.
It implements the operations of {name}`MonadState` using an {name}`ST.Ref`, rather than pure functions.
This ensures that mutation is actually used at run time.

{name}`ST` and {name}`EST` require a phantom type parameter that's used together with {name}`runST`'s polymorphic function argument to encapsulate mutability.
Rather than require this as a parameter to the transformer, an auxiliary type class {name}`STWorld` is used to propagate it directly from {lean}`m`.

The transformer itself is defined as a {ref "syntax-ext"}[syntax extension] and an {ref "elaborators"}[elaborator], rather than an ordinary function.
This is because {name}`STWorld` has no methods: it exists only to propagate information from the inner monad to the transformed monad.
Nonetheless, its instances are terms; keeping them around could lead to unnecessarily large types.

{docstring STWorld}

:::syntax term (title := "`StateRefT`")
The syntax for {lean}`StateRefT σ m` accepts two arguments:

```grammar
StateRefT $_ $_
```

Its elaborator synthesizes an instance of {lean}`STWorld ω m` to ensure that {lean}`m` supports mutable references.
Having discovered the value of {lean}`ω`, it then produces the term {lean}`StateRefT' ω σ m`, discarding the synthesized instance.
:::

{docstring StateRefT'}

{docstring StateRefT'.get}

{docstring StateRefT'.set}

{docstring StateRefT'.modifyGet}

{docstring StateRefT'.run}

{docstring StateRefT'.run'}

{docstring StateRefT'.lift}
