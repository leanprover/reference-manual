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

#doc (Manual) "Combined Error and State Monads" =>

```lean (show := false)
variable (ε : Type u) (σ σ' : Type u) (α : Type u)
```

The {name}`EStateM` monad has both exceptions and mutable state.
{lean}`EStateM ε σ α` is logically equivalent to {lean}`ExceptT ε (StateM σ) α`.
While {lean}`ExceptT ε (StateM σ)` evaluates to the type {lean}`σ → Except ε α × σ`, the type {lean}`EStateM ε σ α` evaluates to {lean}`σ → EStateM.Result ε σ α`.
{name}`EStateM.Result` is an inductive type that's very similar to {name}`Except`, except both constructors have an additional field for the state.
In compiled code, this representation removes one level of indirection from each monadic bind.

```lean (show := false)
/-- info: σ → Except ε α × σ -/
#check_msgs in
#reduce (types := true) ExceptT ε (StateM σ) α

/-- info: σ → EStateM.Result ε σ α -/
#check_msgs in
#reduce (types := true) EStateM ε σ α
```

{docstring EStateM}

{docstring EStateM.Result}

{docstring EStateM.run}

{docstring EStateM.run'}

{docstring EStateM.adaptExcept}

{docstring EStateM.fromStateM (allowMissing := true)}

# State Rollback

Composing {name}`StateT` and {name}`ExceptT` in different orders causes exceptions to interact differently with state.
In one ordering, state changes are rolled back when exceptions are caught; in the other, they persist.
The latter option matches the semantics of most imperative programming languages, but the former is very useful for search-based problems.
Often, some but not all state should be rolled back; this can be achieved by “sandwiching” {name}`ExceptT` between two separate uses of {name}`StateT`.

To avoid yet another layer of indirection via the use of {lean}`StateT σ (EStateM ε σ') α`, {name}`EStateM` offers the {name}`EStateM.Backtrackable` {tech}[type class].
This class specifies some part of the state that can be saved and restored.
{name}`EStateM` then arranges for the saving and restoring to take place around error handling.

{docstring EStateM.Backtrackable}

There is a universally-applicable instance of {name EStateM.Backtrackable}`Backtrackable` that neither saves nor restores anything.
Because instance synthesis chooses the most recent instance first, the universal instance is used only if no other instance has been defined.

{docstring EStateM.nonBacktrackable}

# Implementations

These functions are typically not called directly, but rather are accessed through their corresponding type classes.

{docstring EStateM.map}

{docstring EStateM.pure}

{docstring EStateM.bind}

{docstring EStateM.orElse}

{docstring EStateM.orElse'}

{docstring EStateM.seqRight}

{docstring EStateM.tryCatch}

{docstring EStateM.throw}

{docstring EStateM.get}

{docstring EStateM.set}

{docstring EStateM.modifyGet}
