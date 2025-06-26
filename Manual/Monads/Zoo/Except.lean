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

#doc (Manual) "Exceptions" =>
%%%
tag := "exception-monads"
%%%

Exception monads describe computations that terminate early (fail).
Failing computations provide their caller with an _exception_ value that describes _why_ they failed.
In other words, computations either return a value or an exception.
The inductive type {name}`Except` captures this pattern, and is itself a monad.

# Exceptions

{docstring Except}

{docstring Except.pure}

{docstring Except.bind}

{docstring Except.map}

{docstring Except.mapError}

{docstring Except.tryCatch}

{docstring Except.orElseLazy}

{docstring Except.isOk}

{docstring Except.toOption}

{docstring Except.toBool}


# Type Class

{docstring MonadExcept}

{docstring MonadExcept.ofExcept}

{docstring MonadExcept.orElse}

{docstring MonadExcept.orelse'}

{docstring MonadExceptOf}

{docstring throwThe}

{docstring tryCatchThe}

# “Finally” Computations

{docstring MonadFinally}

# Transformer

{docstring ExceptT}

{docstring ExceptT.lift}

{docstring ExceptT.run}

{docstring ExceptT.pure}

{docstring ExceptT.bind}

{docstring ExceptT.bindCont}

{docstring ExceptT.tryCatch}

{docstring ExceptT.mk}

{docstring ExceptT.map}

{docstring ExceptT.adapt}


# Exception Monads in Continuation Passing Style

```lean (show := false)
universe u
variable (α : Type u)
variable (ε : Type u)
variable {m : Type u → Type v}
```

Continuation-passing-style exception monads represent potentially-failing computations as functions that take success and failure continuations, both of which return the same type, returning that type.
They must work for _any_ return type.
An example of such a type is {lean}`(β : Type u) → (α → β) → (ε → β) → β`.
{lean}`ExceptCpsT` is a transformer that can be applied to any monad, so {lean}`ExceptCpsT ε m α` is actually defined as {lean}`(β : Type u) → (α → m β) → (ε → m β) → m β`.
Exception monads in continuation passing style have different performance characteristics than {name}`Except`-based state monads; for some applications, it may be worth benchmarking them.

```lean (show := false)
/-- info: (β : Type u) → (α → m β) → (ε → m β) → m β -/
#check_msgs in
#reduce (types := true) ExceptCpsT ε m α
```

{docstring ExceptCpsT}

{docstring ExceptCpsT.runCatch}

{docstring ExceptCpsT.runK}

{docstring ExceptCpsT.run}

{docstring ExceptCpsT.lift}
