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

#doc (Manual) "Lifting Monads" =>

::::keepEnv

```lean (show := false)
variable {m m' n : Type u → Type v} [Monad m] [Monad m'] [Monad n] [MonadLift m n]
variable {α β : Type u}
```

When one monad is at least as capable as another, then actions from the latter monad can be used in a context that expects actions from the former.
This is called {deftech (key := "lift")}_lifting_ the action from one monad to another.
Lean automatically inserts lifts when they are available; lifts are defined in the {name}`MonadLift` type class.
Automatic monad lifting is attempted before the general {tech}[coercion] mechanism.

{docstring MonadLift}

{tech key:="lift"}[Lifting] between monads is reflexive and transitive.
Any monad can run its own actions.
Lifts from {lean}`m` to {lean}`m'` and from {lean}`m'` to {lean}`n` can be composed to yield a lift from {lean}`m` to {lean}`n`.
The utility type class {name}`MonadLiftT` constructs lifts via the reflexive and transitive closure of {name}`MonadLift` instances.
Users should not define new instances of {name}`MonadLiftT`, but it is useful as an instance implicit parameter to a polymorphic function that needs to run actions from multiple monads in some user-provided monad.

{docstring MonadLiftT}

When a term of type {lean}`n β` is expected, but the provided term has type {lean}`m α`, and the two types are not definitionally equal, Lean attempts to insert lifts and coercions before reporting an error.
There are the following possiblities:
 1. If {lean}`m` and {lean}`n` can be unified to the same monad, then {lean}`α` and {lean}`β` are not the same.
    In this case, no monad lifts are necessary, but the value in the monad must be {tech key:="coercion"}[coerced].
    If the appropriate coercion is found, then a call to {name}`Lean.Internal.coeM` is inserted, which has the following signature:
    ```signature
    Lean.Internal.coeM.{u, v} {m : Type u → Type v} {α β : Type u}
      [(a : α) → CoeT α a β] [Monad m]
      (x : m α) :
      m β
    ```
 2. If {lean}`α` and {lean}`β` can be unified, then the monads differ.
    In this case, a monad lift is necessary to transform an expression with type {lean}`m α` to {lean}`n α`.
    If {lean}`m` can be lifted to {lean}`n` (that is, there is an instance of {lean}`MonadLiftT m n`) then a call to {name}`liftM`, which is an alias for {name}`MonadLiftT.monadLift`, is inserted.
    ```signature
    liftM.{u, v, w}
      {m : Type u → Type v} {n : Type u → Type w}
      [self : MonadLiftT m n] {α : Type u} :
      m α → n α
    ```
 3. If neither {lean}`m` and {lean}`n` nor {lean}`α` and {lean}`β` can be unified, but {lean}`m` can be lifted into {lean}`n` and {lean}`α` can be coerced to {lean}`β`, then a lift and a coercion can be combined.
    This is done by inserting a call to {name}`Lean.Internal.liftCoeM`:
    ```signature
    Lean.Internal.liftCoeM.{u, v, w}
      {m : Type u → Type v} {n : Type u → Type w}
      {α β : Type u}
      [MonadLiftT m n] [(a : α) → CoeT α a β] [Monad n]
      (x : m α) :
      n β
    ```

As their names suggest, {name}`Lean.Internal.coeM` and {name}`Lean.Internal.liftCoeM` are implementation details, not part of the public API.
In the resulting terms, occurrences of {name}`Lean.Internal.coeM`, {name}`Lean.Internal.liftCoeM`, and coercions are unfolded.

::::

::::keepEnv
:::example "Lifting `IO` Monads"
There is an instance of {lean}`MonadLift BaseIO IO`, so any `BaseIO` action can be run in `IO` as well:
```lean
def fromBaseIO (act : BaseIO α) : IO α := act
```
Behind the scenes, {name}`liftM` is inserted:
```lean (name := fromBase)
#check fun {α} (act : BaseIO α) => (act : IO α)
```
```leanOutput fromBase
fun {α} act => liftM act : {α : Type} → BaseIO α → EIO IO.Error α
```
:::
::::

:::::keepEnv
::::example "Lifting Transformed Monads"
There are also instances of {name}`MonadLift` for most of the standard library's {tech}[monad transformers], so base monad actions can be used in transformed monads without additional work.
For example, state monad actions can be lifted across reader and exception transformers, allowing compatible monads to be intermixed freely:
````lean (keep := false)
def incrBy (n : Nat) : StateM Nat Unit := modify (+ n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
````

Disabling lifting causes the code to fail to work:
````lean (name := noLift)
set_option autoLift false

def incrBy (n : Nat) : StateM Nat Unit := modify (+ n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
````

::::
:::::


Automatic lifting can be disabled by setting {option}`autoLift` to {lean}`false`.

{optionDocs autoLift}
