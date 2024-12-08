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

{tech key:="lift"}[Lifting] between monads is reflexive and transitive:
 * Any monad can run its own actions.
 * Lifts from {lean}`m` to {lean}`m'` and from {lean}`m'` to {lean}`n` can be composed to yield a lift from {lean}`m` to {lean}`n`.
The utility type class {name}`MonadLiftT` constructs lifts via the reflexive and transitive closure of {name}`MonadLift` instances.
Users should not define new instances of {name}`MonadLiftT`, but it is useful as an instance implicit parameter to a polymorphic function that needs to run actions from multiple monads in some user-provided monad.

{docstring MonadLiftT}

:::example "Monad Lifts in Function Signatures"
The function {name}`IO.withStdin` has the following signature:
```signature
IO.withStdin.{u} {m : Type → Type u} {α : Type}
  [Monad m] [MonadFinally m] [MonadLiftT BaseIO m]
  (h : IO.FS.Stream) (x : m α) :
  m α
```
Because it doesn't require its parameter to precisely be in {name}`IO`, it can be used in many monads, and the body does not need to restrict itself to {name}`IO`.
The instance implicit parameter {lean}`MonadLiftT BaseIO m` allows the reflexive transitive closure of {name}`MonadLift` to be used to assemble the lift.
:::


When a term of type {lean}`n β` is expected, but the provided term has type {lean}`m α`, and the two types are not definitionally equal, Lean attempts to insert lifts and coercions before reporting an error.
There are the following possibilities:
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

# Reversing Lifts

```lean (show := false)
variable {m n : Type u → Type v} {α ε : Type u}
```

Monad lifting is not always sufficient to combine monads.
Many operations provided by monads are higher order, taking an action _in the same monad_ as a parameter.
Even if these operations are lifted to some more powerful monad, their arguments are still restricted to the original monad.

There are two type classes that support this kind of “reverse lifting”: {name}`MonadFunctor` and {name}`MonadControl`.
An instance of {lean}`MonadFunctor m n` explains how to interpret a fully-polymorphic function in {lean}`m` into {lean}`n`.
This polymorphic function must work for _all_ types {lean}`α`: it has type {lean}`{α : Type u} → m α → m α`.
Such a function can be thought of as one that may have effects, but can't do so based on specific values that are provided.
An instance of {lean}`MonadControl m n` explains how to interpret an arbitrary action from {lean}`m` into {lean}`n`, while at the same time providing a “reverse interpreter” that allows the {lean}`m` action to run {lean}`n` actions.

## Monad Functors

{docstring MonadFunctor}

{docstring MonadFunctorT}

## Reversible Lifting with `MonadControl`

{docstring MonadControl}

{docstring MonadControlT}

{docstring control}

{docstring controlAt}


::::keepEnv
:::example "Exceptions and Lifting"
One example is {name}`Except.tryCatch`:
```signature
Except.tryCatch.{u, v} {ε : Type u} {α : Type v}
  (ma : Except ε α) (handle : ε → Except ε α) :
  Except ε α
```
Both of its parameters are in {lean}`Except ε`.
{name}`MonadLift` can lift the entire application of the handler.
The function {lean}`getBytes`, which extracts the single bytes from an array of {lean}`Nat`s using state and exceptions, is written without {keywordOf Lean.Parser.Term.do}`do`-notation or automatic lifting in order to make its structure explicit.
```lean
set_option autoLift false

def getByte (n : Nat) : Except String UInt8 :=
  if n < 256 then
    pure n.toUInt8
  else throw s!"Out of range: {n}"

def getBytes (input : Array Nat) : StateT (Array UInt8) (Except String) Unit := do
  input.forM fun i =>
    liftM (Except.tryCatch (some <$> getByte i) fun _ => pure none) >>=
      fun
        | some b => modify (·.push b)
        | none => pure ()
```

```lean (name := getBytesEval1)
#eval getBytes #[1, 58, 255, 300, 2, 1000000] |>.run #[] |>.map (·.2)
```
```leanOutput getBytesEval1
Except.ok #[1, 58, 255, 2]
```
{name}`getBytes` uses an `Option` returned from the lifted action to signal the desired state updates.
This quickly becomes unwieldy if there are more possible ways to react to the inner action, such as saving handled exceptions.
Ideally, state updates would be performed within the {name}`tryCatch` call directly.


Attempting to save bytes and handled exceptions does not work, however, because the arguments to {name}`Except.tryCatch` have type {lean}`Except String Unit`:
```lean (error := true) (name := getBytesErr) (keep := false)
def getBytes' (input : Array Nat) : StateT (Array String) (StateT (Array UInt8) (Except String)) Unit := do
  input.forM fun i =>
    liftM
      (Except.tryCatch
        (getByte i >>= fun b =>
         modifyThe (Array UInt8) (·.push b))
        fun e =>
          modifyThe (Array String) (·.push e))
```
```leanOutput getBytesErr
failed to synthesize
  MonadStateOf (Array String) (Except String)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

Because {name}`StateT` has a {name}`MonadControl` instance, {name}`control` can be used instead of {name}`liftM`.
It provides the inner action with an interpreter for the outer monad.
In the case of {name}`StateT`, this interpreter expects that the inner monad returns a tuple that includes the updated state, and takes care of providing the initial state and extracting the updated state from the tuple.

```lean
def getBytes' (input : Array Nat) : StateT (Array String) (StateT (Array UInt8) (Except String)) Unit := do
  input.forM fun i =>
    control fun run =>
      (Except.tryCatch
        (getByte i >>= fun b =>
         run (modifyThe (Array UInt8) (·.push b))))
        fun e =>
          run (modifyThe (Array String) (·.push e))
```

```lean (name := getBytesEval2)
#eval
  getBytes' #[1, 58, 255, 300, 2, 1000000]
  |>.run #[] |>.run #[]
  |>.map (fun (((), bytes), errs) => (bytes, errs))
```
```leanOutput getBytesEval2
Except.ok (#["Out of range: 300", "Out of range: 1000000"], #[1, 58, 255, 2])
```
:::
::::
