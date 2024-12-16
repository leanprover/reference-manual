/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Manual.Monads.Zoo.State
import Manual.Monads.Zoo.Reader
import Manual.Monads.Zoo.Except
import Manual.Monads.Zoo.Combined
import Manual.Monads.Zoo.Id
import Manual.Monads.Zoo.Option

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
-- set_option trace.SubVerso.Highlighting.Code true

#doc (Manual) "Varieties of Monads" =>


The {lean}`IO` monad has many, many effects, and is used for writing programs that need to interact with the world.
It is described in {ref "io"}[its own section].
Programs that use {lean}`IO` are essentially black boxes: they are typically not particularly amenable to verification.

Many algorithms are easiest to express with a much smaller set of effects.
These effects can often be simulated; for example, mutable state can be simulated by passing around a tuple that contains both the program's value and the state.
These simulated effects are easier to reason formally about, because they are defined using ordinary code rather than new language primitives.

The standard library provides abstractions for working with commonly-used effects.
Many frequently-used effects fall into a small number of categories:

: {deftech}[State monads] have mutable state

  Computations that have access to some data that may be modified by other parts of the computation use _mutable state_.
  State can be implemented in a variety of ways, described in the section on {ref "state-monads"}[state monads] and captured in the {name}`MonadState` type class.

: {deftech}[Reader monads] are parameterized computations

  Computations that can read the value of some parameter provided by a context exist in most programming languages, but many languages that feature state and exceptions as first-class features do not have built-in facilities for defining new parameterized computations.
  Typically, these computations are provided with a parameter value when invoked, and sometimes they can locally override it.
  Parameter values have _dynamic extent_: the value provided most recently in the call stack is the one that is used.
  They can be simulated by passing a value unchanged through a sequence of function calls; however, this technique can make code harder to read and introduces a risk that the values may be passed incorrectly to further calls by mistake.
  They can also be simulated using mutable state with a careful discipline surrounding the modification of the state.
  Monads that maintain a parameter, potentially allowing it to be overridden in a section of the call stack, are called _reader monads_.
  Reader monads are captured in the {lean}`MonadReader` type class.
  Additionally, reader monads that allow the parameter value to be locally overridden are captured in the {lean}`MonadWithReader` type class.

: {deftech}[Exception monads] have exceptions

  Computations that may terminate early with an exceptional value use _exceptions_.
  They are typically modeled with a sum type that has a constructor for ordinary termination and a constructor for early termination with errors.
  Exception monads are described in the section on {ref "exception-monads"}[exception monads], and captured in the {name}`MonadExcept` type class.


# Monad Type Classes

Using type classes like {lean}`MonadState` and {lean}`MonadExcept` allow client code to be polymorphic with respect to monads.
Together with automatic lifting, this allows programs to be re-usable in many different monads and makes them more robust to refactoring.

It's important to be aware that effects in a monad may not interact in only one way.
For example, a monad with state and exceptions may or may not roll back state changes when an exception is thrown.
If this matters for the correctness of a function, then it should use a more specific signature.

::::keepEnv
:::example "Effect Ordering"
The function {name}`sumNonFives` adds the contents of a list using a state monad, terminating early if it encounters a {lean}`5`.
```lean
def sumNonFives {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Unit := do
  for x in xs do
    if x == 5 then
      throw "Five was encountered"
    else
      modify (· + x)
```

Running it in one monad returns the state at the time that {lean}`5` was encountered:
```lean (name := exSt)
#eval
  sumNonFives (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run 0
```
```leanOutput exSt
(Except.error "Five was encountered", 10)
```

In another, the state is discarded:
```lean (name := stEx)
#eval
  sumNonFives (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run 0
```
```leanOutput stEx
Except.error "Five was encountered"
```

In the second case, an exception handler would roll back the state to its value at the start of the {keywordOf Lean.Parser.Term.termTry}`try`.
The following function is thus incorrect:
```lean
/-- Computes the sum of the non-5 prefix of a list. -/
def sumUntilFive {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Nat := do
  MonadState.set 0
  try
    sumNonFives xs
  catch _ =>
    pure ()
  get
```

In one monad, the answer is correct:
```lean (name := exSt2)
#eval
  sumUntilFive (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run' 0
```
```leanOutput exSt2
Except.ok 10
```

In the other, it is not:
```lean (name := stEx2)
#eval
  sumUntilFive (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run' 0
```
```leanOutput stEx2
Except.ok 0
```
:::
::::

A single monad may support multiple version of the same effect.
For example, there might be a mutable {lean}`Nat` and a mutable {lean}`String` or two separate reader parameters.
As long as they have different types, it should be convenient to access both.
In typical use, some monadic operations that are overloaded in type classes have type information available for {tech key:="synthesis"}[instance synthesis], while others do not.
For example, the argument passed to {name MonadState.set}`set` determines the type of the state to be used, while {name MonadState.get}`get` takes no such argument.
The type information present in applications of {name MonadState.set}`set` can be used to pick the correct instance when multiple states are available, which suggests that the type of the mutable state should be an input parameter or {tech}[semi-output parameter] so that it can be used to select instances.
The lack of type information present in uses of {name MonadState.get}`get`, on the other hand, suggests that the type of the mutable state should be an {tech}[output parameter] in {lean}`MonadState`, so type class synthesis determines the state's type from the monad itself.

This dichotomy is solved by having two versions of many of the effect type classes.
The version with a semi-output parameter has the suffix `-Of`, and its operations take types explicitly as needed.
Examples include {name}`MonadStateOf`, {name}`MonadReaderOf`, and {name}`MonadExceptOf`.
The operations with explicit type parameters have names ending in `-The`, such as {name}`getThe`, {name}`readThe`, and {name}`tryCatchThe`.
The name of the version with an output parameter is undecorated.
The standard library exports a mix of operations from the `-Of` and undecorated versions of each type class, based on what has good inference behavior in typical use cases.

:::table (header := true)
  * ignored
   * Operation
   * From Class
   * Notes
  * ignored
   * {name}`get`
   * {name}`MonadState`
   * Output parameter improves type inference
  * ignored
   * {name}`set`
   * {name}`MonadStateOf`
   * Semi-output parameter uses type information from {name}`set`'s argument
  * ignored
   * {name}`modify`
   * {name}`MonadState`
   * Output parameter is needed to allow functions without annotations
  * ignored
   * {name}`modifyGet`
   * {name}`MonadState`
   * Output parameter is needed to allow functions without annotations
  * ignored
   * {name}`read`
   * {name}`MonadReader`
   * Output parameter is needed due to lack of type information from arguments
  * ignored
   * {name}`readThe`
   * {name}`MonadReaderOf`
   * Semi-output parameter uses the provided type to guide synthesis
  * ignored
   * {name}`withReader`
   * {name}`MonadWithReader`
   * Output parameter avoids the need for type annotations on the function
  * ignored
   * {name}`withTheReader`
   * {name}`MonadWithReaderOf`
   * Semi-output parameter uses provided type to guide synthesis
  * ignored
   * {name}`throw`
   * {name}`MonadExcept`
   * Output parameter enables the use of constructor dot notation for the exception
  * ignored
   * {name}`throwThe`
   * {name}`MonadExceptOf`
   * Semi-output parameter uses provided type to guide synthesis
  * ignored
   * {name}`tryCatch`
   * {name}`MonadExcept`
   * Output parameter enables the use of constructor dot notation for the exception
  * ignored
   * {name}`tryCatchThe`
   * {name}`MonadExceptOf`
   * Semi-output parameter uses provided type to guide synthesis
:::

```lean (show := false)
example : @get = @MonadState.get := by rfl
example : @set = @MonadStateOf.set := by rfl
example (f : σ → σ) : @modify σ m inst f = @MonadState.modifyGet σ m inst PUnit fun (s : σ) => (PUnit.unit, f s) := by rfl
example : @modifyGet = @MonadState.modifyGet := by rfl
example : @read = @MonadReader.read := by rfl
example : @readThe = @MonadReaderOf.read := by rfl
example : @withReader = @MonadWithReader.withReader := by rfl
example : @withTheReader = @MonadWithReaderOf.withReader := by rfl
example : @throw = @MonadExcept.throw := by rfl
example : @throwThe = @MonadExceptOf.throw := by rfl
example : @tryCatch = @MonadExcept.tryCatch := by rfl
example : @tryCatchThe = @MonadExceptOf.tryCatch := by rfl
```

:::example "State Types"
The state monad {name}`M` has two separate states: a {lean}`Nat` and a {lean}`String`.
```lean
abbrev M := StateT Nat (StateM String)
```

Because {name}`get` is an alias for {name}`MonadState.get`, the state type is an output parameter.
This means that Lean selects a state type automatically, in this case the one from the outermost monad transformer:
```lean (name := getM)
#check (get : M _)
```
```leanOutput getM
get : M Nat
```

Only the outermost may be used, because the type of the state is an output parameter.
```lean (name := getMStr) (error := true)
#check (get : M String)
```
```leanOutput getMStr
failed to synthesize
  MonadState String M
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

Providing the state type explicitly using {name}`getThe` from {name}`MonadStateOf` allows both states to be read.
```lean (name := getTheM)
#check ((getThe String, getThe Nat) : M String × M Nat)
```
```leanOutput getTheM
(getThe String, getThe Nat) : M String × M Nat
```

Setting a state works for either type, because the state type is a {tech}[semi-output parameter] on {name}`MonadStateOf`.
```lean (name := setNat)
#check (set 4 : M Unit)
```
```leanOutput setNat
set 4 : M PUnit
```

```lean (name := setStr)
#check (set "Four" : M Unit)
```
```leanOutput setStr
set "Four" : M PUnit
```

:::


# Monad Transformers
%%%
tag := "monad-transformers"
%%%

A {deftech}_monad transformer_ is a function that, when provided with a monad, gives back a new monad.
Typically, this new monad has all the effects of the original monad along with some additional ones.

```lean (show := false)
variable {α : Type u} (T : (Type u → Type v) → Type u → Type w) (m : Type u → Type v)

```
A monad transformer consists of the following:
 * A function {lean}`T` that constructs the new monad's type from an existing monad
 * A `run` function that adapts a {lean}`T m α` into some variant of {lean}`m`, often requiring additional parameters and returning a more specific type under {lean}`m`
 * An instance of {lean}`[Monad m] → Monad (T m)` that allows the transformed monad to be used as a monad
 * An instance of {lean}`MonadLift` that allows the original monad's code to be used in the transformed monad
 * If possible, an instance of {lean}`MonadControl m (T m)` that allows actions from the transformed monad to be used in the original monad

Typically, a monad transformer also provides instances of one or more type classes that describe the effects that it introduces.
The transformer's {name}`Monad` and {name}`MonadLift` instances make it practical to write code in the transformed monad, while the type class instances allow the transformed monad to be used with polymorphic functions.

::::keepEnv
```lean (show := false)
universe u v
variable {m : Type u → Type v} {α : Type u}
```
:::example "The Identity Monad Transformer "
The identity monad transformer neither adds nor removes capabilities to the transformed monad.
Its definition is the identity function, suitably specialized:
```lean
def IdT (m : Type u → Type v) : Type u → Type v := m
```
Similarly, the {name IdT.run}`run` function requires no additional arguments and just returns an {lean}`m α`:
```lean
def IdT.run (act : IdT m α) : m α := act
```

The monad instance relies on the monad instance for the transformed monad, selecting it via {tech}[type ascriptions]:
```lean
instance [Monad m] : Monad (IdT m) where
  pure x := (pure x : m _)
  bind x f := (x >>= f : m _)
```

Because {lean}`IdT m` is definitionally equal to {lean}`m`, the {lean}`MonadLift m (IdT m)` instance doesn't need to modify the action being lifted:
```lean
instance : MonadLift m (IdT m) where
  monadLift x := x
```

The {lean}`MonadControl` instance is similarly simple.
```lean
instance [Monad m] : MonadControl m (IdT m) where
  stM α := α
  liftWith f := f (fun x => Id.run <| pure x)
  restoreM v := v
```

:::
::::

The Lean standard library provides transformer versions of many different monads, including {name}`ReaderT`, {name}`ExceptT`, and {name}`StateT`, along with variants using other representations such as {name}`StateCpsT`, {name StateRefT'}`StateRefT`, and {name}`ExceptCpsT`.
Additionally, the {name}`EStateM` monad is equivalent to combining {name}`ExceptT` and {name}`StateT`, but it can use a more specialized representation to improve performance.

{include 0 Monads.Zoo.Id}

{include 0 Monads.Zoo.State}

{include 0 Monads.Zoo.Reader}

{include 0 Monads.Zoo.Option}

{include 0 Monads.Zoo.Except}

{include 0 Monads.Zoo.Combined}
