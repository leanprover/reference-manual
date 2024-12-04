/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Manual.Monads.Syntax
import Manual.Monads.Zoo
import Manual.Monads.Lift
import Manual.Monads.API
import Manual.Monads.Laws

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false
set_option maxRecDepth 1024

#doc (Manual) "Functors, Monads and `do`-Notation" =>

%%%
tag := "monads-and-do"
%%%

:::planned 102
This chapter will describe `do`-notation in Lean:
 * Overview of {deftech}[monads]
 * Desugaring of `do` and its associated control structures
 * Comprehensive description of the syntax of `do`-notation
 * Definition of being in the "same `do`-block"
 * Various common kinds of monads, including reader monads, {deftech}[state monads], and {deftech}[exception monads].
:::

The type classes {name}`Functor`, {name}`Applicative`, and {name}`Monad` provide fundamental tools for functional programming.{margin}[An introduction to programming with these abstractions is available in [_Functional Programming in Lean_](https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad.html).]
While they are inspired by the concepts of functors and monads in category theory, the versions used for programming are more limited.
The type classes in Lean's standard library represent the concepts as used for programming, rather than the general mathematical definition.

Instances of {name}`Functor` allow an operation to be applied consistently throughout some polymorphic context.
Examples include transforming each element of a list by applying a function and creating new {lean}`IO` actions by arranging for a pure function to be applied to the result of an existing {lean}`IO` action.
Instances of {name}`Monad` allow side effects with data dependencies to be encoded; examples include using a tuple to simulate mutable state, a sum type to simulate exceptions, and representing actual side effects with {lean}`IO`.
{name}`Applicative` occupies a middle ground: like monads, they allow functions computed with effects to be applied to arguments that are computed with effects, but they do not allow sequential dependencies where the output of an effect forms an input into another effectful operation.

The additional type classes {name}`Pure`, {name}`Bind`, {name}`SeqLeft`, {name}`SeqRight`, and {name}`Seq` capture individual operations from {name}`Applicative` and {name}`Monad`, allowing them to be overloaded and used with types that are not necessarily {name}`Applicative` functors or {name}`Monad`s.


{docstring Functor}

{docstring Pure}

{docstring Seq}

{docstring SeqLeft}

{docstring SeqRight}

{docstring Applicative}


:::::keepEnv

```lean (show := false)
section
variable {α : Type u} {β : Type u}
variable {n : Nat}
```

::::example "Lists with Lengths as Applicative Functors"

The structure {name}`LenList` pairs a list with a proof that it has the desired length.
As a consequence, its `zipWith` operator doesn't require a fallback in case the lengths of its inputs differ.

```lean
structure LenList (length : Nat) (α : Type u) where
  list : List α
  lengthOk : list.length = length

def LenList.head (xs : LenList (n + 1) α) : α :=
  xs.list.head <| by
    intro h
    cases xs
    simp_all [List.length]
    subst_eqs

def LenList.tail (xs : LenList (n + 1) α) : LenList n α :=
  match xs with
  | ⟨_ :: xs', _⟩ => ⟨xs', by simp_all⟩

def LenList.map (f : α → β) (xs : LenList n α) : LenList n β where
  list := xs.list.map f
  lengthOk := by
    cases xs
    simp [List.length_map, *]

def LenList.zipWith (f : α → β → γ)
    (xs : LenList n α) (ys : LenList n β) :
    LenList n γ where
  list := xs.list.zipWith f ys.list
  lengthOk := by
    cases xs; cases ys
    simp [List.length_zipWith, *]
```

The well-behaved {name}`Applicative` instance applies functions to arguments element-wise.
Because {name}`Applicative` extends {name}`Functor`, a separate {name}`Functor` instance is not necessary, and {name Functor.map}`map` can be defined as part of the {name}`Applicative` instance.

```lean
instance : Applicative (LenList n) where
  map := LenList.map
  pure x := {
    list := List.replicate n x
    lengthOk := List.length_replicate _ _
  }
  seq fs xs := fs.zipWith (· ·) (xs ())
```

The well-behaved {name}`Monad` instance takes the diagonal of the results of applying the function:

```lean
@[simp]
theorem LenList.list_length_eq (xs : LenList n α) : xs.list.length = n := by
  cases xs
  simp [*]

def LenList.diagonal (square : LenList n (LenList n α)) : LenList n α :=
  match n with
  | 0 => ⟨[], rfl⟩
  | n' + 1 => {
    list := square.head.head :: (square.tail.map (·.tail)).diagonal.list,
    lengthOk := by simp
  }
```

```lean (show := false)
end
```
::::
:::::


{docstring Alternative}

{docstring Bind}

{docstring Monad}

{include 0 Manual.Monads.Laws}

{include 0 Manual.Monads.Lift}

{include 0 Manual.Monads.Syntax}

{include 0 Manual.Monads.API}

# Varieties of Monads

The {lean}`IO` monad has many, many effects, and is used for writing programs that need to interact with the world.
It is described in {ref "io"}[its own section].
Programs that use {lean}`IO` are essentially black boxes: they are typically not particularly amenable to verification.

Many algorithms are easiest to express with a much smaller set of effects.
These effects can often be simulated; for example, mutable state can be simulated by passing around a tuple that contains both the program's value and the state.
These simulated effects are easier to reason formally about, because they are defined using ordinary code rather than new language primitives.

The standard library provides abstractions for working with commonly-used effects.
Many frequently-used effects fall into a small number of categories:

: State monads have mutable state

  Computations that have access to some data that may be modified by other parts of the computation use _mutable state_.
  State can be implemented in a variety of ways, described in the section on {ref "state-monads"}[state monads] and captured in the {name}`MonadState` type class.

: Reader monads are parameterized computations

  Computations that can read the value of some parameter provided by a context exist in most programming languages, but many languages that feature state and exceptions as first-class features do not have built-in facilities for defining new parameterized computations.
  Typically, these computations are provided with a parameter value when invoked, and sometimes they can locally override it.
  Parameter values have _dynamic extent_: the value provided most recently in the call stack is the one that is used.
  They can be simulated by passing a value unchanged through a sequence of function calls; however, this technique can make code harder to read and introduces a risk that the values may be passed incorrectly to further calls by mistake.
  They can also be simulated using mutable state with a careful discipline surrounding the modification of the state.
  Monads that maintain a parameter, potentially allowing it to be overridden in a section of the call stack, are called _reader monads_.
  Reader monads are captured in the {lean}`MonadReader` type class.
  Additionally, reader monads that allow the parameter value to be locally overridden are captured in the {lean}`MonadWithReader` type class.

: Exception monads have exceptions

  Computations that may terminate early with an exceptional value use _exceptions_.
  They are typically modeled with a sum type that has a constructor for ordinary termination and a constructor for early termination with errors.
  Exception monads are described in the section on {ref "exception-monads"}[exception monads], and captured in the {name}`MonadExcept` type class.


## Monad Type Classes

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


## Monad Transformers

A {deftech}_monad transformer_ is a function that, when provided with a monad, gives back a new monad.
Typically, this new monad has all the effects of the original monad along with some additional ones.

```lean (show := false)
variable (T : (Type u → Type v) → Type u → Type w) (m : Type u → Type v)
```
A monad transformer consists of the following:
 * A function {lean}`T` that constructs the new monad's type from an existing monad
 * An instance of {lean}`[Monad m] → Monad (T m)` that allows the transformed monad to be used as a monad
 * An instance of {lean}`MonadLift` that allows the original monad's code to be used in the transformed monad

The Lean standard library provides transformer versions of many different monads, including {name}`ReaderT`, {name}`ExceptT`, and {name}`StateT`, variants using other representations such as {name}`StateCpsT`, {name StateRefT'}`StateRefT`, and {name}`ExceptCpsT`.
Additionally, the {name}`EStateM` monad is equivalent to combining {name}`ExceptT` and {name}`StateT`, but it can use a more specialized representation to improve performance.

{include 2 Monads.Zoo.Id}

{include 2 Monads.Zoo.State}

{include 2 Monads.Zoo.Reader}

{include 2 Monads.Zoo.Except}

{include 2 Monads.Zoo.Control}

{include 2 Monads.Zoo.Combined}
