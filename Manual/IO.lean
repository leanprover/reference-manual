/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

import Manual.IO.Console
import Manual.IO.Files
import Manual.IO.Threads
import Manual.IO.Ref

open Manual
open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "IO" =>
%%%
tag := "io"
%%%

# Logical Model

Lean is a pure functional programming language.
While Lean code is ordinarily strictly evaluated,{TODO}[xref to evaluation order] the order of evaluation that is used during type checking, especially while checking {tech}[definitional equality], is formally unspecified and makes use of a number of heuristics that improve performance but are subject to change.
This means that simply adding operations that perform side effects (such as file I/O, exceptions, or mutable references) would lead to programs in which the order of effects is unspecified.
During type checking, even terms with free variables are reduced; this would make side effects even more difficult to predict.

Conceptually, Lean distinguishes evaluation or reduction of terms from _execution_ of side effects.
Term reduction is specified by rules such as {tech}[β] and {tech}[δ], which may occur anywhere at any time.
Side effects, which must be executed in the correct order, are abstractly described in Lean's logic.
When programs are run, the Lean runtime system is responsible for actually carrying out the described effects.

```lean (show := false)
section Model
/-- A type -/
axiom α : Type
```

The type {lean}`IO α` is a description of a process that, by performing side effects, should either return a value of type {lean}`α` or throw an error.
It can be thought of as a {TODO}[xref]state monad, in which the state is the entire world.
Just as a value of type {lean}`StateM Nat Bool` computes a {lean}`Bool` while having the ability to mutate a natural number, a value of type {lean}`IO Bool` computes a {lean}`Bool` while potentially changing the world.
Error handling is accomplished by layering an appropriate exception monad transformer on top of this.

Because the entire world can't be represented in memory, the actual implementation uses an abstract token that stands for its state.
The Lean runtime system is responsible for providing the initial token when the program is run, and each primitive action accepts a token that represents the world and returns another when finished.
This ensures that effects occur in the proper order, and it clearly separates the execution of side effects from the reduction semantics of Lean terms.

```lean (show := false)
end Model
```

Non-termination via general recursion is treated separately from the effects described by {name}`IO`. {TODO}[xref]

A very important property of {lean}`IO` is that there is no way for values to “escape”.
Without using one of a few clearly-marked unsafe operators, programs have no way to extract a pure {lean}`Nat` from an {lean}`IO Nat`.
This ensures that the correct ordering of side effects is preserved, and it ensures that programs that have side effects are clearly marked as such.

## The `IO`, `EIO` and `BaseIO` Monads

There are two monads that are typically used for programs that interact with the real world:

 * Actions in {lean}`IO` may throw exceptions of type {lean}`IO.Error` or modify the world.
 * Actions in {lean}`BaseIO` can't throw exceptions, but they can modify the world.

The distinction makes it possible to tell whether exceptions are possible by looking at an action's type signature.
{lean}`BaseIO` actions are automatically promoted to {lean}`IO` as necessary.

{docstring IO}

{docstring BaseIO}

Both {lean}`IO` and {lean}`BaseIO` are instances of {lean}`EIO`, in which the type of errors is a parameter.
{lean}`IO` is defined as {lean}`EIO IO.Error`, while {lean}`BaseIO` is defined as {lean}`EIO Empty`.
In some circumstances, such as bindings to non-Lean libraries, it can be convenient to use {lean}`EIO` with a custom error type, which ensures that errors are handled at the boundaries between these and other {lean}`IO` actions.

```lean (show := false)
-- Check claim in preceding paragraph
example : IO = EIO IO.Error := rfl
example : BaseIO = EIO Empty := rfl
```

{docstring EIO}

{docstring IO.toEIO}

{docstring EIO.toIO}

{docstring EIO.toIO'}

{docstring EIO.toBaseIO}

{docstring IO.lazyPure}


## Errors and Error Handling

Error handling in the {lean}`IO` monad uses the same facilities as any other exception monad.{TODO}[xref]
In particular, throwing and catching exceptions uses the methods of the {name}`MonadExceptOf` {tech}[type class].
The exceptions thrown in {lean}`IO` have the type {lean}`IO.Error`.
The constructors of this type represent the low-level errors that occur on most operating systems, such as files not existing.
The most-used constructor is {name IO.Error.userError}`userError`, which covers all other cases and includes a string that describes the problem.

{docstring IO.Error}

{docstring IO.Error.toString}

{docstring IO.ofExcept}

{docstring EIO.catchExceptions}

{docstring IO.userError}

::::example "Throwing and Catching Errors"
:::ioExample

This program repeatedly demands a password, using exceptions for control flow.
The syntax used for exceptions is available in all exception monads, not just {lean}`IO`.
When an incorrect password is provided, an exception is thrown, which is caught by the loop that repeats the password check.
A correct password allows control to proceed past the check, terminating the loop, and any other exceptions are re-thrown.

```ioLean
def accessControl : IO Unit := do
  IO.println "What is the password?"
  let password ← (← IO.getStdin).getLine
  if password.trim != "secret" then
    throw (.userError "Incorrect password")
  else return

def repeatAccessControl : IO Unit := do
  repeat
    try
      accessControl
      break
    catch
      | .userError "Incorrect password" =>
        continue
      | other =>
        throw other

def main : IO Unit := do
  repeatAccessControl
  IO.println "Access granted!"
```

When run with this input:
```stdin
publicinfo
secondtry
secret
```

the program emits:
```stdout
What is the password?
What is the password?
What is the password?
Access granted!
```
:::
::::

### Constructing IO Errors

{docstring IO.Error.mkUnsupportedOperation}

{docstring IO.Error.mkUnsatisfiedConstraints}

{docstring IO.Error.mkProtocolError}

{docstring IO.Error.mkResourceBusy}

{docstring IO.Error.mkResourceVanished}

{docstring IO.Error.mkNoSuchThing}

{docstring IO.Error.mkNoSuchThingFile}

{docstring IO.Error.mkEofError}

{docstring IO.Error.mkPermissionDenied}

{docstring IO.Error.mkNoFileOrDirectory}

{docstring IO.Error.mkTimeExpired}

{docstring IO.Error.fopenErrorToString}

{docstring IO.Error.mkAlreadyExists}

{docstring IO.Error.mkInvalidArgument}

{docstring IO.Error.mkHardwareFault}

{docstring IO.Error.mkResourceExhausted}

{docstring IO.Error.mkInappropriateType}

{docstring IO.Error.mkOtherError}

{docstring IO.Error.otherErrorToString}

{docstring IO.Error.mkInvalidArgumentFile}

{docstring IO.Error.mkResourceExhaustedFile}

{docstring IO.Error.mkAlreadyExistsFile}


{docstring IO.Error.mkIllegalOperation}

{docstring IO.Error.mkPermissionDeniedFile}

{docstring IO.Error.mkInterrupted}

{docstring IO.Error.mkInappropriateTypeFile}

# Control Structures

Normally, programs written in {lean}`IO` use {ref "monads-and-do"}[the same control structures as those written in other monads].
There is one specific {lean}`IO` helper.

{docstring IO.iterate}

{include 0 Manual.IO.Console}

{include 0 Manual.IO.Ref}

{include 0 Manual.IO.Files}

# Environment Variables

{docstring IO.getEnv}

# Timing

{docstring IO.sleep}

{docstring IO.monoNanosNow}

{docstring IO.monoMsNow}

{docstring IO.getNumHeartbeats}

{docstring IO.addHeartbeats}

# Processes

## Current Process

{docstring IO.Process.getCurrentDir}

{docstring IO.Process.setCurrentDir}

{docstring IO.Process.exit}

{docstring IO.Process.getPID}

## Running Processes

::: TODO

 * How to run a program in batch mode
 * How to run a program interactively

:::

{docstring IO.Process.SpawnArgs}

{docstring IO.Process.StdioConfig}

{docstring IO.Process.Stdio}

{docstring IO.Process.Stdio.toHandleType}

{docstring IO.Process.Child}

{docstring IO.Process.Child.wait}

{docstring IO.Process.Child.tryWait}

{docstring IO.Process.Child.kill}

{docstring IO.Process.Child.takeStdin}

{docstring IO.Process.Output}

{docstring IO.Process.run}

{docstring IO.Process.spawn}

{docstring IO.Process.output}


# Random Numbers

{docstring IO.setRandSeed}

{docstring IO.rand}

{docstring randBool}

{docstring randNat}

## Random Generators

{docstring RandomGen}

{docstring StdGen}

{docstring stdRange}

{docstring stdNext}

{docstring stdSplit}

{docstring mkStdGen}

## System Randomness

{docstring IO.getRandomBytes}

{include 0 Manual.IO.Threads}
