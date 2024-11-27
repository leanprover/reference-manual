/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

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

{docstring IO.iterate}

# Console IO

Lean includes convenience functions for writing to {tech}[standard output] and {tech}[standard error].
All make use of {lean}`ToString` instances, and the varieties whose names end in `-ln` add a newline after the output.

{docstring IO.print}

{docstring IO.println}

{docstring IO.eprint}

{docstring IO.eprintln}

{include 0 Manual.IO.Ref}

# Files, File Handles, and Streams

Lean provides a consistent filesystem API on all supported platforms.
These are the key concepts:

: {deftech}[Files]

  Files are an abstraction provided by operating systems that provide random access to persistently-stored data, organized hierarchically into directories.

: {deftech}[Directories]

  Directories, also known as _folders_, may contain files or other directories.
  Fundamentally, a directory maps names to the files and/or directories that it contains.

: {deftech}[File Handles]

  File handles ({name IO.FS.Handle}`Handle`) are abstract references to files that have been opened for reading and/or writing.
  A file handle maintains a mode that determines whether reading and/or writing are allowed, along with a cursor that points at a specific location in the file.
  Reading from or writing to a file handle advances the cursor.
  File handles may be {deftech}[buffered], which means that reading from a file handle may not return the current contents of the persistent data, and writing to a file handle may not modify them immediately.

: Paths

  Files are primarily accessed via {deftech}_paths_ ({name}`System.FilePath`).
  A path is a sequence of directory names, potentially terminated by a file name.
  They are represented by strings in which separator characters {margin}[The current platform's separator characters are listed in {name}`System.FilePath.pathSeparators`.] delimit the names.

  The details of paths are platform-specific.
  {deftech}[Absolute paths] begin in a {deftech}_root directory_; some operating systems have a single root, while others may have multiple root directories.
  Relative paths do not begin in a root directory and require that some other directory be taken as a starting point.
  In addition to directories, paths may contain the special directory names `.`, which refers to the directory in which it is found, and `..`, which refers to prior directory in the path.

  Filenames, and thus paths, may end in one or more {deftech}_extensions_ that identify the file's type.
  Extensions are delimited by the character {name}`System.FilePath.extSeparator`.
  On some platforms, executable files have a special extension ({name}`System.FilePath.exeExtension`).

: {deftech}[Streams]

  Streams are a higher-level abstraction over files, both providing additional functionality and hiding some details of files.
  While {tech}[file handles] are essentially a thin wrapper around the operating system's representation, streams are implemented in Lean as a structure called {lean}`IO.FS.Stream`.
  Because streams are implemented in Lean, user code can create additional streams, which can be used seamlessly together with those provided in the standard library.

## Low-Level File API

At the lowest level, files are explicitly opened using {name IO.FS.Handle.mk}`Handle.mk`.
When the last reference to the handle object is dropped, the file is closed.
There is no explicit way to close a file handle other than by ensuring that there are no references.



{docstring IO.FS.Handle}

{docstring IO.FS.Handle.mk}

{docstring IO.FS.Mode}

{docstring IO.FS.Handle.read}

{docstring IO.FS.Handle.readToEnd}

{docstring IO.FS.Handle.readBinToEnd}

{docstring IO.FS.Handle.readBinToEndInto}

{docstring IO.FS.Handle.getLine}

{docstring IO.FS.Handle.write}

{docstring IO.FS.Handle.putStr}

{docstring IO.FS.Handle.putStrLn}

{docstring IO.FS.Handle.flush}

{docstring IO.FS.Handle.rewind}

{docstring IO.FS.Handle.truncate}

{docstring IO.FS.Handle.isTty}

{docstring IO.FS.Handle.lock}

{docstring IO.FS.Handle.tryLock}

{docstring IO.FS.Handle.unlock}


::::example "One File, Multiple Handles"
This program has two handles to the same file.
Because file I/O may be buffered independently for each handle, {name IO.FS.Handle.flush}`Handle.flush` should be called when the buffers need to be synchronized with the file's actual contents.
Here, the two handles proceed in lock-step through the file, with one of them a single byte ahead of the other.
The first handle is used to count the number of occurrences of `'A'`, while the second is used to replace each `'A'` with `'!'`.
The second handle is opened in {name IO.FS.Mode.readWrite}`readWrite` mode rather than {name IO.FS.Mode.write}`write` mode because opening an existing file in {name IO.FS.Mode.write}`write` mode replaces it with an empty file.
In this case, the buffers don't need to be flushed during execution because modifications occur only to parts of the file that will not be read again, but the write handle should be flushed after the loop has completed.

:::ioExample
```ioLean
open IO.FS (Handle)

def main : IO Unit := do
  IO.println s!"Starting contents: '{(← IO.FS.readFile "data").trim}'"

  let h ← Handle.mk "data" .read
  let h' ← Handle.mk "data" .readWrite
  h'.rewind

  let mut count := 0
  let mut buf : ByteArray ← h.read 1
  while ok : buf.size = 1 do
    if Char.ofUInt8 buf[0] == 'A' then
      count := count + 1
      h'.write (ByteArray.empty.push '!'.toUInt8)
    else
      h'.write buf
    buf ← h.read 1

  h'.flush

  IO.println s!"Count: {count}"
  IO.println s!"Contents: '{(← IO.FS.readFile "data").trim}'"
```

When run on this file:
```inputFile "data"
AABAABCDAB
```

the program outputs:
```stdout
Starting contents: 'AABAABCDAB'
Count: 5
Contents: '!!B!!BCD!B'
```
```stderr (show := false)
```

Afterwards, the file contains:
```outputFile "data"
!!B!!BCD!B
```

:::
::::

## Streams

{docstring IO.FS.Stream}

{docstring IO.FS.withIsolatedStreams}

{docstring IO.FS.Stream.read}

{docstring IO.FS.Stream.write}

{docstring IO.FS.Stream.flush}

{docstring IO.FS.Stream.getLine}

{docstring IO.FS.Stream.isTty}

{docstring IO.FS.Stream.ofBuffer}

{docstring IO.FS.Stream.ofHandle}

{docstring IO.FS.Stream.putStr}

{docstring IO.FS.Stream.putStrLn}

{docstring IO.FS.Stream.Buffer}

{docstring IO.FS.Stream.Buffer.data}

{docstring IO.FS.Stream.Buffer.pos}

## Paths

Paths are represented by strings.
Different platforms have different conventions for paths: some use slashes (`/`) as directory separators, others use backslashes (`\`).
Some are case-sensitive, others are not.
Different Unicode encodings and normal forms may be used to represent filenames, and some platforms consider filenames to be byte sequences rather than strings.
A string that represents an {tech}[absolute path] on one system may not even be a valid path on another system.

To write Lean code that is as compatible as possible with multiple systems, it can be helpful to use Lean's path manipulation primitives instead of raw string manipulation.
Helpers such as {name}`System.FilePath.join` take platform-specific rules for absolute paths into account, {name}`System.FilePath.pathSeparator` contains the appropriate path separator for the current platform, and {name}`System.FilePath.exeExtension` contains any necessary extension for executable files.
Avoid hard-coding these rules.

As a slight abuse of notation, there is an instance of the {lean}`Div` type class for {name System.FilePath}`FilePath` which allows the slash operator to be used to concatenate paths.

{docstring System.FilePath}

{docstring System.mkFilePath}

{docstring System.FilePath.join}

{docstring System.FilePath.normalize}

{docstring System.FilePath.isAbsolute}

{docstring System.FilePath.isRelative}

{docstring System.FilePath.parent}

{docstring System.FilePath.components}

{docstring System.FilePath.fileName}

{docstring System.FilePath.fileStem}

{docstring System.FilePath.extension}

{docstring System.FilePath.addExtension}

{docstring System.FilePath.withExtension}

{docstring System.FilePath.withFileName}

{docstring System.FilePath.pathSeparator}

{docstring System.FilePath.pathSeparators}

{docstring System.FilePath.extSeparator}

{docstring System.FilePath.exeExtension}

## Interacting with the Filesystem

Some operations on paths consult the filesystem.

{docstring IO.FS.Metadata}

{docstring System.FilePath.metadata}

{docstring System.FilePath.pathExists}

{docstring System.FilePath.isDir}

{docstring IO.FS.DirEntry}

{docstring IO.FS.DirEntry.path}

{docstring System.FilePath.readDir}

{docstring System.FilePath.walkDir}

{docstring IO.FileRight}

{docstring IO.FileRight.flags}

{docstring IO.setAccessRights}

{docstring IO.FS.removeFile}

{docstring IO.FS.rename}

{docstring IO.FS.removeDir}

{docstring IO.FS.lines}

{docstring IO.FS.withTempFile}

{docstring IO.FS.createDirAll}

{docstring IO.FS.writeBinFile}

{docstring IO.FS.withFile}

{docstring IO.FS.removeDirAll}

{docstring IO.FS.createTempFile}

{docstring IO.FS.readFile}

{docstring IO.FS.realPath}

{docstring IO.FS.writeFile}

{docstring IO.FS.readBinFile}

{docstring IO.FS.createDir}

## Standard I/O

On operating systems that are derived from or inspired by Unix, {deftech}_standard input_, {deftech}_standard output_, and {deftech}_standard error_ are the names of three streams that are available in each process.
Generally, programs are expected to read from standard input, write ordinary output to the standard output, and error messages to the standard error.
By default, standard input receives input from the console, while standard output and standard error output to the console, but all three are often redirected to or from pipes or files.

Rather than providing direct access to the operating system's standard I/O facilities, Lean wraps them in {name IO.FS.Stream}`Stream`s.
Additionally, the {lean}`IO` monad contains special support for replacing or locally overriding them.
This extra level of indirection makes it possible to redirect input and output within a Lean program.


{docstring IO.getStdin}

::::example "Reading from Standard Input"
In this example, {lean}`IO.getStdin` and {lean}`IO.getStdout` are used to get the current standard input and output, respectively.
These can be read from and written to.

:::ioExample
```ioLean
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "Who is it?"
  let name ← stdin.getLine
  stdout.putStr "Hello, "
  stdout.putStrLn name
```

With this standard input:
```stdin
Lean user
```
the standard output is:
```stdout
Who is it?
Hello, Lean user
```
:::
::::

{docstring IO.setStdin}

{docstring IO.withStdin}

{docstring IO.getStdout}

{docstring IO.setStdout}

{docstring IO.withStdout}

{docstring IO.getStderr}

{docstring IO.setStderr}

{docstring IO.withStderr}

{docstring IO.FS.withIsolatedStreams}

::::keepEnv
:::example "Redirecting Standard I/O to Strings"
The {lean}`countdown` function counts down from a specified number, writing its progress to standard output.
Using `IO.FS.withIsolatedStreams`, this output can be redirected to a string.

```lean (name := countdown)
def countdown : Nat → IO Unit
  | 0 =>
    IO.println "Blastoff!"
  | n + 1 => do
    IO.println s!"{n + 1}"
    countdown n

def runCountdown : IO String := do
  let (output, ()) ← IO.FS.withIsolatedStreams (countdown 10)
  return output

#eval runCountdown
```

Running {lean}`countdown` yields a string that contains the output:
```leanOutput countdown
"10\n9\n8\n7\n6\n5\n4\n3\n2\n1\nBlastoff!\n"
```
:::
::::

## Files and Directories

{docstring IO.currentDir}

{docstring IO.appPath}

{docstring IO.appDir}

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
