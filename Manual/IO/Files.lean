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

#doc (Manual) "Files, File Handles, and Streams" =>

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

# Low-Level File API

At the lowest level, files are explicitly opened using {name IO.FS.Handle.mk}`Handle.mk`.
When the last reference to the handle object is dropped, the file is closed.
There is no explicit way to close a file handle other than by ensuring that there are no references to it.


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

# Streams

{docstring IO.FS.Stream}

{docstring IO.FS.withIsolatedStreams}

{docstring IO.FS.Stream.ofBuffer}

{docstring IO.FS.Stream.ofHandle}

{docstring IO.FS.Stream.putStrLn}

{docstring IO.FS.Stream.Buffer}

{docstring IO.FS.Stream.Buffer.data}

{docstring IO.FS.Stream.Buffer.pos}

# Paths

Paths are represented by strings.
Different platforms have different conventions for paths: some use slashes (`/`) as directory separators, others use backslashes (`\`).
Some are case-sensitive, others are not.
Different Unicode encodings and normal forms may be used to represent filenames, and some platforms consider filenames to be byte sequences rather than strings.
A string that represents an {tech}[absolute path] on one system may not even be a valid path on another system.

To write Lean code that is as compatible as possible with multiple systems, it can be helpful to use Lean's path manipulation primitives instead of raw string manipulation.
Helpers such as {name}`System.FilePath.join` take platform-specific rules for absolute paths into account, {name}`System.FilePath.pathSeparator` contains the appropriate path separator for the current platform, and {name}`System.FilePath.exeExtension` contains any necessary extension for executable files.
Avoid hard-coding these rules.

There is an instance of the {lean}`Div` type class for {name System.FilePath}`FilePath` which allows the slash operator to be used to concatenate paths.

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

# Interacting with the Filesystem

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

# Standard I/O
%%%
tag := "stdio"
%%%

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

# Files and Directories

{docstring IO.currentDir}

{docstring IO.appPath}

{docstring IO.appDir}
