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

#doc (Manual) "IO" =>
%%%
tag := "io"
%%%



:::ioExample
```ioLean
def main : IO Unit :=
  IO.println "Hello, world!"
```
```stdout
Hello, world!
```
```stderr

```
:::

```exampleFile input "foo"
hey
you
```


# Logical Model

## The `IO`, `EIO` and `BaseIO` Monads

{docstring IO}

{docstring EIO}

{docstring BaseIO}

::: TODO
 * The real world
 * {name}`EIO`, {name}`BaseIO`, {name}`IO`
:::

## Errors and Error Handling

# Console IO

{docstring IO.print}

{docstring IO.println}

{docstring IO.eprint}

{docstring IO.eprintln}

# Mutable References

{docstring IO.mkRef}

# Files, File Handles, and Streams

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
  Absolute paths begin in a {deftech}_root directory_; some operating systems have a single root, while others may have multiple root directories.
  Relative paths do not begin in a root directory and require that some other directory be taken as a starting point.
  In addition to directories, paths may contain the special directory names `.`, which refers to the directory in which it is found, and `..`, which refers to prior directory in the path.

  Filenames, and thus paths, may end in one or more {deftech}_extensions_ that identify the file's type.
  Extensions are delimited by the character {name}`System.FilePath.extSeparator`.
  On some platforms, executable files have a special extension ({name}`System.FilePath.exeExtension`).

## Low-Level File API

At the lowest level, files are explicitly opened using {name IO.FS.Handle.mk}`Handle.mk`.
When the last reference to the handle object is dropped, the file is closed.
There is no explicit way to close a file handle other than

{docstring IO.FS.Mode}

{docstring IO.FS.Handle}

{docstring IO.FS.Handle.mk}

{docstring IO.FS.Handle.isTty}

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

{docstring IO.FS.Handle.lock}

{docstring IO.FS.Handle.tryLock}

{docstring IO.FS.Handle.unlock}

{docstring IO.FS.Stream}

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

## Paths

:::TODO
Platform concerns
:::

{docstring System.FilePath}

{docstring System.mkFilePath}

{docstring System.FilePath.join}

{docstring System.FilePath.normalize}

{docstring System.FilePath.isAbsolute}

{docstring System.FilePath.isRelative}

{docstring System.FilePath.parent}

{docstring System.FilePath.pathExists}

{docstring System.FilePath.isDir}

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

{docstring System.FilePath.metadata}

{docstring System.FilePath.readDir}

{docstring System.FilePath.walkDir}



## Standard IO

::: TODO

 * How to get `stdin`/`stdout`, and how to locally override them
 * What's going on here? Why do these operations exist?
:::

{docstring IO.getStdin}

{docstring IO.setStdin}

{docstring IO.withStdin}

{docstring IO.getStdout}

{docstring IO.setStdout}

{docstring IO.withStdout}

{docstring IO.getStderr}

{docstring IO.setStderr}

{docstring IO.withStderr}

## Files and Directories

{docstring IO.currentDir}

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

# Tasks and Threads
