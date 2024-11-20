/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual hiding «example»
open Verso.Genre
open Verso.Genre.Manual
open Lean.Parser.Command (declModifiers «example»)

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "IO" =>

%%%
tag := "io"
%%%

# Logical Model

## The `EIO` and `IO` Monads

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

::: TODO
 * Reading and writing files
 * How to close a file handle
 * Temporary files
:::

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

## Paths

{docstring System.FilePath}

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

::: TODO

 * How to run a program in batch mode
 * How to run a program interactively
:::

## Current Process

{docstring IO.Process.getCurrentDir}

{docstring IO.Process.setCurrentDir}

{docstring IO.Process.exit}

{docstring IO.Process.getPID}

## Running Processes

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
