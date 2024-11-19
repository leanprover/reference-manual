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

{docstring IO.FS.Stream}

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
