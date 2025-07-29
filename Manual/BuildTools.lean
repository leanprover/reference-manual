/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command

import Manual.Meta
import Manual.BuildTools.Lake
import Manual.BuildTools.Elan

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


#doc (Manual) "Build Tools and Distribution" =>
%%%
tag := "build-tools-and-distribution"
shortContextTitle := "Build Tools"
%%%

:::paragraph
The Lean {deftech}_toolchain_ is the collection of command-line tools that are used to check proofs and compile programs in collections of Lean files.
Toolchains are managed by `elan`, which installs toolchains as needed.
Lean toolchains are designed to be self-contained, and most command-line users will never need to explicitly invoke any other than `lake` and `elan`.
They contain the following tools:

: `lean`

  The Lean compiler, used to elaborate and compile a Lean source file.

: `lake`

  The Lean build tool, used to invoke incrementally invoke `lean` and other tools while tracking dependencies.

: `leanc`

  The C compiler that ships with Lean, which is a version of [Clang](https://clang.llvm.org/).

: `leanmake`

  An implementation of the `make` build tool, used for compiling C dependencies.

: `leanchecker`

  A tool that replays elaboration results from {tech}[`.olean` files] through the Lean kernel, providing additional assurance that all terms were properly checked.
:::

In addition to these build tools, toolchains contain files that are needed to build Lean code.
This includes source code, {tech}[`.olean` files], compiled libraries, C header files, and the compiled Lean run-time system.
They also include external proof automation tools that are used by tactics included with Lean, such as `cadical` for {tactic}`bv_decide`.


{include 0 Manual.BuildTools.Lake}

{include 0 Manual.BuildTools.Elan}

# Reservoir
%%%
tag := "reservoir"
draft := true
%%%


::: planned 76
 * Concepts
 * Package and toolchain versions
 * Tags and builds
:::
