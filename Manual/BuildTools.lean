/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake

import Manual.Meta
import Manual.BuildTools.Lake

open Manual
open Verso.Genre
open Verso.Genre.Manual


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


#doc (Manual) "Build Tools and Distribution" =>
%%%
tag := "build-tools-and-distribution"
%%%

:::paragraph
The Lean {deftech}_toolchain_ is the collection of command-line tools that are used to check proofs and compile programs in collections of Lean files.
Toolchains are managed by `elan`, which installs toolchains as needed.
Lean toolchains are designed to be self-contained, and most command-line users will never need to explicitly invoke any other than `lake` and `elan`.
The contain the following tools:

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

When using Elan, the version of each tool on the {envVar}`PATH` is a proxy that invokes the correct version.
The proxy determines the appropriate toolchain version for the current context, ensures that it is installed, and then invokes the underlying tool in the appropriate toolchain installation.
These proxies can be instructed to use a specific version by passing it as an argument prefixed with `+`, so `lake +4.0.0` invokes `lake` version `4.0.0`, after installing it if necessary.
If present, a {deftech}_toolchain file_ in a directory causes a particular version of Lean to be used in it and all subdirectories.
This file should indicate a specific version, such as `leanprover/lean4:v4.15.0`, `leanprover/lean4:v4.16.0-rc2`, or `leanprover/lean4:nightly-2025-01-19`.
If no toolchain file is present, then the `elan` configuration is used to select a version to invoke. {TODO}[Link to Elan chapter here]


In addition to these build tools, toolchains contain files that are needed to build Lean code.
This includes source code, {tech}[`.olean` files], compiled libraries, C header files, and the compiled Lean run-time system.
They also include external proof automation tools that are used by tactics included with Lean, such as `cadical` for {tactic}`bv_decide`.


{include 0 Manual.BuildTools.Lake}

# Reservoir
%%%
tag := "reservoir"
%%%


::: planned 76
 * Concepts
 * Package and toolchain versions
 * Tags and builds
:::
