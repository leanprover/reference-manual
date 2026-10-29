/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/

import VersoManual
import Manual.Meta

import Manual.LibLean.JSON
import Manual.LibLean.HTML

open Verso.Genre Manual InlineLean
open Lean

#doc (Manual) "Lean as a Library" =>
%%%
tag := "lean-as-a-library"
%%%

Lean is a _self-hosted_ language, in the sense that most of its implementation (parser, elaborator, compiler, the metaprogramming framework) is written in Lean itself.
These components are accessed by importing modules from the `Lean` library.

Parts of the `Lean` library may also be useful for more general programming applications.
Note that the library is evolving quickly, and does not necessarily enjoy the same level of polish or stability guarantees as the standard library `Std`.
Furthermore, it is a large library, and importing it outside the {tech}[metaprogramming phase] may substantially increase the size of compiled executables.

{include 1 Manual.LibLean.JSON}

{include 1 Manual.LibLean.HTML}
