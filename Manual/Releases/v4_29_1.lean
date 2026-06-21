/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.29.1 (2026-04-14)" =>
%%%
tag := "release-v4.29.1"
file := "v4.29.1"
%%%

For this release, 1 change landed.
In addition to the 0 feature additions,
and 1 fix listed below,
there were 0 refactoring changes,
0 documentation improvements,
0 performance improvements,
0 improvements to the test suite,
and 0 other changes.

# Compiler

```markdown

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  fixes a heap buffer overflow in `lean_io_prim_handle_read` that was triggered through an
  integer overflow in the size computation of an allocation. In addition it places several checked
  arithmetic operations on all relevant allocation paths to have potential future overflows be turned
  into crashes instead. The offending code now throws an out of memory error instead.

```
