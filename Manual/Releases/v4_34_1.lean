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

#doc (Manual) "Lean 4.34.1 (2026-09-24)" =>
%%%
tag := "release-v4.34.1"
file := "v4.34.1"
%%%

This patch release contains multiple runtime fixes,
and we encourage all users of v4.34.0 or earlier to upgrade to it.

For this release, 3 changes landed.
In addition to the 0 feature additions
and 3 fixes listed below,
there were 0 refactoring changes,
0 documentation improvements,
0 performance improvements,
0 improvements to the test suite,
and 0 other changes.

# Compiler

```markdown

- [#15289](https://github.com/leanprover/lean4/pull/15289)
  makes maximal sharing, including the kernel's sharing of every theorem it checks, panic when a shared subterm gains more than `INT_MAX` references, instead of eventually freeing the subterm while it is still referenced. On inputs north of 100GB, the possibility of triggering undefined behavior in the official kernel this way, which could be extended into a proof of False, could not be excluded. Other kernels such as nanoda or con-leche not based on the Lean runtime or not making use of this specific function were not affected.

- [#15288](https://github.com/leanprover/lean4/pull/15288)
  fixes potential undefined behavior when an object with a huge number of incoming references is shared between threads. The official kernel does not use multithreading in its default configuration (as used by comparator and `lake check/compare`), but other Lean-based checkers such as con-leche might be affected.

- [#15241](https://github.com/leanprover/lean4/pull/15241)
  prevents deletion cascades from releasing objects whose reference count has been frozen after over- or underflow. Like #14838, on machines with at least 18GB of free RAM, it could potentially be used to trigger use-after-free in the official kernel, which could be extended into a proof of False. Other kernels such as nanoda or con-ron not based on the Lean runtime were not affected.

```
