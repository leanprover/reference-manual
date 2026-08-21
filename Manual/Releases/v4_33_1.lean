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

#doc (Manual) "Lean 4.33.1 (2026-08-21)" =>
%%%
tag := "release-v4.33.1"
file := "v4.33.1"
%%%

This patch release contains runtime and kernel fixes, and we encourage all users of `v4.33.0` or earlier to upgrade to it.

For this release, 11 changes landed.
In addition to the 2 feature additions
and 7 fixes listed below,
there were 0 refactoring changes,
0 documentation improvements,
1 performance improvement,
1 improvement to the test suite,
and 0 other changes.

# Language

````markdown

- [#14582](https://github.com/leanprover/lean4/pull/14582)
  makes the kernel reject inductive declarations in which a datatype being declared occurs applied to anything other than the parameters and universe levels of the declaration. Such non-uniform occurrences could previously hide in positions that escape the kernel's checks: behind a reduction that erases them, or in the parametric arguments of a nested occurrence, which are dropped from the auxiliary declaration the kernel generates and were therefore only checked for well-typedness.

````

# Compiler

````markdown

- [#14838](https://github.com/leanprover/lean4/pull/14838)
  prevents memory corruption when an object's 32-bit reference count overflows. On machines with at least 18GB of free RAM, it could be used to trigger use-after-free in the official kernel, which could be extended into a proof of False. Other kernels such as nanoda not based on the Lean runtime were not affected.

````

# Other

````markdown

- [#14833](https://github.com/leanprover/lean4/pull/14833)
  makes Lean require GMP 6.3.0 or newer and builds the official releases against GMP 6.3.0. Earlier GMP versions contain bugs that can cause Lean to produce unsound (i.e., incorrect) results in corner cases; independent kernels that do not depend on GMP will catch such unsoundness. The portable Linux releases were previously linked against GMP 6.1.2 (inherited from the old glibc nixpkgs used for portability).

- [#14849](https://github.com/leanprover/lean4/pull/14849)
  makes the kernel reject `Nat` literals and computations whose representation would exceed a configurable size limit (128 MB by default). This prevents pathological or adversarial inputs from driving the kernel to spend unbounded memory and time constructing enormous numerals, and keeps the kernel's arithmetic comfortably within the range where its arbitrary-precision integer backend is well exercised. The limit can be raised with the `LEAN_NAT_MAX_SIZE` environment variable for the rare workloads that legitimately compute very large numerals in the kernel.

- [#14847](https://github.com/leanprover/lean4/pull/14847)
  adds another test for the `is_prop` bug in the kernel.
  The exploit was submitted by Daniel Selsam (OpenAI) and was generated using OpenAI's internal models.

- [#14843](https://github.com/leanprover/lean4/pull/14843)
  applies the fix from #14807 to `inductive.h`. As the comment in `inductive.h` points out, the code should check whether `e_type` is a proposition using `is_prop`, but it was still inlining the old, buggy version of `is_prop`.

- [#14808](https://github.com/leanprover/lean4/pull/14808)
  adds a new defensive check to the kernel.

- [#14807](https://github.com/leanprover/lean4/pull/14807)
  fixes a soundness issue.

- [#14806](https://github.com/leanprover/lean4/pull/14806)
  fixes a soundness issue in the kernel.

- [#14161](https://github.com/leanprover/lean4/pull/14161)
  adds support for compiling with thread sanitizer. This both increases memory consumption and slows lean down massively so we only run a very small subset of tests to remain in a reasonable time. Developers need to add additional tests to the set themselves.

````
