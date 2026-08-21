/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
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
  adds a new defensive check to the kernel. When the kernel generates a recursor for an inductive type, it installs the recursor and its computation rules with `add_core`, which does not re-check them. It adds a verification pass that (1) type-checks each generated recursor's type and (2) checks that each computation rule is type-preserving: reducing the recursor applied to a constructor yields a term whose type is the recursor's declared result type. This catches a recursor whose minor-premise type and reduction rule disagree, for example a minor premise that expects an induction hypothesis while the rule omits it. Checking only that a rule's right-hand side has some type is not enough, because an under-applied minor premise is still a well-typed (function) term. The check is defense-in-depth: it does not change what the kernel accepts for well-formed inductives, and only rejects declarations that were already malformed.

- [#14807](https://github.com/leanprover/lean4/pull/14807)
  fixes a soundness issue. The kernel's `is_prop` decided whether a term is a proposition by taking the weak head normal form of its inferred type and checking that the result is syntactically `Sort 0`. When the inferred type did not reduce to a sort but was left as a stuck term, `is_prop` returned `false` instead of treating the term as ill-formed. This let the proof-irrelevance guard in projection inference be skipped, so a non-proof field could be projected out of a value used as a `Prop`, and `False` derived. The fix computes the inferred type with `ensure_sort`, which reduces it and requires the result to be a sort, raising `(kernel) type expected` otherwise. The bogus proof was also accepted by nanoda, an independent implementation of the Lean kernel. We believe the lean4lean external kernel does not have this bug.

- [#14806](https://github.com/leanprover/lean4/pull/14806)
  fixes a soundness issue in the kernel. The kernel cached successful `is_def_eq` queries in a union-find structure. Because the implemented `is_def_eq` is sound but incomplete, and therefore not transitive, the transitive closure computed by the union-find made a query's result depend on the order of earlier queries: `is_def_eq(v0, v2)` could return `false` on its own but `true` after `is_def_eq(v0, v1)` and `is_def_eq(v1, v2)` had succeeded. A crafted input used this to build a recursor whose type and computation rule disagreed, and derive `False`. The fix replaces the union-find with a plain cache keyed on the query pair, so `is_def_eq` is again a function of its two arguments. The issue was reported by Daniel Selsam (OpenAI) using their internal models. An OpenAI agent then produced two distinct exploits based on it. Both exploits are also caught by nanoda, and both are caught by the new lean-inductive-models developed by Joachim Breitner.

- [#14161](https://github.com/leanprover/lean4/pull/14161)
  adds support for compiling with thread sanitizer. This both increases memory consumption and slows lean down massively so we only run a very small subset of tests to remain in a reasonable time. Developers need to add additional tests to the set themselves.

````
