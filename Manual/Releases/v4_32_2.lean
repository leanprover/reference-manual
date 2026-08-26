/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.32.2 (2026-07-28)" =>
%%%
tag := "release-v4.32.2"
file := "v4.32.2"
%%%

This point release fixes a soundness bug in the kernel.

The issue was discovered by Ramana Kumar and reported by Kiran Gopinathan.

A malicious meta program can trick the kernel into accepting a proof of `False`, or any other theorem. The kernel’s handling of nested inductive types with phantom type parameters was incomplete and bypassed the type checker.

The bug can be exploited even when using `comparator`.

The external checker `nanoda` does not suffer from the same bug. However, by the nature of this bug, it is possible to write proof terms that exploit it and at the same time exploit unrelated bugs in the external checker, as demonstrated by Kumar with a bug in `nanoda` that was (independently) [reported and fixed very recently](https://github.com/ammkrn/nanoda_lib/pull/22/changes). We highly recommend users who have to account for malicious proofs and follow the {ref "validating-comparator"}[recommended way to validate proofs] to upgrade to the latest `nanoda` version as well.

The FRO takes these issues seriously and will invest in the checker ecosystem, towards more hardening, more testing and more independent implementations of kernels and checkers.

See [issue #14576](https://github.com/leanprover/lean4/issues/14576) for more details on the bug and [PR #14577](https://github.com/leanprover/lean4/pull/14577) for the fix.
