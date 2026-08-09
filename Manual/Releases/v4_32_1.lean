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

#doc (Manual) "Lean 4.32.1 (2026-07-22)" =>
%%%
tag := "release-v4.32.1"
file := "v4.32.1"
%%%

This point release fixes a soundness bug in the kernel.

The issue was discovered by Patrick Hulin with the help of GPT-5.6 Sol.

This bug can be used by a malicious meta program to trick the kernel into accepting a proof of `False`, or any other theorem. It requires the malicious meta program to run in the same process as the kernel. In that situation, malicious meta programs already have other, blunter, ways to let the system accept bad proofs, so this bug does not create a new attack vector.

The {ref "validating-comparator"}[recommended way to check possibly dishonest proofs] using comparator is *not* affected by this bug.

See [issue #14484](https://github.com/leanprover/lean4/issues/14484) for more details on the bug and [PR #14498](https://github.com/leanprover/lean4/pull/14498) for the fix.
