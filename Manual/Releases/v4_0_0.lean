/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.0.0 (2023-09-08)" =>
%%%
tag := "release-v4.0.0"
file := "v4.0.0"
%%%

````markdown
* [`Lean.Meta.getConst?` has been renamed](https://github.com/leanprover/lean4/pull/2454).
  We have renamed `getConst?` to `getUnfoldableConst?` (and `getConstNoEx?` to `getUnfoldableConstNoEx?`).
  These were not intended to be part of the public API, but downstream projects had been using them
  (sometimes expecting different behaviour) incorrectly instead of `Lean.getConstInfo`.

* [`dsimp` / `simp` / `simp_all` now fail by default if they make no progress](https://github.com/leanprover/lean4/pull/2336).

  This can be overridden with the `(config := { failIfUnchanged := false })` option.
  This change was made to ease manual use of `simp` (with complicated goals it can be hard to tell if it was effective)
  and to allow easier flow control in tactics internally using `simp`.
  See the [summary discussion](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/simp.20fails.20if.20no.20progress/near/380153295)
  on zulip for more details.

* [`simp_all` now preserves order of hypotheses](https://github.com/leanprover/lean4/pull/2334).

  In order to support the `failIfUnchanged` configuration option for `dsimp` / `simp` / `simp_all`
  the way `simp_all` replaces hypotheses has changed.
  In particular it is now more likely to preserve the order of hypotheses.
  See [`simp_all` reorders hypotheses unnecessarily](https://github.com/leanprover/lean4/pull/2334).
  (Previously all non-dependent propositional hypotheses were reverted and reintroduced.
  Now only such hypotheses which were changed, or which come after a changed hypothesis,
  are reverted and reintroduced.
  This has the effect of preserving the ordering amongst the non-dependent propositional hypotheses,
  but now any dependent or non-propositional hypotheses retain their position amongst the unchanged
  non-dependent propositional hypotheses.)
  This may affect proofs that use `rename_i`, `case ... =>`, or `next ... =>`.

* [New `have this` implementation](https://github.com/leanprover/lean4/pull/2247).

  `this` is now a regular identifier again that is implicitly introduced by anonymous `have :=` for the remainder of the tactic block. It used to be a keyword that was visible in all scopes and led to unexpected behavior when explicitly used as a binder name.

* [Show typeclass and tactic names in profile output](https://github.com/leanprover/lean4/pull/2170).

* [Make `calc` require the sequence of relation/proof-s to have the same indentation](https://github.com/leanprover/lean4/pull/1844),
  and [add `calc` alternative syntax allowing underscores `_` in the first relation](https://github.com/leanprover/lean4/pull/1844).

  The flexible indentation in `calc` was often used to align the relation symbols:
  ```lean
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc
        (x + y) * (x + y) = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
                        -- improper indentation
                        _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
                        _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
                        _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
  ```

  This is no longer legal.  The new syntax puts the first term right after the `calc` and each step has the same indentation:
  ```lean
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc (x + y) * (x + y)
      _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
  ```


* Update Lake to latest prerelease.

* [Make go-to-definition on a typeclass projection application go to the instance(s)](https://github.com/leanprover/lean4/pull/1767).

* [Include timings in trace messages when `profiler` is true](https://github.com/leanprover/lean4/pull/1995).

* [Pretty-print signatures in hover and `#check <ident>`](https://github.com/leanprover/lean4/pull/1943).

* [Introduce parser memoization to avoid exponential behavior](https://github.com/leanprover/lean4/pull/1799).

* [feat: allow `doSeq` in `let x <- e | seq`](https://github.com/leanprover/lean4/pull/1809).

* [Add hover/go-to-def/refs for options](https://github.com/leanprover/lean4/pull/1783).

* [Add empty type ascription syntax `(e :)`](https://github.com/leanprover/lean4/pull/1797).

* [Make tokens in `<|>` relevant to syntax match](https://github.com/leanprover/lean4/pull/1744).

* [Add `linter.deprecated` option to silence deprecation warnings](https://github.com/leanprover/lean4/pull/1768).

* [Improve fuzzy-matching heuristics](https://github.com/leanprover/lean4/pull/1710).

* [Implementation-detail hypotheses](https://github.com/leanprover/lean4/pull/1692).

* [Hover information for `cases`/`induction` case names](https://github.com/leanprover/lean4/pull/1660).

* [Prefer longer parse even if unsuccessful](https://github.com/leanprover/lean4/pull/1658).

* [Show declaration module in hover](https://github.com/leanprover/lean4/pull/1638).

* [New `conv` mode structuring tactics](https://github.com/leanprover/lean4/pull/1636).

* `simp` can track information and can print an equivalent `simp only`. [PR #1626](https://github.com/leanprover/lean4/pull/1626).

* Enforce uniform indentation in tactic blocks / do blocks. See issue [#1606](https://github.com/leanprover/lean4/issues/1606).

* Moved `AssocList`, `HashMap`, `HashSet`, `RBMap`, `RBSet`, `PersistentArray`, `PersistentHashMap`, `PersistentHashSet` to the Lean package. The [standard library](https://github.com/leanprover/std4) contains versions that will evolve independently to simplify bootstrapping process.

* Standard library moved to the [std4 GitHub repository](https://github.com/leanprover/std4).

* `InteractiveGoals` now has information that a client infoview can use to show what parts of the goal have changed after applying a tactic. [PR #1610](https://github.com/leanprover/lean4/pull/1610).

* Add `[inheritDoc]` attribute. [PR #1480](https://github.com/leanprover/lean4/pull/1480).

* Expose that `panic = default`. [PR #1614](https://github.com/leanprover/lean4/pull/1614).

* New [code generator](https://github.com/leanprover/lean4/tree/master/src/Lean/Compiler/LCNF) project has started.

* Remove description argument from `register_simp_attr`. [PR #1566](https://github.com/leanprover/lean4/pull/1566).

* [Additional concurrency primitives](https://github.com/leanprover/lean4/pull/1555).

* [Collapsible traces with messages](https://github.com/leanprover/lean4/pull/1448).

* [Hygienic resolution of namespaces](https://github.com/leanprover/lean4/pull/1442).

* [New `Float` functions](https://github.com/leanprover/lean4/pull/1460).

* Many new doc strings have been added to declarations at `Init`.

````
