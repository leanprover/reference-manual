/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.2.0 (2023-10-31)" =>
%%%
tag := "release-v4.2.0"
file := "v4.2.0"
%%%

```markdown
* [isDefEq cache for terms not containing metavariables.](https://github.com/leanprover/lean4/pull/2644).
* Make [`Environment.mk`](https://github.com/leanprover/lean4/pull/2604) and [`Environment.add`](https://github.com/leanprover/lean4/pull/2642) private, and add [`replay`](https://github.com/leanprover/lean4/pull/2617) as a safer alternative.
* `IO.Process.output` no longer inherits the standard input of the caller.
* [Do not inhibit caching](https://github.com/leanprover/lean4/pull/2612) of default-level `match` reduction.
* [List the valid case tags](https://github.com/leanprover/lean4/pull/2629) when the user writes an invalid one.
* The derive handler for `DecidableEq` [now handles](https://github.com/leanprover/lean4/pull/2591) mutual inductive types.
* [Show path of failed import in Lake](https://github.com/leanprover/lean4/pull/2616).
* [Fix linker warnings on macOS](https://github.com/leanprover/lean4/pull/2598).
* **Lake:** Add `postUpdate?` package configuration option. Used by a package to specify some code which should be run after a successful `lake update` of the package or one of its downstream dependencies. ([lake#185](https://github.com/leanprover/lake/issues/185))
* Improvements to Lake startup time ([#2572](https://github.com/leanprover/lean4/pull/2572), [#2573](https://github.com/leanprover/lean4/pull/2573))
* `refine e` now replaces the main goal with metavariables which were created during elaboration of `e` and no longer captures pre-existing metavariables that occur in `e` ([#2502](https://github.com/leanprover/lean4/pull/2502)).
  * This is accomplished via changes to `withCollectingNewGoalsFrom`, which also affects `elabTermWithHoles`, `refine'`, `calc` (tactic), and `specialize`. Likewise, all of these now only include newly-created metavariables in their output.
  * Previously, both newly-created and pre-existing metavariables occurring in `e` were returned inconsistently in different edge cases, causing duplicated goals in the infoview (issue [#2495](https://github.com/leanprover/lean4/issues/2495)), erroneously closed goals (issue [#2434](https://github.com/leanprover/lean4/issues/2434)), and unintuitive behavior due to `refine e` capturing previously-created goals appearing unexpectedly in `e` (no issue; see PR).

```
