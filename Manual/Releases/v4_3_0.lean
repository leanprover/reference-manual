/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.3.0 (2023-11-30)" =>
%%%
tag := "release-v4.3.0"
file := "v4.3.0"
%%%

```markdown
* `simp [f]` does not unfold partial applications of `f` anymore. See issue [#2042](https://github.com/leanprover/lean4/issues/2042).
  To fix proofs affected by this change, use `unfold f` or `simp (config := { unfoldPartialApp := true }) [f]`.
* By default, `simp` will no longer try to use Decidable instances to rewrite terms. In particular, not all decidable goals will be closed by `simp`, and the `decide` tactic may be useful in such cases. The `decide` simp configuration option can be used to locally restore the old `simp` behavior, as in `simp (config := {decide := true})`; this includes using Decidable instances to verify side goals such as numeric inequalities.

* Many bug fixes:
  * [Add left/right actions to term tree coercion elaborator and make `^`` a right action](https://github.com/leanprover/lean4/pull/2778)
  * [Fix for #2775, don't catch max recursion depth errors](https://github.com/leanprover/lean4/pull/2790)
  * [Reduction of `Decidable` instances very slow when using `cases` tactic](https://github.com/leanprover/lean4/issues/2552)
  * [`simp` not rewriting in binder](https://github.com/leanprover/lean4/issues/1926)
  * [`simp` unfolding `let` even with `zeta := false` option](https://github.com/leanprover/lean4/issues/2669)
  * [`simp` (with beta/zeta disabled) and discrimination trees](https://github.com/leanprover/lean4/issues/2281)
  * [unknown free variable introduced by `rw ... at h`](https://github.com/leanprover/lean4/issues/2711)
  * [`dsimp` doesn't use `rfl` theorems which consist of an unapplied constant](https://github.com/leanprover/lean4/issues/2685)
  * [`dsimp` does not close reflexive equality goals if they are wrapped in metadata](https://github.com/leanprover/lean4/issues/2514)
  * [`rw [h]` uses `h` from the environment in preference to `h` from the local context](https://github.com/leanprover/lean4/issues/2729)
  * [missing `withAssignableSyntheticOpaque` for `assumption` tactic](https://github.com/leanprover/lean4/issues/2361)
  * [ignoring default value for field warning](https://github.com/leanprover/lean4/issues/2178)
* [Cancel outstanding tasks on document edit in the language server](https://github.com/leanprover/lean4/pull/2648).
* [Remove unnecessary `%` operations in `Fin.mod` and `Fin.div`](https://github.com/leanprover/lean4/pull/2688)
* [Avoid `DecidableEq` in `Array.mem`](https://github.com/leanprover/lean4/pull/2774)
* [Ensure `USize.size` unifies with `?m + 1`](https://github.com/leanprover/lean4/issues/1926)
* [Improve compatibility with emacs eglot client](https://github.com/leanprover/lean4/pull/2721)

**Lake:**

* [Sensible defaults for `lake new MyProject math`](https://github.com/leanprover/lean4/pull/2770)
* Changed `postUpdate?` configuration option to a `post_update` declaration. See the `post_update` syntax docstring for more information on the new syntax.
* [A manifest is automatically created on workspace load if one does not exists.](https://github.com/leanprover/lean4/pull/2680).
* The `:=` syntax for configuration declarations (i.e., `package`, `lean_lib`, and `lean_exe`) has been deprecated. For example, `package foo := {...}` is deprecated.
* [support for overriding package URLs via `LAKE_PKG_URL_MAP`](https://github.com/leanprover/lean4/pull/2709)
* Moved the default build directory (e.g., `build`), default packages directory (e.g., `lake-packages`), and the compiled configuration (e.g., `lakefile.olean`) into a new dedicated directory for Lake outputs, `.lake`. The cloud release build archives are also stored here, fixing [#2713](https://github.com/leanprover/lean4/issues/2713).
* Update manifest format to version 7 (see [lean4#2801](https://github.com/leanprover/lean4/pull/2801) for details on the changes).
* Deprecate the `manifestFile` field of a package configuration.
* There is now a more rigorous check on `lakefile.olean` compatibility (see [#2842](https://github.com/leanprover/lean4/pull/2842) for more details).

```
