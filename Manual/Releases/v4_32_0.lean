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

#doc (Manual) "Lean 4.32.0-rc1 (2026-06-17)" =>
%%%
tag := "release-v4.32.0"
file := "v4.32.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 102 changes landed.
In addition to the 35 feature additions,
and 20 fixes listed below,
there were 7 refactoring changes,
2 documentation improvements,
9 performance improvements,
2 improvements to the test suite,
and 27 other changes.

# Language

````markdown

- [#14039](https://github.com/leanprover/lean4/pull/14039)
  fixes a bug where the builting docstring roles for asserting equalities did not properly highlight their contents for downstream consumers of rich docstring info, and exposes a structure that was mistakenly made private.

- [#14030](https://github.com/leanprover/lean4/pull/14030)
  removes the hypothesis rewriting functionality of `cbv` (introduced using `cbv at` syntax) in the `Sym` mode. Additionally, this PR fixes the transparency level when dealing with projections in `cbv`.

- [#14025](https://github.com/leanprover/lean4/pull/14025)
  adds `Lean.DoElem` and `Lean.DoSeq` as abbreviations for ``TSyntax `doElem`` and ``TSyntax `Lean.Parser.Term.doSeq``, mirroring `Lean.Term`, and uses them throughout the `do` elaborator.

- [#13961](https://github.com/leanprover/lean4/pull/13961)
  adds a a `--record-exceptions` flag to `lake lint`, such that the definitions triggering builtin linting framework warnings will be silenced, by putting an appropriate `set_option` flag.

- [#13072](https://github.com/leanprover/lean4/pull/13072)
  moves the status emoji from the stored trace header to the rendering layer. `withTraceNode`/`withTraceNodeBefore` no longer prepend `TraceResult.toEmoji` to the header `MessageData`; instead, `formatAux` and `InteractiveDiagnostic` prepend it when rendering. `TraceResult.toEmoji` is moved from `Lean.Util.Trace` to `Lean.Message` (next to the `TraceResult` definition) so that both rendering paths can use it.

- [#13868](https://github.com/leanprover/lean4/pull/13868)
  adds `Lean.Environment.hasExposedBody` — a small helper that asks "does `env` export a body for `n` to downstream modules?". The idiom

- [#13981](https://github.com/leanprover/lean4/pull/13981)
  fixes a private inductive type not being usable as a namespace immediately after its definition.

- [#13970](https://github.com/leanprover/lean4/pull/13970)
  makes the printed name of a variable in a `do`-elaborator error message carry hover info so the infoview surfaces its type. The bulk of the change is a small refactor that introduces a `MutVar` structure (declaration identifier + initial `FVarId`) and threads it through the do-elaborator helpers.

- [#13954](https://github.com/leanprover/lean4/pull/13954)
  prepares the `@[spec]` attribute used by `mvcgen` to support both specifications theorems for both new and old `mvcgen'` meta theories.

- [#13912](https://github.com/leanprover/lean4/pull/13912)
  extends the `nestedAction` parser (`←` inside `do` blocks) to accept arbitrary `doElem`s after `←` instead of just terms. The new `do` elaborator handles any `doElem`; the legacy elaborator (`set_option backward.do.legacy true`) keeps the old restriction to terms and rejects more general `doElem`s with an explicit error.

- [#13931](https://github.com/leanprover/lean4/pull/13931)
  introduces the `do← body` marker (ASCII `do<- body`), which lets ordinary continuation-taking wrappers like `withReader` or `Meta.withLocalDecl` participate in the surrounding `do` block's control flow. When `do← body` appears as the last argument of an application inside a `do` block, the body's `return`, `break`, `continue`, and `mut`-variable reassignments are forwarded out through the wrapper to the enclosing block.

- [#13852](https://github.com/leanprover/lean4/pull/13852)
  adds builtin linter sets — linter sets registered from core Lean code during initialization, complementing the user-facing `register_linter_set` command — and makes `linter.extra` one of them. Enabling `linter.extra` (e.g. via `set_option linter.extra true` or `lake lint --extra`) now activates the extra linters through the same set-membership mechanism as any other linter set.

- [#13917](https://github.com/leanprover/lean4/pull/13917)
  adds module linters, which run once at the end of elaborating a module rather than after every command. A module linter receives the full array of top-level command syntaxes for the module, making it suitable for checks that need a whole-module view (e.g. enforcing module-wide syntactic conventions) rather than per-command checks.

- [#13928](https://github.com/leanprover/lean4/pull/13928)
  fixes a non-linearity in DiscrTree insertion, reducing the time it takes to `import Mathlib` by ~10%

- [#13916](https://github.com/leanprover/lean4/pull/13916)
  fixes the silencing of `deprecated` warnings inside of definitions that are themselves deprecated and use `grind` with a `deprecated` theorem.

- [#13911](https://github.com/leanprover/lean4/pull/13911)
  removes the `Lean.Parser.Term.liftMethod` alias for `Lean.Parser.Term.nestedAction` that was kept for bootstrapping during the rename in #13910. Now that stage0 has been updated, the alias is no longer needed.

- [#13910](https://github.com/leanprover/lean4/pull/13910)
  renames the `liftMethod` parser (the `← <action>` syntax inside `do` blocks) and all of its associated helpers to use the more descriptive "nested action" terminology that the documentation already adopted.

- [#13305](https://github.com/leanprover/lean4/pull/13305)
  makes the new `do` elaborator (#12459) the default by flipping `backward.do.legacy` to `false`. Legacy behavior remains available via `set_option backward.do.legacy true`.

````

# Library

````markdown

- [#14054](https://github.com/leanprover/lean4/pull/14054)
  upstreams `Nat.sqrt` from Batteries and just enough theory from mathlib to characterize the function without having to expose its internals.

- [#14051](https://github.com/leanprover/lean4/pull/14051)
  cleans up the internal `Std.Internal.Do` weakest-precondition library: the wp application lemmas and the `Triple` entailment field are renamed to follow the naming convention, the loop-invariant types are curried, and the monad spec lemmas reuse the `Triple` rules.

- [#14048](https://github.com/leanprover/lean4/pull/14048)
  adds a few lemmas about the way that `cpop` and `setWidth` interact on `BitVec`.

- [#3727](https://github.com/leanprover/lean4/pull/3727)
  adds `BitVec.flattenList`, which concatenates a list of bitvectors of a common width into a single bitvector, together with lemmas describing its bits: `getLsbD_flattenList` and `getMsbD_flattenList` compute an individual bit in terms of the corresponding element of the list, and `extractLsb_flattenList` describes extracting a contiguous range that falls within a single element. For efficient execution, `flattenList` is replaced at runtime via `@[csimp]` with a divide-and-conquer implementation costing `O(n * L * log L)` rather than the `O(n * L²)` of a naive left fold (≈900x faster at a million elements), while keeping `O(log L)` recursion depth so it remains stack-safe.

- [#13458](https://github.com/leanprover/lean4/pull/13458)
  adds `Nat.or_two_pow_eq_add_of_lt`, a small missing bitwise lemma.

- [#13459](https://github.com/leanprover/lean4/pull/13459)
  adds some missing `Array` and `Vector` `set!` convenience lemmas.

- [#13865](https://github.com/leanprover/lean4/pull/13865)
  adds lemmas to simplify sequencing with `pure` in `LawfulApplicative`.

- [#13988](https://github.com/leanprover/lean4/pull/13988)
  removes `OPENSSL_init_ssl` from `initialize_openssl` so it helps with loading OpenSSL lazily.

- [#13798](https://github.com/leanprover/lean4/pull/13798)
  simplifies the `Std.Time` API by removing the `DateTime (tz : TimeZone)` and replacing it with `ZonedDateTime` that got renamed to `DateTime`.

- [#12030](https://github.com/leanprover/lean4/pull/12030)
  links OpenSSL

- [#13960](https://github.com/leanprover/lean4/pull/13960)
  renames the `WPAdequate` typeclass to `WPSound` to reflect that it encodes the directional soundness arrow `wp x P → Internal.Ensures P x` (not a bidirectional adequacy correspondence), and replaces the `Id`-only `*.of_wp_run_eq` family with a uniform per-transformer soundness framework that works over any base monad with `WPSound`.

- [#13908](https://github.com/leanprover/lean4/pull/13908)
  deprecates the `Lean.RBMap` and `Lean.RBTree` containers in favour of `Std.TreeMap` and `Std.TreeSet`, which offer a more complete and consistent API. Nothing in the Lean repository uses these types any longer, and downstream code should migrate to the `Std` containers.

- [#13942](https://github.com/leanprover/lean4/pull/13942)
  introduces `PersistentHashMap.alter` in the same spirit as `Std.HashMap.alter`.

- [#13938](https://github.com/leanprover/lean4/pull/13938)
  adds tail-recursive `@[csimp]` runtime replacements for the bounded-quantifier `Decidable` instances `Nat.decidableBallLT`, `Nat.decidableExistsLT`, and `Nat.decidableExistsLT'`, so that *running* them no longer takes quadratic time or overflows the stack for large `n`.

- [#13891](https://github.com/leanprover/lean4/pull/13891)
  adds opt-in support for serializing closures (functions with captured values) to `.olean` files via `CompactedRegion.save (allowClosures := true)`, so a saved function can be loaded back and called, including from a separate process. Regular module data is unaffected and continues to reject closures.

````

# Tactics

````markdown

- [#14031](https://github.com/leanprover/lean4/pull/14031)
  implements `SymM` simprocs for reducing bit-vector conversion operations.

- [#14029](https://github.com/leanprover/lean4/pull/14029)
  fixes a `Sym.dsimp` bug that could produce an ill-typed term, causing the kernel to reject the resulting goal with errors such as `application type mismatch` or `function expected`. It triggered when a `let`/`λ`/`∀` binder's type or value referenced an earlier binder in the same telescope.

- [#14022](https://github.com/leanprover/lean4/pull/14022)
  fixes `grind?` for goals containing hypotheses with inaccessible names. Distinct terms that differ only in inaccessible variables have identical anchors, so anchor references in generated tactic scripts could resolve to the wrong term during replay, producing empty `grind only` suggestions and scripts that could not close the goal. The `cases` tactic now supports anchor ordinal references (e.g., `cases #a56e/2` selects the second candidate matching the anchor), and `grind?` uses them to disambiguate colliding anchors.

- [#14021](https://github.com/leanprover/lean4/pull/14021)
  fixes an `unknown metavariable` error in `grind` that occurred when instantiating `match`-congruence equations whose generalized-pattern equalities mention theorem parameters that cannot be determined by E-matching.

- [#14020](https://github.com/leanprover/lean4/pull/14020)
  fixes two bugs that made `grind` construct proofs that are rejected by the kernel for goals involving `match`-expressions with overlapping patterns and proof discriminants (#13773).

- [#13971](https://github.com/leanprover/lean4/pull/13971)
  makes the `cbv` tactic available inside `grind`'s interactive `sym =>` mode. It reduces the goal target using call-by-value evaluation and supports the standard `at` location syntax (`cbv at h`, `cbv at h ⊢`, `cbv at *`) to reduce selected hypotheses, automatically closing equation goals via `refl` when reduction finishes the proof.

- [#13983](https://github.com/leanprover/lean4/pull/13983)
  adds `mvcgen' until $t`, where `$t` is a conv-style pattern (holes `_` allowed); verification-condition generation stops as soon as the program matches the pattern, leaving it as a VC instead of applying a spec, similar to the existing `stepLimit` option.

- [#13925](https://github.com/leanprover/lean4/pull/13925)
  consolidates `mvcgen'`'s syntax across tactic and grind (`sym =>`) modes. The grind-mode `with` clause is removed (use `<;>` instead), and the tactic-level `with` now takes a single grind step that shares an E-graph with `mvcgen'`. `mvcgen' invariants?` (suggest mode) also works inside `sym => …` blocks.

- [#13944](https://github.com/leanprover/lean4/pull/13944)
  changes a `filterMap` to a `map` in `CNF.convertLRAT'` so that tautological clauses become `none` in the array rather then being deleted.

- [#13932](https://github.com/leanprover/lean4/pull/13932)
  implements the `evalGround` `dsimproc` for `Sym.dsimp`.

- [#13621](https://github.com/leanprover/lean4/pull/13621)
  fixes a bug in the `rcases`-family tactics where the InfoView could give "unknown free variable" errors when the cursor was inside the pattern. It hoists applying the fvar substitution to give `addTermInfo'` and `addLocalVarInfo` the correct expression. Previously, the substitution only happened in `rfl`/typed/tuple/alternative branches, which caused stale free variables to be recorded in the info tree. Repeated applications in recursive cases like `.paren` should be fine, because the domain of `fs` should be old fvars and replacement exprs should only refer current-goal fvars, not old-domain fvars. Proof elaboration shouldn't be affected by this PR.

- [#13909](https://github.com/leanprover/lean4/pull/13909)
  makes the `intersperse` library suggestion combinator honor `ratio` at the endpoints, so `ratio = 0` draws entirely from `selector₂` and `ratio = 1` entirely from `selector₁` while both selectors still have results. Previously each element was chosen by comparing the achieved fraction of `selector₁` contributions against `ratio` with a strict `<` (seeded to `0` when empty), which left `ratio = 1` drawing one stray element from `selector₂` before settling. The combinator now picks whichever candidate next state keeps the running fraction closest to `ratio`, with ties going to `selector₁`.

- [#13907](https://github.com/leanprover/lean4/pull/13907)
  makes the `intersperse` library suggestion combinator request `maxSuggestions` results from each of its two selectors instead of splitting the budget by `ratio`, so that if one selector returns fewer suggestions than its allocation the other can compensate to still fill the request. The interspersing ratio and the final `maxSuggestions` cap on the combined result are unchanged.

- [#13896](https://github.com/leanprover/lean4/pull/13896)
  improves the support for universe constraints in the `SymM` pattern matcher/unifier. Two new cases are supported

- [#13887](https://github.com/leanprover/lean4/pull/13887)
  factors the whnf-based projection step used inside `mvcgen'`'s head reducer into a new `reduceProjAndUnfold?` helper that `unfoldReducible`s the projected field only when whnf reduced the structure. The outer `Sym.unfoldReducible` call in `tryHeadReduceProg` is no longer needed, so the per-step cost of normalizing abbrevs is proportional to the small unfolded instance body rather than the whole program expression.

- [#13888](https://github.com/leanprover/lean4/pull/13888)
  teaches `mvcgen'` to register Triple-shaped local hypotheses as specs as they come into scope during VC generation. This is an existing feature of `mvcgen`.

- [#13883](https://github.com/leanprover/lean4/pull/13883)
  teaches `mvcgen'` to register Triple-shaped local hypotheses as specs as they come into scope during VC generation. This is an existing feature of `mvcgen`.

- [#13881](https://github.com/leanprover/lean4/pull/13881)
  lets `mvcgen'` decompose programs whose head is a typeclass method projection (e.g. `Add.add inst a b`) by reducing through the kernel projection to the instance body.

- [#13880](https://github.com/leanprover/lean4/pull/13880)
  reverts #13870 due to large performance regressions visible on [radar](https://radar.lean-lang.org/repos/lean4/commits/3757160ab7625097a69757bd1dce8c28f6af9f09) that were not caught by benchmarking before merge.

- [#13878](https://github.com/leanprover/lean4/pull/13878)
  fixes a bug when reducing `match`-expressions in the `Sym.dsimp` tactic.

- [#13870](https://github.com/leanprover/lean4/pull/13870)
  lets `mvcgen'` decompose programs whose head is a typeclass method projection (e.g. `Add.add inst a b`) by reducing through the kernel projection to the instance body.

````

# Compiler

````markdown

- [#14044](https://github.com/leanprover/lean4/pull/14044)
  introduces constant folding for `Nat.reprFast`.

- [#13123](https://github.com/leanprover/lean4/pull/13123)
  makes the task thread pool reclaim idle worker threads after 5 seconds of inactivity. Previously, pool threads were allocated on demand but never freed, which could waste significant memory given the new default 1GB stack size per thread.

- [#13991](https://github.com/leanprover/lean4/pull/13991)
  adds constant folding for `USize` operations that are already supported in other datatypes. It does so by checking whether the result of applying the operation is equivalent in both `UInt32` and `UInt64`. Furthermore, it also adds constant folding operations for the most common bitwise operations.

- [#13989](https://github.com/leanprover/lean4/pull/13989)
  fixes a bug in the constant folding for `Bool` wherein the compiler incorrectly determined
  0-ary functions that participate in constant folding to be equal to `false`.

- [#13974](https://github.com/leanprover/lean4/pull/13974)
  adds constant folding for `USize` relation by evaluating them both in the `UInt32` and
  `UInt64` world and applying the fold if both worlds agree.

- [#13926](https://github.com/leanprover/lean4/pull/13926)
  makes `dbgTraceIfShared` print the shared message in all non-linear situations. Previously
  it would only trigger if `RC > 1`. However, `RC = 0` and `RC < 0` are also non-linearity triggers.

- [#13924](https://github.com/leanprover/lean4/pull/13924)
  fixes a code generator panic that occurred when a recursive definition (well-founded or structural) was marked by a `noncomputable section` and then referenced from computable code. The compiler now reports a clean error, or accepts the second definition when everything occurs in a `noncomputable section`.

````

# FFI

````markdown

- [#13952](https://github.com/leanprover/lean4/pull/13952)
  declares the `extern "C"` parameter of `lean_mk_bool_data_value` as `uint8` to match its `@[export]`ed Lean definition (where a `Bool` argument lowers to `uint8_t` at the C ABI), fixing a `wasm32`-emscripten/LTO ABI mismatch that trapped during module initialization.

````

# Lake

````markdown

- [#14060](https://github.com/leanprover/lean4/pull/14060)
  has Lake deduplicate artifacts by their hash when uploading or downloading to the cache (e.g., in `lake cache put` or `lake cache get`). This fixes possible errors when `curl` was asked to transfer to the same file and/or URL multiple times.

- [#14036](https://github.com/leanprover/lean4/pull/14036)
  refines when and how Lake decides to overwrite data while caching, and has Lake prefer outputs in a local trace file over those stored in the cache.

- [#13893](https://github.com/leanprover/lean4/pull/13893)
  makes environment linters (the declaration-level checks run by `lake lint --builtin-lint`) controlled by `Lean.Option`s, just like ordinary linters. Each environment linter is tied to a boolean option, so you enable or disable it per declaration with `set_option linter.X false in ...` and across a lint run with the new `lake lint --linters=linter.X,-linter.Y` flag.  Using `--lint-only` with the same syntax will only collect information from the specified linters and will not run the default on linters. The previous `lake lint` flags `--extra`, `--lint-all`, and the `builtin_nolint` attribute, are removed in favour of this option-based control.

- [#13949](https://github.com/leanprover/lean4/pull/13949)
  adds a `LAKE_RESTORE_ARTIFACTS` environment variable that overrides the workspace's default `restoreAllArtifacts` configuration, mirroring how `LAKE_ARTIFACT_CACHE` overrides `enableArtifactCache`.

- [#13936](https://github.com/leanprover/lean4/pull/13936)
  fixes an issue where `depPkgs` was not properly set for a transitive dependency that was overriden by a package at a higher level in the dependency graph.

````

# Other

````markdown

- [#14028](https://github.com/leanprover/lean4/pull/14028)
  fixes an issue where existence of potential stray files could influence whether a module is loaded under the module system, resulting in unexpected behavior

- [#14019](https://github.com/leanprover/lean4/pull/14019)
  fixes `mkSimpleThunkType` to use `_` instead of `Name.anonymous` as its binder name. A local declaration whose user name is `Name.anonymous` matches every identifier in `resolveLocalName`, shadowing all global constants and making the pretty printer render every constant in the local context as inaccessible (e.g., `True✝`). The `match` compiler uses `mkSimpleThunkType` to create the minor premises of parameterless alternatives, and tactics that introduce these binders using their binder name verbatim (e.g., `grind`) ended up with a corrupted local context. Found while investigating #13773.

- [#13965](https://github.com/leanprover/lean4/pull/13965)
  adds **experimental** CLI flags that cache `lean`'s post-import elaboration state across invocations: `--incr-save FILE` writes a full snapshot at end of run, `--incr-load FILE` reuses one at startup, and `--incr-header-save FILE` writes a header-only snapshot (post-import `Environment`, no command bodies). A loaded snapshot will be reused as far as unchanged syntax (i.e. import header plus subsequent commands, if saved) allows for.

````
