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
open Lean.MessageSeverity

#doc (Manual) "Lean 4.31.0-rc2 (2026-06-04)" =>
%%%
tag := "release-v4.31.0"
file := "v4.31.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 305 changes landed.
In addition to the 105 feature additions,
and 102 fixes listed below,
there were 17 refactoring changes,
5 documentation improvements,
13 performance improvements,
15 improvements to the test suite,
and 48 other changes.

# Highlights

Lean 4.31.0 is a consolidation-heavy release: alongside a handful of new user-facing features — `do` blocks elaboration, Lake built-in linting, and richer editor hovers — it lands a large, coordinated effort to make definitional-equality checking properly respect transparency levels, a faster and reimplemented `mvcgen'`, significant development in libraries including HTTP, and broad performance work including an LLVM 22 upgrade.

## `do` Notation: New Loop Forms and New Elaborator

The `while` condition in `do` blocks now accepts any condition form already allowed by `if` ([#13534](https://github.com/leanprover/lean4/pull/13534)). In addition to `while c do …` and `while h : c do …`, you can now match against a pattern, binding either with `:=` or with `←`:

```
while let some x := stack.pop? do
  process x

while let .ok line ← readLine? do
  handle line
```

`repeat`/`while` loops also became *verifiable* ([#13209](https://github.com/leanprover/lean4/pull/13209)). They now expand through a new `whileM` combinator that admits a one-step unfolding lemma `whileM_eq`. Existing loops keep working without source changes, and the accompanying `@[spec]`. See also [#13689](https://github.com/leanprover/lean4/pull/13689) / [#13442](https://github.com/leanprover/lean4/pull/13442) / [#13447](https://github.com/leanprover/lean4/pull/13447).

At the same time, the new `do` elaborator (accessible via `set_option backward.do.legacy false`) is also being developed: beyond extensibility, it already produces more precise and more actionable diagnostics:

```lean (name := newDo)
set_option backward.do.legacy false in
example : IO Nat := do
  return 5
  IO.println "never runs"
```
```leanOutput newDo (severity := warning)
This `do` element and its control-flow region are dead code. Consider removing it.
```

The legacy elaborator instead rejects the same program with a coarser, purely structural error:

```lean +error (name := oldDo)
example : IO Nat := do
  return 5
  IO.println "never runs"
```
```leanOutput oldDo (severity := error)
must be last element in a `do` sequence
```

Related development in [#13404](https://github.com/leanprover/lean4/pull/13404) / [#13542](https://github.com/leanprover/lean4/pull/13542) / [#13491](https://github.com/leanprover/lean4/pull/13491) / [#13494](https://github.com/leanprover/lean4/pull/13494) / [#13502](https://github.com/leanprover/lean4/pull/13502) / [#13506](https://github.com/leanprover/lean4/pull/13506) / [#13486](https://github.com/leanprover/lean4/pull/13486) / [#13397](https://github.com/leanprover/lean4/pull/13397) / [#13396](https://github.com/leanprover/lean4/pull/13396) / [#13399](https://github.com/leanprover/lean4/pull/13399) / [#13413](https://github.com/leanprover/lean4/pull/13413) / [#13434](https://github.com/leanprover/lean4/pull/13434) / [#13437](https://github.com/leanprover/lean4/pull/13437) / [#13507](https://github.com/leanprover/lean4/pull/13507) / [#13255](https://github.com/leanprover/lean4/pull/13255) / [#13250](https://github.com/leanprover/lean4/pull/13250).

## Monadic Program Verification: `mvcgen'`

Work continues on the monadic verification framework. [#12965](https://github.com/leanprover/lean4/pull/12965) introduces new foundations for reasoning about monadic Lean code, generalizing the assertion language for pre-/post-conditions of monadic Hoare triples from `SPred` to any `CompleteLattice`, separating post-conditions on terminating and abrupt paths, and resolving several universe-polymorphism issues.

Building on this, [#13644](https://github.com/leanprover/lean4/pull/13644) adds the experimental `mvcgen'` tactic, a from-scratch reimplementation of `mvcgen` on the new `SymM`-based symbolic-evaluation framework. It can outperform {tactic}`mvcgen` by a factor of over 100x on some synthetic benchmarks and aspires to be feature-complete with it. `mvcgen'` can also be used as a step inside interactive `sym => …` blocks, where leftover verification conditions become subgoals for subsequent `grind` steps ([#13680](https://github.com/leanprover/lean4/pull/13680)).

## Transparency and Defeq Discipline

A cross-cutting theme of this release is making definitional-equality checking properly respect *transparency*: how aggressively Lean unfolds definitions when deciding whether two terms are *definitionally equal*. A plain `def` is defeq to its body at `.default` transparency, but `simp`/`dsimp` operate at the lower `.reducible` level, where it does not unfold:

```lean +error
def x : Nat := 5

-- `rfl` checks defeq at `.default` transparency, so it closes the goal:
example : x = 5 := rfl

-- but `with_reducible` (where `simp`/`dsimp` run) won't unfold it:
example : x = 5 := by with_reducible refl

-- and `simp`/`dsimp` does not work either:
example : x = 5 := by simp
```

Previously such transparency mismatches were common and hard to diagnose. The usual fix is to let the constant unfold at the lower transparency by marking it `@[reducible]`:

```lean (name := defeqFix)
@[reducible] def y : Nat := 5
example : y = 5 := by with_reducible rfl
example : y = 5 := by simp
```

*Migration:* if proofs break under the stricter regime, the most common fixes are to scope `set_option backward.defeqAttrib.useBackward true in` over the affected declaration, switch `simpa using` to `simpa using!`, mark the relevant constants `@[implicit_reducible]`, or add the now-required projections explicitly to `simp`/`dsimp` calls. The diagnostics above (and `set_option diagnostics true` with `set_option trace.diagnostics true`) help locate the affected spots.

Related development: [#13492](https://github.com/leanprover/lean4/pull/13492) / [#13363](https://github.com/leanprover/lean4/pull/13363) / [#13281](https://github.com/leanprover/lean4/pull/13281) / [#13512](https://github.com/leanprover/lean4/pull/13512) / [#13636](https://github.com/leanprover/lean4/pull/13636) / [#13833](https://github.com/leanprover/lean4/pull/13833) / [#13317](https://github.com/leanprover/lean4/pull/13317) / [#13368](https://github.com/leanprover/lean4/pull/13368) / [#13793](https://github.com/leanprover/lean4/pull/13793) / [#13280](https://github.com/leanprover/lean4/pull/13280) / [#13768](https://github.com/leanprover/lean4/pull/13768) / [#13772](https://github.com/leanprover/lean4/pull/13772).

## Deprecating Modules, Syntax, and Options

This release adds a family of tools for library authors to manage deprecations:

- [#13002](https://github.com/leanprover/lean4/pull/13002) adds a `deprecated_module` command that marks the current module as deprecated; importers receive a warning suggesting replacements. A `#show_deprecated_modules` command lists deprecated modules in the environment.

  ```
  deprecated_module "use NewModule instead" (since := "2026-03-30")
  ```

- [#13108](https://github.com/leanprover/lean4/pull/13108) adds a `deprecated_syntax` command that marks syntax kinds as deprecated, emitting a linter warning when the deprecated syntax is elaborated, including through macro expansion.
- [#13195](https://github.com/leanprover/lean4/pull/13195) allows options to be marked deprecated, warning on `set_option` uses (controlled by `linter.deprecated.options`).

A related set of new linters warns about redundant modifiers: `linter.redundantVisibility` for `private`/`public` that matches the default ([#13132](https://github.com/leanprover/lean4/pull/13132)), `linter.redundantExpose` for no-op `@[expose]`/`@[no_expose]` ([#13359](https://github.com/leanprover/lean4/pull/13359)), and warnings for `@[simp]` theorems with a variable or unrecognized head symbol ([#13325](https://github.com/leanprover/lean4/pull/13325)).

## Lake: Built-in Linting

Lake gains a built-in linting framework, accessible through `lake lint` flags ([#13393](https://github.com/leanprover/lean4/pull/13393), [#13431](https://github.com/leanprover/lean4/pull/13431)). It ships with environment linters upstreamed from Batteries/Mathlib (`defLemma`/`defProp`, `checkUnivs`) — see also the core upstreaming in [#13356](https://github.com/leanprover/lean4/pull/13356) — and a `builtinLint` package configuration option. Flags include `--builtin-lint`, `--builtin-only`, `--clippy`, `--lint-all`, and `--lint-only <name>`, and a `@[builtin_nolint]` attribute suppresses specific linters per declaration.

[#13513](https://github.com/leanprover/lean4/pull/13513) extends this to *text* linters by persisting their warnings into each module's `.olean`, and [#13843](https://github.com/leanprover/lean4/pull/13843) makes module-system targets lint their public surface, matching what downstream consumers see.

## Performance

This release includes broad performance work:

- [#13545](https://github.com/leanprover/lean4/pull/13545) upgrades the bundled compiler toolchain from LLVM 19 to LLVM 22, bringing general improvements of up to 5% instructions depending on the benchmark.
- [#13788](https://github.com/leanprover/lean4/pull/13788) generates specialized `dec` code for values of known shape, and [#13669](https://github.com/leanprover/lean4/pull/13669) optimizes the `lean_dec_ref_cold` cold path.
- [#13796](https://github.com/leanprover/lean4/pull/13796) reduces `String.compare` to a single `memcmp`, and [#13235](https://github.com/leanprover/lean4/pull/13235) uses `memcmp` for {name}`ByteArray` equality.
- [#13651](https://github.com/leanprover/lean4/pull/13651) replaces the tactic configuration elaboration system with one that directly constructs configuration objects and can skip term elaboration entirely; configuration evaluation now takes about 6.2% of the time it did before. The new system also supports custom configuration syntaxes and user configuration options for {tactic}`simp` (e.g. `(user.optionName := …)`).
- Elaboration itself is faster for structure instance notation with many fields ([#13760](https://github.com/leanprover/lean4/pull/13760)) and for `Expr.instantiateBetaRevRange` in the common case ([#13758](https://github.com/leanprover/lean4/pull/13758)).

## Library Highlights

The standard HTTP library introduced last release grows into a working server: [#12146](https://github.com/leanprover/lean4/pull/12146) adds the `H1` pure HTTP/1.1 state machine and [#12151](https://github.com/leanprover/lean4/pull/12151) adds an async HTTP/1.1 `Server`. Importantly, [#13511](https://github.com/leanprover/lean4/pull/13511) graduates the `Async` and `Http` modules out of `Internal` into `Std`.

Other notable library additions:

- Date/time gains a `WallTime` type for local-time points and a simplified `Timestamp` API ([#13675](https://github.com/leanprover/lean4/pull/13675)), plus `Locale`/`LocaleSymbols` for configurable formatting ([#13567](https://github.com/leanprover/lean4/pull/13567)).
- `List.prod`/`Array.prod`/`Vector.prod` mirror the existing `sum` API, with simp and grind lemmas ([#13200](https://github.com/leanprover/lean4/pull/13200)).
- More {name}`ByteArray` `push`/`set!` lemmas ([#13457](https://github.com/leanprover/lean4/pull/13457)) and `Vector` append lemmas generalized to differently-sized vectors ([#13693](https://github.com/leanprover/lean4/pull/13693)).
- Verification of `String.dropWhile`/`String.takeWhile` continues the String verification effort ([#13155](https://github.com/leanprover/lean4/pull/13155)).

A number of runtime robustness fixes also turn previously silent memory-exhaustion failures into proper errors or panics instead of segfaults and corruption ([#13392](https://github.com/leanprover/lean4/pull/13392), [#13546](https://github.com/leanprover/lean4/pull/13546), [#13547](https://github.com/leanprover/lean4/pull/13547), [#13548](https://github.com/leanprover/lean4/pull/13548), [#13549](https://github.com/leanprover/lean4/pull/13549), [#13521](https://github.com/leanprover/lean4/pull/13521)). For security-sensitive deployments, [#13401](https://github.com/leanprover/lean4/pull/13401) adds a `LEAN_MI_SECURE` build option enabling additional mimalloc memory-safety mitigations.

## Editor and UX Improvements

[#13260](https://github.com/leanprover/lean4/pull/13260) adds server-side support for *incremental diagnostics*. Previously, reporting diagnostics while a file was being processed required re-sending the full set each time, a quadratic amount of work over the course of a file. Clients that advertise `incrementalDiagnosticSupport` now receive a `PublishDiagnosticsParams.isIncremental` flag telling them to append rather than replace, eliminating the quadratic reporting. A client-side implementation for the VS Code extension is tracked in [vscode-lean4#752](https://github.com/leanprover/vscode-lean4/pull/752).

There is also significant development in the display of metavariables ([#13446](https://github.com/leanprover/lean4/pull/13446)) and hovering ([#13728](https://github.com/leanprover/lean4/pull/13728) / [#13399](https://github.com/leanprover/lean4/pull/13399) / [#13678](https://github.com/leanprover/lean4/pull/13678) / [#13715](https://github.com/leanprover/lean4/pull/13715)).

## Breaking Changes

Beyond the transparency-related changes above, note the following:

- [#13807](https://github.com/leanprover/lean4/pull/13807) makes the application elaborator beta-reduce arguments while substituting them into later expected types, consistent with `inferType` and `instantiateMVars`. *Breaking change:* some tactic proofs may need unnecessary steps removed, e.g. `dsimp only` steps that previously existed only to perform these beta reductions. Relatedly, [#13528](https://github.com/leanprover/lean4/pull/13528) changes metavariable bookkeeping so that metaprograms can no longer assume an `MVarId` changes merely because metavariables were assigned (for example, `change` no longer changes the `MVarId` when its only effect is incidental assignments); it also revealed many `dsimp`s that did nothing and can be deleted.
- [#13243](https://github.com/leanprover/lean4/pull/13243) no longer applies a structure's default values when elaborating structure instance notation *in patterns* (e.g. `s matches { x := 1 }`). *Breaking change:* such patterns may now report “field missing” errors and need the missing fields supplied or a `..` added.
- [#13476](https://github.com/leanprover/lean4/pull/13476) filters assigned metavariables before computing `apply`/`rewrite` subgoal tags, so a single remaining goal now inherits the input goal's tag. *Breaking change:* scripts relying on the previous tag names (e.g. `case h => …` after `funext`) may need updating.
- [#13030](https://github.com/leanprover/lean4/pull/13030) changes level-metavariable pretty printing to use per-definition indices. *Breaking metaprogramming change:* level pretty printing should use `delabLevel` or `MessageData.ofLevel`; `format`/`toString` lack access to the indices and print the raw internal identifier as `?_mvar.nnn`. Some tests needed `maxHeartbeats` raised 20–50% due to index-recording allocations.
- [#13627](https://github.com/leanprover/lean4/pull/13627) renames `UInt8.ofNatTruncate` to `UInt8.ofNatClamp` (and the other width variants) for consistency with the rest of the `UIntX` API.
- [#13516](https://github.com/leanprover/lean4/pull/13516) adds the missing `namespace Lake` to `Lake.Util.Opaque`; code referring to `Opaque` without `open Lake` must be updated.

# Language

````markdown

- [#13803](https://github.com/leanprover/lean4/pull/13803)
  renames the `defLemma` linter to `defProp` and clarifies
  its warning message.

- [#13862](https://github.com/leanprover/lean4/pull/13862)
  updates the error message improvement from #10488 to also check for identifier escape characters when providing the improved message. Before, it checked only for identifier start characters.

- [#13853](https://github.com/leanprover/lean4/pull/13853)
  makes `lake lint --builtin-lint` group saved text linter diagnostics by the module
  that produced them, rather than printing one combined block under the
  top-level module being linted. Each contributing submodule now gets its own
  `-- Text linter diagnostics in <module>:` header, mirroring how the
  environment-linter side already groups results.

- [#13844](https://github.com/leanprover/lean4/pull/13844)
  makes `Lean.Linter.logLint` attach an internal tag to every
  linter warning so that `Lean.Linter.recordLints` can reliably distinguish
  linter-produced messages from other tagged messages (named errors,
  unknown-identifier messages, `hasSorry` markers, etc.). Previously,
  `recordLints` captured every message whose top-level kind was non-anonymous,
  which over-recorded non-linter diagnostics into the persistent lint log.

- [#13752](https://github.com/leanprover/lean4/pull/13752)
  makes projection notation errors always mention a private declaration on a parent structure as the cause when applicable. Previously, for projections that resolved through structure inheritance, the hint was silently omitted, leaving users without the actual cause.

- [#13813](https://github.com/leanprover/lean4/pull/13813)
  fixes an issue where `beforeElaboration` attributes were not being run on `inductive`/`structure`/`coinductive` commands. Closes #13433.

- [#13811](https://github.com/leanprover/lean4/pull/13811)
  updates the `#where` command to be able to report `module`-related scope state, for example a  `@[expose] public meta section` line in the output.

- [#13760](https://github.com/leanprover/lean4/pull/13760)
  improves elaboration performance for structure instance notation with large numbers of fields. It also uses beta-reducing substitution for structure parameters, which is already the case for structure fields.

- [#13807](https://github.com/leanprover/lean4/pull/13807)
  modifies the app elaborator to beta reduce arguments while substituting them into expected types for later arguments. This makes it consistent with `inferType` and `instantiateMVars`, which both beta reduce substitutions. In particular, this change ensures that the app elaborator behaves as if it creates metavariables for each parameter and assigns elaborated arguments to the metavariables. **Breaking change:** tactic proofs may need to be modified to remove unnecessary steps, e.g. `dsimp only` steps that were previously for beta reductions.

- [#13808](https://github.com/leanprover/lean4/pull/13808)
  enforces that Verso docstring extensions should always be meta at attribute application time, giving better error messages, and ensures that the generated argument parser helper is also meta and has the same visibility.

- [#13801](https://github.com/leanprover/lean4/pull/13801)
  adds two new fields to `DoOps`, `splitMonadApp?` and `mkMonadApp`, so that callers of `elabDoWith` can use indexed monads like `Measure α` (where `Measure : (α : Type u) → [MeasureSpace α] → Type u` carries instance arguments) that the default `m α` decomposition cannot handle. The existing behavior moves into `DoOps.default`.

- [#13800](https://github.com/leanprover/lean4/pull/13800)
  renames the `do` elaborator's `mkMonadicType` to `mkMonadApp`, aligning it with the existing `mkPureApp` / `mkBindApp` naming convention in `DoOps`.

- [#13780](https://github.com/leanprover/lean4/pull/13780)
  is part 2 to #13779. It completes the transition of the configuration evaluation metaprograms into being builtin elaborators.

- [#13779](https://github.com/leanprover/lean4/pull/13779)
  makes the command elaborators for configuration evaluation metaprogramming be builtins, to avoid bootstrapping ABI issues in core Lean due to the interpreter evaluating large parts of the elaborator before all builtin initializers are run. (This is part 1; #13780 will be applied after a stage0 update.)

- [#13762](https://github.com/leanprover/lean4/pull/13762)
  does some refactoring of the function application elaborator, and it improves `trace.Elab.app` tracing. It also improves asymptotic complexity by more carefully substituting arguments into the function's type and by changing how named argument dependency suppression is implemented. For dot notation, it now constructs base projections directly rather than using the app elaborator. It fixes a bug in the eta args feature where more explicit arguments would be turned into implicit arguments than expected, and it improves expected type propagation by following the rules from the main app elaborator.

- [#13772](https://github.com/leanprover/lean4/pull/13772)
  closes https://github.com/leanprover/lean4/issues/13770 by including `Config.zetaUnused` in `Config.toKey`. Without this, two configs that differ only in `zetaUnused` share a `WHNF`/`isDefEq` cache key, so reductions performed under one setting can be returned for the other. The new bit sits at position 22, immediately above `zetaHave`.

- [#13768](https://github.com/leanprover/lean4/pull/13768)
  fixes a long-standing bug in `Meta.Config.toKey` and `Context.setTransparency` where `TransparencyMode` was packed into only 2 bits of the cache key, even though it has 5 constructors (`.all`, `.default`, `.reducible`, `.instances`, `.none`). The `.none` case (value `4`, i.e. `0b100`) overlapped with the `foApprox` bit, so configurations differing only in transparency vs. `foApprox` could collide in the `isDefEq`/`WHNF` cache, and `Context.setTransparency` corrupted the neighbouring bit when switching to/from `.none`.

- [#13763](https://github.com/leanprover/lean4/pull/13763)
  adds `MessageData.withExprHover`, for creating messages that show information about an expression when hovered over. A `withExprHoverM` variant captures the current local context.

- [#13758](https://github.com/leanprover/lean4/pull/13758)
  improves `Expr.instantiateBetaRevRange` to be more efficient in the common case where lambda functions are not being instantiated, and it increases expression sharing in applications.

- [#13737](https://github.com/leanprover/lean4/pull/13737)
  changes the separator between the plugin file name and the initialization function in `--plugin` from `:` to `=`. This prevents clashes with the `:` in drive prefixes on Windows.

- [#13651](https://github.com/leanprover/lean4/pull/13651)
  replaces the previous tactic configuration system with a significantly more efficient one that supports custom configuration syntaxes and processing. On a simple benchmark, configuration evaluation takes 6.2% of the time it used to. The `declare_config_elab` command generates a configuration elaborator that now directly constructs configuration objects; previously it relied on `Meta.evalExpr'`, which involved running a configuration through the full term elaboration, compilation, and evaluation processes. The generated configuration elaborators now also have the capability to do direct `Syntax` evaluation in common cases, skipping term elaboration. Furthermore, the elaborator accepts configurations more liberally: any user-defined syntax that has the form of an `optConfig`-style configuration or configuration item (including, e.g., `namedArgument`s) is accepted. Import `Lean.Elab.ConfigEval` to use the system; see this module for some documentation in addition to the docstrings in `Lean.Elab.ConfigEval.Commands`. Furthermore, the `simp` tactic now also has `(user.optionName := ...)` user configuration options, which can be declared using a global `tactic.simp.user.optionName` option; use `getUserConfigOption` and `withUserConfig` to access and set these in metaprograms.

- [#13550](https://github.com/leanprover/lean4/pull/13550)
  improves the logic and performance of the `checkImpossibleInstance` function to detect more arguments that are impossible to
  infer for typeclass synthesis. It also improves the formatting of the error messages for `checkImpossibleInstance` and `checkNonClassInstance` to be more readable.

- [#13730](https://github.com/leanprover/lean4/pull/13730)
  fixes a regression introduced in #7166 where, after fixed and varying
  parameters were allowed to be reordered, three places in
  `Lean.Elab.Structural.FindRecArg` still indexed the concatenation `xs ++ ys`
  with `recArgInfo.recArgPos` even though `recArgPos` refers to the original
  parameter order. With fixed parameters interleaved with the structural
  argument, this picked the wrong element: error messages named the wrong
  parameter, and `argsInGroup`'s nested-inductive recognition silently rejected
  otherwise-valid mutual definitions.

- [#13728](https://github.com/leanprover/lean4/pull/13728)
  improves hovers and completions for compound field names in structure instance notation. Previously a field like `x.fst` would only have information associated to `x` attached to the entire syntax, but now `x` and `fst` are treated separately.

- [#13715](https://github.com/leanprover/lean4/pull/13715)
  improves the message of `unusedVariables` linter, by replacing potentially confusing "unused variable `x`" message with "Variable name `x` is not explicitly referenced. The binding can be removed (if unused) or named `_` (if used implicitly)."

- [#13710](https://github.com/leanprover/lean4/pull/13710)
  makes the test-only `waitForMessage` helper abort promptly
  when the Lean language server reports a fatalError, instead of
  blocking until the outer test framework's timeout kills the process.

- [#11313](https://github.com/leanprover/lean4/pull/11313)
  ensures that `withSetOptionIn` does not modify the infotrees or error on malformed option values, and thus avoids panics in linters that traverse the infotrees with `visitM`.

- [#13595](https://github.com/leanprover/lean4/pull/13595)
  silences the `Linter.deprecated` warnings inside of definitions that are themselves deprecated.

- [#13209](https://github.com/leanprover/lean4/pull/13209)
  adds `whileM`, a counterpart to `Lean.Loop.forIn` that admits a one-step unfolding lemma `whileM_eq` (impossible to prove for the original `partial def`). `Lean.Loop.forIn` now expands to `whileM`, so `repeat`/`while` keep working without source changes, and the `Spec.whileM`/`Spec.forIn_loop` `@[spec]` theorems let `mvcgen` discharge their bodies given a Nat variant and an `α ⊕ β` invariant.

- [#13670](https://github.com/leanprover/lean4/pull/13670)
  adds support for blockquotes to Verso docstrings, which had been missing before. It also substantially improves the robustness of Verso->Markdown rendering of docstrings, especially the handling of blockquote line prefixes.

- [#13663](https://github.com/leanprover/lean4/pull/13663)
  replaces the `check_cancel` two-way coordination protocol used by
  `tests/server_interactive/cancellation_par.lean` with a single tactic
  `block_until_cancelled "<label>"`. The first invocation for a label registers
  a promise, prints `<label>: blocked`, and loops on `Core.checkInterrupted`
  until the cancel token fires (then `finally` resolves the promise). Any later
  invocation for the same label waits on that promise — so the test only
  terminates if the first invocation actually exited the loop. If cancellation
  fails to propagate, the second invocation's `IO.wait` blocks forever and the
  test hangs (timeout = failure), with no false-success path.

- [#13548](https://github.com/leanprover/lean4/pull/13548)
  fixes possible corruption when recovering from memory exhaustion.

- [#13613](https://github.com/leanprover/lean4/pull/13613)
  makes the elaborator reject `@[foo]` when the module that registers `foo` is not visibly imported into the current file but merely loaded as IR. Previously such uses silently elaborated but led to divergence of cmdline and server behavior and caused `lake shake --fix` to flip-flop on successive runs (#13599).

- [#13510](https://github.com/leanprover/lean4/pull/13510)
  adds the ability to specify a name for the initialization function of a Lean plugin on load.

- [#13645](https://github.com/leanprover/lean4/pull/13645)
  fixes the termination checker reporting errors at the wrong
  recursive call site when a function contains structurally-identical
  recursive calls at different source locations.

- [#13547](https://github.com/leanprover/lean4/pull/13547)
  prevents silent allocation failures leading to memory corruption when not using GMP.

- [#13596](https://github.com/leanprover/lean4/pull/13596)
  fixes private(ly imported) default instances from accidentally being used in public signatures, leading to follow-up errors.

- [#13574](https://github.com/leanprover/lean4/pull/13574)
  ensures consistent metavariable behavior between Verso docstrings and Verso moduledocs by sharing more code between their elaborators. It also improves the error message when a metavariable leak is prevented.

- [#13528](https://github.com/leanprover/lean4/pull/13528)
  gives the `specialize` tactic the ability to instantiate universal quantifiers other than the first using `specialize h (y := v)` syntax. It also fixes an issue where `MVarId.assertAfter` did not record variable alias information, and an issue where `MVarId.replace` and `MVarId.replaceLocalDecl` did not take metavariables into account when calculating dependencies. Additionally it fixes some uninstantiated metavariables bugs, including one in the Infoview tactic state hypothesis diff.

- [#13428](https://github.com/leanprover/lean4/pull/13428)
  fixes parallel tactic combinators (`attempt_all_par`, `first_par`) leaking their subtasks when the server cancels elaboration on re-elaboration. Subtasks spawned via `CoreM.asTask` (and its `MetaM`/`TermElabM`/`TacticM` variants) get a fresh `IO.CancelToken`, which previously had no link to the parent token; `cancelRec` would set the command-level token but the children kept running.

- [#13569](https://github.com/leanprover/lean4/pull/13569)
  addresses two review points on `IO.CancelToken`:

  * `set` now resolves the underlying promise *before* writing the `Bool`
    fast-path flag, so observing `isSet = true` implies any synchronously
    chained `onSet` callback has already run. The previous order (flag first,
    then resolve) was a subtle footgun: code seeing `isSet = true` could not
    rely on the cancellation task having fired.
  * The underlying promise and the task it produces are kept private. The
    prior `task : Task (Option Unit)` accessor is removed; consumers should
    use `onSet` to react to cancellation. A comment on the structure records
    that re-exposing the task in the future requires re-auditing the order
    in `set` for races between the promise and the `Bool` flag.

- [#13303](https://github.com/leanprover/lean4/pull/13303)
  moves `IO.CancelToken` from `Init.System.IO` to its own file `Init.System.CancelToken`, backed by `IO.Promise Unit` instead of `IO.Ref Bool`. This enables non-polling cancellation propagation: the token's underlying promise can be used directly with `IO.waitAny`, and callbacks can be registered to fire when cancellation is requested.

- [#13542](https://github.com/leanprover/lean4/pull/13542)
  replaces the catch-all "unsupported pattern in syntax match" error that the new `do` elaborator produces for typical pattern mistakes (#2215, #8304, #10393) with the proper diagnostics from the regular pattern-var collector (e.g. "Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`", "ambiguous pattern, use fully qualified name"), pointing at the offending pattern.

- [#13359](https://github.com/leanprover/lean4/pull/13359)
  adds a `linter.redundantExpose` option (default `true`) that warns when `@[expose]` or `@[no_expose]` attributes have no effect:

  - `@[expose]` on `abbrev` (always exposed) or non-Prop `instance` (always exposed)
  - `@[expose]` on a `def` inside an `@[expose] section` (already exposed by the section)
  - `@[expose]`/`@[no_expose]` in a non-`module` file (no module system)
  - `@[no_expose]` on a declaration that wouldn't be exposed by default

- [#13492](https://github.com/leanprover/lean4/pull/13492)
  introduces stricter inference for the `@[defeq]` attribute and a
  companion `@[backward_defeq]` attribute that preserves the pre-PR behavior
  as an opt-in.

- [#13534](https://github.com/leanprover/lean4/pull/13534)
  generalizes the `while` syntax in `do` blocks so that the condition can be any `doIfCond`, the same condition form already accepted by `if`. As a result, `while let pat := e do …` and `while let pat ← e do …` are now supported in addition to `while cond do …` and `while h : cond do …`. The previously separate `doWhile` and `doWhileH` parsers and their accompanying macros are unified into a single `doWhile` parser whose macro delegates to the existing `doIf` desugaring.

- [#13523](https://github.com/leanprover/lean4/pull/13523)
  allows tactic macros and elaborators to opt out of automatic fallback to previous macros/elabs on failure. `throwUnsupportedSyntax` is unaffected.

- [#13363](https://github.com/leanprover/lean4/pull/13363)
  replaces the transparency bump from `.reducible` to `.instances` in `whnfMatcher` with an explicit allowlist in `canUnfoldAtMatcher`. Previously, `whnfMatcher` would unfold all `implicitReducible` definitions and all `fromClass` projections when reducing match discriminants. This made it impossible to mark definitions as `implicit_reducible` without silently affecting match reduction behavior.

- [#13512](https://github.com/leanprover/lean4/pull/13512)
  changes `whnfAux` in the equation-theorem generation machinery to use
  reducible transparency (`whnfR`) instead of instances transparency (`whnfI`).
  Previously, the loop in `Eqns.go` would unfold instances on the LHS, which
  interacts badly with users that mark `dite`/`ite` as `implicit_reducible`:
  equation generation would reduce past the `dite` and get stuck instead of
  committing to a branch. The original motivation for `whnfI` (reducing
  `Nat.rec ... (OfNat.ofNat 0)` residuals from `match` on numeric literals) is
  already covered by the surrounding `simpMatch?`/`simpIf?`/`simpTargetStar`
  steps in `Eqns.go`, so the full test suite continues to pass.

- [#13506](https://github.com/leanprover/lean4/pull/13506)
  appends `unreachable!` to the expansion of `break`-less `repeat` when the expected result type does not unify with `PUnit`. The continuation then has a polymorphic value, so the enclosing do block's result type is inferred without a user-written filler, and `ControlInfo` for break-less `repeat` can report `noFallthrough` honestly — dead-code warnings on subsequent elements are now actionable.

- [#13507](https://github.com/leanprover/lean4/pull/13507)
  exposes the `Pure.pure` / `Bind.bind` applications emitted by the `do` elaborator as pluggable closures, so external surface syntaxes (e.g. an `ido` notation for indexed monads) can reuse the full `do` machinery while emitting alternate constants.

- [#13491](https://github.com/leanprover/lean4/pull/13491)
  fixes the `ControlInfo` inference for a do-block `match`: the fold over the match arms started from `ControlInfo.pure` (defaults to `numRegularExits := 1`, `noFallthrough := false`), but `alternative` sums `numRegularExits` and ANDs `noFallthrough`, so the fold identity is `{ numRegularExits := 0, noFallthrough := true }`. With the wrong base, a `match` whose arms all `break`/`continue`/`return` reported `numRegularExits = 1` and `noFallthrough = false`, suppressing the dead-code warning on the continuation after the match. The fix corrects both the inference handler in `InferControlInfo.lean` and the fold in `elabDoMatchCore`.

- [#13502](https://github.com/leanprover/lean4/pull/13502)
  splits `ControlInfo`'s dead-code signal in two. `numRegularExits` is now purely syntactic: how many times the block wires its continuation into the elaborated expression, consumed by `withDuplicableCont` as a join-point duplication trigger (`> 1`). The new `noFallthrough : Bool` asserts that the next doElem in the enclosing sequence is semantically irrelevant; `false` asserts nothing. Invariant: `numRegularExits = 0 → noFallthrough`; the converse does not hold. `sequence` derives `noFallthrough := a.noFallthrough || b.noFallthrough` (and aggregates syntactic fields unconditionally); `alternative` derives it as `a.noFallthrough && b.noFallthrough`. The dead-code warning gate in `withDuplicableCont` and `ControlLifter.ofCont` now reads `noFallthrough`.

- [#13494](https://github.com/leanprover/lean4/pull/13494)
  stops the `repeat` inference handler from reporting `numRegularExits := 0` for break-less bodies. For break-less `repeat` the loop never terminates normally, so `0` looks more accurate semantically, but the loop expression still has type `m Unit` and the do block's continuation after the loop is what carries that type. Reporting `0` makes the elaborator flag that continuation as dead code, yet there is no way for the user to remove it that is also type correct — unless the enclosing do block's monadic result type happens to be `Unit`. Pinning `numRegularExits` at `1` (matching `for ... in`) eliminates those spurious warnings.

- [#13489](https://github.com/leanprover/lean4/pull/13489)
  fixes a bug where the nesting level in Verso Docstrings is forgotten when there's a doc comment with no headers.

- [#13486](https://github.com/leanprover/lean4/pull/13486)
  fixes `inferControlInfoSeq` and `ControlInfo.sequence` to keep aggregating `breaks`/`continues`/`returnsEarly`/`reassigns` past elements whose `ControlInfo` reports `numRegularExits := 0`. Previously the analysis short-circuited at such elements, so any trailing `return`/`break`/`continue` was missing from the inferred info. The elaboration framework only skips subsequent doElems syntactically for top-level `return`/`break`/`continue`; for every other `numRegularExits == 0` case (e.g. a `match`/`if`/`try` whose branches all terminate, or a `repeat` without `break`) the elaborator keeps visiting the continuation and the for/match elaborator then tripped its invariant check with `Early returning ... but the info said there is no early return`. With this change the inferred info matches what the elaborator actually sees, which also removes the need for the `numRegularExits := 1` workaround on `repeat` introduced in #13479.

- [#13477](https://github.com/leanprover/lean4/pull/13477)
  fixes a benchmark regression introduced in #13475: `eqnOptionsExt`
  was using `.async .asyncEnv` asyncMode, which accumulates state in the
  `checked` environment and can block. Switching to `.local` — consistent
  with the neighbouring `eqnsExt` and the other declaration caches in
  `src/Lean/Meta` — restores performance (the
  `build/profile/blocked (unaccounted) wall-clock` bench moves from +33%
  back to baseline). `.local` is safe here because `saveEqnAffectingOptions`
  is only called during top-level `def` elaboration and downstream readers
  see the imported state; modifications on non-main branches are merged
  into the main branch on completion.

- [#13475](https://github.com/leanprover/lean4/pull/13475)
  replaces the eager equation realization that was triggered by
  non-default values of equation-affecting options (like
  `backward.eqns.nonrecursive`) with a `MapDeclarationExtension` that
  stores non-default option values at definition time. These values are
  then restored when equations are lazily realized, so the same equations
  are produced regardless of when generation occurs.

- [#13367](https://github.com/leanprover/lean4/pull/13367)
  removes some cases where `simp` would significantly overrun a timeout.

- [#13447](https://github.com/leanprover/lean4/pull/13447)
  removes the transitional `syntax` declarations for `repeat`, `while`, and `repeat ... until` from `Init.While` and promotes the corresponding `@[builtin_doElem_parser]` defs in `Lean.Parser.Do` from `low` to default priority, making them the canonical parsers.

- [#13442](https://github.com/leanprover/lean4/pull/13442)
  promotes the `repeat`, `while`, and `repeat ... until` parsers from `syntax` declarations in `Init.While` to `@[builtin_doElem_parser]` definitions in `Lean.Parser.Do`, alongside the other do-element parsers. The `while` variants and `repeat ... until` get `@[builtin_macro]` expansions; `repeat` itself gets a `@[builtin_doElem_elab]` so a follow-up can extend it with an option-driven choice between `Loop.mk` and a well-founded `Repeat.mk`.

- [#13437](https://github.com/leanprover/lean4/pull/13437)
  adds a builtin `doElem_control_info` handler for `doRepeat`. It is ineffective as long as we have the macro for `repeat`.

- [#13434](https://github.com/leanprover/lean4/pull/13434)
  names the `repeat` syntax (`doRepeat`) and installs dedicated elaborators for it in both the legacy and new do-elaborators. Both currently expand to `for _ in Loop.mk do ...`, identical to the existing fallback macro in `Init.While`.

- [#13389](https://github.com/leanprover/lean4/pull/13389)
  adds two validation checks to `addInstance` that provide early feedback for common mistakes in instance declarations:

  1. **Non-class instance check**: errors when an instance target type is not a type class. This catches the common mistake of writing `instance` for a plain structure. Previously handled by the `nonClassInstance` linter in Batteries (`Batteries.Tactic.Lint.TypeClass`), this is now checked directly at declaration time.

  2. **Impossible argument check**: errors when an instance has arguments that cannot be inferred by instance synthesis. Specifically, it flags arguments that are not instance-implicit and do not appear in any subsequent instance-implicit argument or in the return type. Previously such instances would be silently accepted but could never be synthesised.

- [#13315](https://github.com/leanprover/lean4/pull/13315)
  fixes `processDefDeriving` to propagate the `meta` attribute to instances derived via delta deriving, so that `deriving BEq` inside a `public meta section` produces a meta instance. Previously the derived `instBEqFoo` was not marked meta, and the LCNF visibility checker rejected meta definitions that used `==` on the alias — this came up while bumping verso to v4.30.0-rc1.

- [#13404](https://github.com/leanprover/lean4/pull/13404)
  fixes #12846, where the new do elaborator produced confusing errors when a do element's continuation had a mismatched monadic result type. The errors were misleading both in location (e.g., pointing at the value of `let x ← value` rather than the `let` keyword) and in content (e.g., mentioning `PUnit.unit` which the user never wrote).

- [#13420](https://github.com/leanprover/lean4/pull/13420)
  fixes a panic when `coinductive` predicates are defined inside macro scopes where constructor names carry macro scopes. The existing guard only checked the declaration name for macro scopes, missing the case where constructor identifiers are generated inside a macro quotation and thus carry macro scopes. This caused `removeFunctorPostfixInCtor` to panic on `Name.num` components from macro scope encoding.

- [#13413](https://github.com/leanprover/lean4/pull/13413)
  adds an internal `skip` syntax for do blocks, intended for use by the `if` and `unless` elaborators to replace `pure PUnit.unit` in implicit else branches. This gives the elaborator a dedicated syntax node to attach better error messages and location info to, rather than synthesizing `pure PUnit.unit` which leaks internal details into user-facing errors.

- [#13391](https://github.com/leanprover/lean4/pull/13391)
  adds level instantiation and normalization in `getDecLevel` and `getDecLevel?` before calling `decLevel`.

- [#13395](https://github.com/leanprover/lean4/pull/13395)
  makes the `deriving Inhabited` handler for `structure`s be able to inherit `Inhabited` instances from structure parents, using the same mechanism as for class parents. This fixes a regression introduced by #9815, which lost the ability to apply `Inhabited` instances for parents represented as subobject fields. With this PR, now it works for all parents in the hierarchy.

- [#13399](https://github.com/leanprover/lean4/pull/13399)
  fixes #12827, where hovering over `for` loop variables `x` and `h` in `for h : x in xs do` showed no type information in the new do elaborator. The fix adds `Term.addLocalVarInfo` calls for the loop variable and membership proof binder after they are introduced by `withLocalDeclsD` in `elabDoFor`.

- [#13397](https://github.com/leanprover/lean4/pull/13397)
  improves error reporting when the `do` elaborator produces an ill-formed expression that fails `checkedAssign` in `withDuplicableCont`. Previously the failure was silently discarded, making it hard to diagnose bugs in the `do` elaborator. Now a descriptive error is thrown showing the join point RHS and the metavariable it failed to assign to.

- [#13396](https://github.com/leanprover/lean4/pull/13396)
  fixes #12768, where the new `do` elaborator produced a "declaration has free variables" kernel error when the bind continuation's result type was definitionally but not syntactically independent of the bound variable. The fix moves creation of the result type metavariable before `withLocalDecl`, so the unifier must reduce away the dependency.

- [#13325](https://github.com/leanprover/lean4/pull/13325)
  adds warnings when registering `@[simp]` theorems whose left-hand side has a problematic head symbol in the discrimination tree:

  - **Variable head** (`.star` key): The theorem will be tried on every `simp` step, which can be expensive. The warning notes this may be acceptable for `local` or `scoped` simp lemmas. Controlled by `warning.simp.varHead` (default: `true`).
  - **Unrecognized head** (`.other` key, e.g. a lambda expression): The theorem is unlikely to ever be applied by `simp`. Controlled by `warning.simp.otherHead` (default: `true`).

- [#13390](https://github.com/leanprover/lean4/pull/13390)
  changes the linear BEq derivation strategy to use `Nat.decEq` instead of `decEq` when comparing constructor indices. Since constructor indices are always `Nat`, using `Nat.decEq` directly is more appropriate because it is `@[reducible]`, whereas the generic `decEq` is only semireducible and does not unfold at `.reducible` transparency. This makes the generated code more transparent-friendly.

- [#13356](https://github.com/leanprover/lean4/pull/13356)
  upstreams environment linters of batteries to core lean.

- [#13360](https://github.com/leanprover/lean4/pull/13360)
  fixes #13268 where `local macro` (and other local declarations) with compound names of depth ≥ 3 would silently lose their local entries.

- [#13374](https://github.com/leanprover/lean4/pull/13374)
  fixes `SizeOf` instance generation for public inductive types that have
  private constructors. The spec theorem proof construction needs to unfold
  `_sizeOf` helper functions which may not be exposed in the public view, so
  we use `withoutExporting` for the proof construction and type check.

- [#13239](https://github.com/leanprover/lean4/pull/13239)
  fixes an issue where `(builtin_)initialize` inside `module` would not allow referencing private defs in its type unless explicitly prefixed with `private`.

- [#9815](https://github.com/leanprover/lean4/pull/9815)
  changes the `Inhabited` deriving handler for `structure` types to use default field values when present; this ensures that `{}` and `default` are interchangeable when all fields have default values. The handler effectively uses `by refine' {..} <;> exact default` to construct the inhabitant. (Note: when default field values cannot be resolved, they are ignored, as usual for ellipsis mode.)

- [#13318](https://github.com/leanprover/lean4/pull/13318)
  adds a check for OS-forbidden names and characters in module names.  This implements the functionality of `modulesOSForbidden` linter of mathlib.

- [#13262](https://github.com/leanprover/lean4/pull/13262)
  extends Lean's syntax to allow explicit universe levels in expressions such as `e.f.{u,v}`, `(f e).g.{u}`, and `e |>.f.{u,v} x y z`. It fixes a bug where universe levels would be attributed to the wrong expression; for example `x.f.{u}` would be interpreted as `x.{u}.f`. It also changes the syntax of top-level declarations to not allow space between the identifier and the universe level list, and it fixes a bug in the `checkWsBefore` parser where it would not detect whitespace across `optional` parsers.

- [#13332](https://github.com/leanprover/lean4/pull/13332)
  fixes universe unification for `for` loops with `mut` variables whose types span multiple implicit universes. The old approach used `ensureHasType (mkSort mi.u.succ)` per variable, which generated constraints like `max (?u+1) (?v+1) =?= ?u+1` that the universe solver cannot decompose. The new approach uses `getDecLevel`/`isLevelDefEq` on the decremented level, producing `max ?u ?v =?= ?u` which `solveSelfMax` handles directly.

- [#13229](https://github.com/leanprover/lean4/pull/13229)
  wraps the top-level command parser with `withPosition` to enforce indentation in `by` blocks, combined with an empty-by fallback for better error messages.

- [#13320](https://github.com/leanprover/lean4/pull/13320)
  changes the auto-generated `sizeOf` definitions to be not
  exposed and the `sizeOf_spec` theorem to be not marked `[defeq]`.

- [#13311](https://github.com/leanprover/lean4/pull/13311)
  adds an optional `markMeta : Bool := false` parameter to `addAndCompile`, so that callers can propagate the `meta` marking without manually splitting into `addDecl` + `markMeta` + `compileDecl`.

- [#13319](https://github.com/leanprover/lean4/pull/13319)
  amends #13317 to suggest `:= (rfl)` as the recommended way to avoid a theorem to be automatically marked `[defeq]`, for consistency with existing documentation. Rationale: the special treatment of `:= rfl` is based on syntax, not the proof term, so it’s appropriate to use different syntax. And also I like the way it reads like a “muted whisper of `rfl`”.

- [#13223](https://github.com/leanprover/lean4/pull/13223)
  adds a warning preventing a user from applying global attribute using `... in ...`, e.g.
  ```lean4
  theorem a : True := trivial
  attribute [simp] a in
  def b : True := a
  ```

- [#13317](https://github.com/leanprover/lean4/pull/13317)
  adds an opt-in linter (`set_option simp.rfl.checkTransparency true`) that warns when a `rfl` simp theorem's LHS and RHS are not definitionally equal at `.instances` transparency. Bad rfl-simp theorems — those that only hold at higher transparency — create problems throughout the system because `simp` and `dsimp` operate at restricted transparency. The linter suggests two fixes: use `id rfl` as the proof (to remove the `rfl` status), or mark relevant constants as `[implicit_reducible]`.

- [#13304](https://github.com/leanprover/lean4/pull/13304)
  makes the delta-deriving handler create `theorem` declarations instead of `def` declarations when the instance type is a `Prop`. Previously, `deriving instance Nonempty for Foo` would always create a `def`, which is inconsistent with the behavior of a handwritten `instance` declaration.

- [#13281](https://github.com/leanprover/lean4/pull/13281)
  marks any exposed (non-private) auxiliary match declaration as `[implicit_reducible]`. This is essential when the outer declaration is marked as `instance_reducible` — without it, reduction is blocked at the match auxiliary. We do not inherit the attribute from the parent declaration because match auxiliary declarations are reused across definitions, and the reducibility setting of the parent can change independently. This change prepares for implementing the TODO at `ExprDefEq.lean:465`, which would otherwise cause too many failures requiring manual `[implicit_reducible]` annotations on match declarations whose names are not necessarily derived from the outer function.

- [#13280](https://github.com/leanprover/lean4/pull/13280)
  adds a new option `backward.isDefEq.respectTransparency.types` that controls the transparency used when checking whether the type of a metavariable matches the type of the term being assigned to it during `checkTypesAndAssign`. Previously, this check always bumped transparency to `.default` (via `withInferTypeConfig`), which is overly permissive. The new option uses `.instances` transparency instead (via `withImplicitConfig`), matching the behavior already used for implicit arguments.

- [#13266](https://github.com/leanprover/lean4/pull/13266)
  changes the counter-example accumulator in the match compiler from
  a `List` (built with cons, producing reverse order) to an `Array` (built
  with push, preserving declaration order). Missing cases are now reported in
  the order constructors appear in the inductive type definition.

- [#13243](https://github.com/leanprover/lean4/pull/13243)
  changes elaboration of structure instance notation when used in patterns (e.g. `s matches { x := 1, y := [] }`) so that the structure's default values are not used to elaborate the pattern. The motivation is that default values frequently lead to surprisingly over-specific patterns. It will now report "field missing" errors. The error can be suppressed using `{ x := 1, .. }` ellipsis notation, which has the same behavior as before. The pretty printer is also modified to stay in sync with this feature. **Breaking change:** patterns using structure instance notation may need missing fields or a `..` added, as appropriate.

- [#13195](https://github.com/leanprover/lean4/pull/13195)
  adds support for marking options as deprecated. When a deprecated option is used via `set_option`, a warning is emitted (controlled by `linter.deprecated.options`).

- [#13255](https://github.com/leanprover/lean4/pull/13255)
  adds support for let configuration options (`(eq := h)`, `+nondep`, `+usedOnly`, `+zeta`) in `do` block `let` and `have` declarations, matching the behavior available in term-level `let`/`have`. Configuration options are rejected with `let mut` since they are incompatible with mutable bindings. `+postponeValue` and `+generalize` are also rejected in `do` blocks.

- [#13250](https://github.com/leanprover/lean4/pull/13250)
  extends the `doLet`, `doLetElse`, `doLetArrow`, and `doHave` parsers to accept `letConfig` (e.g. `(eq := h)`, `+nondep`, `+usedOnly`, `+zeta`), matching the syntax of term-level `let`/`have`. The elaborators are adjusted to handle the shifted syntax indices but do not yet process the configuration; that will be done in a follow-up PR after stage0 is updated, allowing the use of proper quotation patterns.

- [#13245](https://github.com/leanprover/lean4/pull/13245)
  extends Lean syntax for dotted function notation (`.f`) to add support for explicit mode (`@.f`), explicit universes (`.f.{u,v}`), and both simultaneously (`@.f.{u,v}`). This also includes a fix for a bug involving overloaded functions, where it used to give erroneous deprecation warnings about declarations that the function did not elaborate to.

- [#13232](https://github.com/leanprover/lean4/pull/13232)
  fixes a panic when compiling mutually recursive definitions that use `casesOn` on indexed inductive types (e.g. `Vect`). The `splitMatchOrCasesOn` function in `WF.Unfold` asserted `matcherInfo.numDiscrs = 1`, but for indexed types the casesOn recursor has multiple discriminants (indices + major premise). The fix uses the last discriminant (the major premise) and lets the `cases` tactic handle index discriminants automatically.

- [#13002](https://github.com/leanprover/lean4/pull/13002)
  adds a `deprecated_module` command that marks the current module as deprecated. When another module imports a deprecated module, a warning is emitted during elaboration suggesting replacement imports.

- [#13205](https://github.com/leanprover/lean4/pull/13205)
  fixes `FirstTokens.seq (.optTokens s) .unknown` to return `.unknown`. This occurs e.g. when an optional (with first tokens `.optTokens s`) is followed by a parser category (with first tokens `.unknown`). Previously `FirstTokens.seq` returned `.optTokens s`, ignoring the fact that the optional may be empty and then the parser category may have any first token. The correct behavior here is to return `.unknown`, which indicates that the first token may be anything.

- [#13220](https://github.com/leanprover/lean4/pull/13220)
  adds `checkSystem` calls to several code paths that can run for
  extended periods without checking for cancellation, heartbeat limits, or
  stack overflow. This improves responsiveness of the cancellation mechanism
  in the language server.

- [#13108](https://github.com/leanprover/lean4/pull/13108)
  adds a `deprecated_syntax` command that marks syntax kinds as deprecated. When deprecated syntax is elaborated (in terms, tactics, or commands), a linter warning is emitted. The warning is also emitted during quotation precheck when a macro definition uses deprecated syntax in its expansion.

- [#13219](https://github.com/leanprover/lean4/pull/13219)
  moves `hasAssignableMVar`, `hasAssignableLevelMVar`, and `isLevelMVarAssignable` from `MetavarContext.lean` to a new `Lean.Meta.HasAssignableMVar` module, changing them from generic `[Monad m] [MonadMCtx m]` functions to `MetaM` functions. This enables adding `checkSystem` calls in the recursive traversal, which ensures cancellation and heartbeat checks happen during what can be a very expensive computation.

````

# Library

```markdown

- [#13863](https://github.com/leanprover/lean4/pull/13863)
  changes the e-matching annotations on `BitVec` to avoid automatically going from `getMsbD` theory to `getLsbD` theory. The key reason being that all lemmas are already duplicated between `getMsbD` and `getLsbD` anyways. Thus, whenever we connect them all lemmas fire in both variants even though usually one is already sufficient. In order to make this possible without reducing proof strength noticeably we introduce two changes:
  1. Write or annotate a few additional `BitVec.getMsbD` lemmas to match the reasoning power of `BitVec.getLsbD`. Most notably `getMsbD_eq_getElem` so `getMsbD` can attempt to convert into `getElem` on its own.
  2. Introduce `grind_pattern getMsbD_eq_getLsbD => x.getMsbD i, x.getLsbD _` such that whenever we have both `getMsbD` and `getLsbD` on the same value in scope we attempt to match them up. We expect that this annotation should *usually* not fire much as most `get*D` can probably be converted into `getElem` and be worked from there.

- [#13850](https://github.com/leanprover/lean4/pull/13850)
  removes the grind annotation that makes `getElem?_pos` trigger whenever `c[i]` is in the e-graph. We do this to avoid reasoning about `c[i]?` just because `c[i]` is available. The trigger for instantiating `getElem?_pos` whenever `c[i]?` is in scope remains in order to nudge grind towards proving or disproving the bounds check.

- [#13689](https://github.com/leanprover/lean4/pull/13689)
  makes the unfolding lemma for `whileM` derivable from a `Lean.Order.MonadTail` instance. The public entry point is `whileM_eq_of_monadTail` in `Init.Internal.Order.While`; the underlying pinning predicate `whileM.Pred` and the conditional `whileM_eq` lemma in `Init.While` are kept module-internal.

- [#13787](https://github.com/leanprover/lean4/pull/13787)
  fixes a small docsting error for `String.split`.

- [#13748](https://github.com/leanprover/lean4/pull/13748)
  fixes premise selection silently dropping relevant premises when the goal was reached via `induction`.

- [#13750](https://github.com/leanprover/lean4/pull/13750)
  refines MePo premise selection so that (1) candidates are restricted to theorems, matching the convention already used by `SineQuaNon` and `SymbolFrequency`, and (2) the result is ordered lexicographically by `(iteration, score)` rather than by score alone.

- [#13747](https://github.com/leanprover/lean4/pull/13747)
  fixes the MePo premise selector returning its lowest-scoring premises instead of its best ones.

- [#13457](https://github.com/leanprover/lean4/pull/13457)
  adds the missing `ByteArray` push and `set!` lemmas that are still carried locally in `ZipForStd.ByteArray` downstream.

- [#13654](https://github.com/leanprover/lean4/pull/13654)
  adds `Dyadic.divAtPrec a b prec`, returning the greatest dyadic with precision at most `prec` which is less than or equal to `a/b` (and `0` when `b = 0`). Mirroring the existing `invAtPrec`, the characterising lemmas `divAtPrec_mul_le` and `lt_divAtPrec_add_inc_mul` are also provided.

- [#13718](https://github.com/leanprover/lean4/pull/13718)
  fixes tests in context_async.lean by removing all the issues with Async.sleep and IO.sleep and improving how ContextAsync.race works.

- [#13567](https://github.com/leanprover/lean4/pull/13567)
  adds Locale and LocaleSymbols for configurable date/time formatting. It also modifies alignedWeekOfMonth and weekOfYear so it contains a parameter to the first of the week.

- [#13565](https://github.com/leanprover/lean4/pull/13565)
  fixes an issue where the missing /etc/localtime caused a failure even when TZ and TZDIR were present.

- [#13675](https://github.com/leanprover/lean4/pull/13675)
  adds a `WallTime` type representing a point in time as nanoseconds since `1970-01-01T00:00:00` local time. It also removes the `sinceUNIXEpoch` and `AssumingUTC` suffixes because `Timestamp` implies UTC, and `WallTime` implies it is based on the WallTime epoch (defined in the comment as `1970-01-01T00:00:00`).

- [#13693](https://github.com/leanprover/lean4/pull/13693)
  generalizes a number of `Vector` lemmas about `++` so that the two appended vectors no longer need to share the same size index: `sum_append`, `prod_append`, their `_nat` / `_int` variants, `flatMap_append`, `unattach_append`, `eraseIdx_append_of_lt_size`, and `eraseIdx_append_of_length_le`.

- [#13521](https://github.com/leanprover/lean4/pull/13521)
  prevents undefined behavior in `readModuleDataParts #[]` on configurations without `LEAN_MMAP`. Previously this would lead to out-of-bounds indexing.

- [#13549](https://github.com/leanprover/lean4/pull/13549)
  makes `readModuleDataParts` report a clearer error if there is insufficient memory to load a module.

- [#13627](https://github.com/leanprover/lean4/pull/13627)
  renames `UInt8.ofNatTruncate` to `UInt8.ofNatClamp`.

- [#13583](https://github.com/leanprover/lean4/pull/13583)
  changes `Invariant`, `StringInvariant`, and `StringSliceInvariant` from `abbrev` to `@[spec_invariant_type, simp, grind =] def`, so that they remain visible as applications of a named constant in proof states (where `SymM` does not unfold `def`s) and can be detected as invariant types by `isSpecInvariantType`. The `@[simp, grind =]` annotations ensure they still unfold on demand under `simp` and `grind`.

- [#13582](https://github.com/leanprover/lean4/pull/13582)
  adds several entailment-related lemmas to `Std.Do.SPred` and `Std.Do.PostCond`, intended for goal-decomposition during program verification proof automation.

- [#12965](https://github.com/leanprover/lean4/pull/12965)
  Introduces new foundations for reasoning about monadic Lean code. Eventually we will port `mvcgen` on top of these new foundations, to make the framework more general and robust.

- [#13546](https://github.com/leanprover/lean4/pull/13546)
  prevents memory exhaustion turning into segfaults when using Lean functions which call into libuv

- [#13511](https://github.com/leanprover/lean4/pull/13511)
  moves Async and Http from Internal to Std

- [#12151](https://github.com/leanprover/lean4/pull/12151)
  introduces the Server module, an Async HTTP/1.1 server.

- [#13400](https://github.com/leanprover/lean4/pull/13400)
  fixes the incorrect name `String.Pos.skipWhile_le` to be `String.Pos.le_skipWhile`.

- [#13398](https://github.com/leanprover/lean4/pull/13398)
  removes private from H1.lean

- [#12146](https://github.com/leanprover/lean4/pull/12146)
  introduces the H1 module, a pure HTTP/1.1 state machine that incrementally parses incoming byte streams and emits response bytes without side effects.

- [#13357](https://github.com/leanprover/lean4/pull/13357)
  is based on a systematic review of all read-only operations on the default containers in core. Where sensible it applies specialize annotations on higher order operations that lack them or borrow annotations on parameters that should morally be borrowed (e.g. the container when iterating over it).

- [#13200](https://github.com/leanprover/lean4/pull/13200)
  adds `prod` (multiplicative fold) for `List`, `Array`, and `Vector`, mirroring the existing `sum` API. Includes basic simp lemmas (`prod_nil`, `prod_cons`, `prod_append`, `prod_singleton`, `prod_reverse`, `prod_push`, `prod_eq_foldl`), Nat-specialized lemmas (`prod_pos_iff_forall_pos_nat`, `prod_eq_zero_iff_exists_zero_nat`, `prod_replicate_nat`), Int-specialized lemmas (`prod_replicate_int`), cross-type lemmas (`prod_toArray`, `prod_toList`), and `Perm.prod_nat` with grind patterns.

- [#13273](https://github.com/leanprover/lean4/pull/13273)
  adds a comprehensive public API for constructing maximally shared
  expression applications and performing beta reduction in the `Sym` framework.
  These functions were previously defined locally in the VC generator and cbv
  tactic, and are needed by downstream `SymM`-based tools.

- [#13155](https://github.com/leanprover/lean4/pull/13155)
  verifies the `String.dropWhile` and `String.takeWhile` functions.

- [#13235](https://github.com/leanprover/lean4/pull/13235)
  uses `std::memcmp` for `ByteArray` `BEq` and `DecidableEq`.

- [#13172](https://github.com/leanprover/lean4/pull/13172)
  adds borrow annotations in `Std.Internal.UV.System`.

```

# Tactics

```markdown

- [#13859](https://github.com/leanprover/lean4/pull/13859)
  fixes a kernel rejection when a user-supplied pre-tactic like `clear` in `sym => mvcgen' with (clear h)` rewrites the local context.

- [#13857](https://github.com/leanprover/lean4/pull/13857)
  implements the `dsimp` tactic for interactive `sym =>` mode. It also adds DSL for declaring `dsimp` variants.

- [#13680](https://github.com/leanprover/lean4/pull/13680)
  makes `mvcgen'` usable as a step inside `sym => …` blocks. Leftover VCs become subgoals for subsequent grind steps; `mvcgen' invariants` works inline, `mvcgen' invariants?` is rejected.

- [#13854](https://github.com/leanprover/lean4/pull/13854)
  implements the syntax for declaring `dsimp` variants for `SymM`.

- [#13793](https://github.com/leanprover/lean4/pull/13793)
  extends the new tactic hints about type-incorrect goals at `instances` transparency with the type checking error message to assist with cases that are more complex than "inadvisable `unfold`".

- [#13636](https://github.com/leanprover/lean4/pull/13636)
  makes `simpa using h` close at **reducible** transparency rather than the ambient (default/semireducible) transparency used previously, making `simpa using h` more predictable under changes to the simp set. The previous behaviour is available as `simpa using! h` (introduced in #13833).

- [#13833](https://github.com/leanprover/lean4/pull/13833)
  adds the `simpa ... using! e` syntax as a parallel form of
  `simpa ... using e`. At present `using!` behaves identically to `using` — both
  close the goal at the ambient (default/semireducible) transparency.

- [#13771](https://github.com/leanprover/lean4/pull/13771)
  adds a new `impossible by t` tactic combinator and wires it into the
  default suggestion set of `try?`.

- [#13825](https://github.com/leanprover/lean4/pull/13825)
  implements a collection of reusable reduction `DSimproc`s (`beta`, `zeta`, `zetaAll`, `dsimpProj`, `dsimpMatch`), exposing them as public so callers can compose them into their own `Methods`, and fixing a few bugs.

- [#13824](https://github.com/leanprover/lean4/pull/13824)
  adds functions for simplifying binders in `Sym.dsimp`.

- [#13823](https://github.com/leanprover/lean4/pull/13823)
  adds the basic infrastructure for a `dsimp` in `SymM`.

- [#13812](https://github.com/leanprover/lean4/pull/13812)
  fixes `mconstructor`, `mleft`, and `mright` failing inside `mhave` blocks (#13691), and `mspecialize` failing after a `mrevert; mintro` round trip. Both cases stem from hypothesis-naming `Expr.mdata` leaking from hypothesis-conjunction leaves into non-leaf positions (an inner target, or the antecedent of an `SPred.imp` target), where downstream pattern matches did not see through it.

- [#13766](https://github.com/leanprover/lean4/pull/13766)
  moves the `evalSuggest` combinator and trace-handler dispatch
  from a hardcoded `match` on syntax kinds to the existing
  `tryTacticElabAttribute` registration mechanism, bringing `try?`'s
  extensibility model in line with normal tactics and interactive `grind`.

- [#13774](https://github.com/leanprover/lean4/pull/13774)
  makes `try?`'s `expandUserTactic` walk the info tree for `TryThisInfo`
  nodes (introduced in #10524) instead of parsing the rendered `Try this:` message
  text. The previous approach scraped lines prefixed with `  [apply] ` from the
  message log, which would break the moment that wire format changed.

- [#13430](https://github.com/leanprover/lean4/pull/13430)
  makes an empty `by` block run `try?` in the background and surface its suggestions, while still producing the usual unsolved-goals diagnostic. The implicit `try?` is informational only — it does not change elaboration behavior beyond emitting messages. Behaviour is controlled by a new option `tactic.tryOnEmptyBy`, disabled by default for now; set it to `true` to opt in. The default may flip in a future release.

- [#13699](https://github.com/leanprover/lean4/pull/13699)
  adds a new `grind` configuration option, `genLocal`, that controls the
  maximum term generation for local theorems (e.g., hypotheses). It defaults to
  `8`, same value as `gen` and applies whenever
  `grind` instantiates a theorem whose origin is local rather than a declaration
  or user-provided term. Since users have little control over the patterns used
  for local theorems, a tighter generation bound is a reasonable default.

- [#13698](https://github.com/leanprover/lean4/pull/13698)
  improves the `grind` diagnostics output so that local hypotheses used
  as E-matching theorems show up with their user-facing names and instantiation
  counters, instead of being silently dropped or reported under an anonymous
  `local.<idx>` identifier.

- [#13644](https://github.com/leanprover/lean4/pull/13644)
  adds an experimental tactic `mvcgen'` that will soon replace `mvcgen`. It has been reimplemented from the ground up using the new `SymM`-based framework for efficient symbolic evaluation and can outperform `mvcgen` by a factor of >100x for some synthetic benchmarks. `mvcgen'` aspires to be feature-complete with `mvcgen`. Known exceptions currently are join point sharing, introduction of local specs and smaller bugs.

- [#13678](https://github.com/leanprover/lean4/pull/13678)
  ensures that one can hover over the function name in fun_induction. Fixes #13673

- [#13665](https://github.com/leanprover/lean4/pull/13665)
  replaces `Meta.mkCongrArg` call sites in `handleProj` and `simplifyAppFn` are replaced with direct `congrArg` constructions that reuse types already in the `Sym` pointer cache. A few stray unqualified `inferType` / `getLevel` / `isDefEq` calls in the same file are also routed through the cached `Sym` equivalents.

- [#13640](https://github.com/leanprover/lean4/pull/13640)
  adds a trace event emitted whenever a `dsimp` (or rfl-only `simp`) rewrite fires
  because of a `[backward_defeq]`-tagged theorem (i.e., one that would not
  have applied without `set_option backward.defeqAttrib.useBackward true`).

- [#13635](https://github.com/leanprover/lean4/pull/13635)
  fixes a `Sym.simp` panic ("unexpected kernel projection term
  during simplification") that triggered when matcher iota-reduction
  exposed kernel `Expr.proj` terms via struct-eta. For example, a `do`
  block with a `for` loop whose state is a tuple, where `Sym.simp`
  unfolds the equational lemma and then descends into a destructuring
  match.

- [#13624](https://github.com/leanprover/lean4/pull/13624)
  fixes a `grind` congruence-table invariant violation that could panic
  when an `ite` branch was internalized lazily (after the condition became `True`
  or `False`) and that branch's equivalence class was later merged with another.

- [#13625](https://github.com/leanprover/lean4/pull/13625)
  fixes a `grind` internal error triggered when `cast` (or `Eq.rec`, `Eq.ndrec`, `Eq.recOn`) is applied to an argument that has not yet been internalized. `pushCastHEqs` was emitting `e ≍ a` before internalizing the args of `e`, so the `rhs` of the heq had no enode and the debug sanity check tripped. The call now runs after the args are internalized.

- [#13623](https://github.com/leanprover/lean4/pull/13623)
  fixes proof construction issues in the `grind` projection propagators.

- [#13622](https://github.com/leanprover/lean4/pull/13622)
  fixes another issue in the `grind` AC invariant checker.

- [#13614](https://github.com/leanprover/lean4/pull/13614)
  fixes the invariant in `grind` AC. equations in the todo queue are not fully simplified.

- [#13612](https://github.com/leanprover/lean4/pull/13612)
  improves the universe unifier used by `SymM`.

- [#13611](https://github.com/leanprover/lean4/pull/13611)
  fixes an assertion failure in `Sym.simp` when simplifying a `have`-expression whose binder type depends on a preceding binder in the telescope.

- [#13368](https://github.com/leanprover/lean4/pull/13368)
  adds infrastructure to help diagnose cases where tactics like `unfold`
  leave the goal in a state that is type-correct only at `.default` transparency,
  causing `rw`/`simp` to fail at `.instances` transparency.

- [#13593](https://github.com/leanprover/lean4/pull/13593)
  disables model-based theory combination (`mbtc`) in `grind`'s `NoopConfig`, which is the base configuration used by the derived tactics `lia`, `linarith`, `cutsat`, `order`, and `ring`. Without this fix, these tactics could engage in wasteful reasoning via theory combination, causing them to run for a long time (or hit the deterministic timeout) on problems they are not designed to solve. With this fix, these tactics fail quickly on out-of-scope problems, as expected.

- [#13590](https://github.com/leanprover/lean4/pull/13590)
  makes `lia` (and `grind`'s arithmetic case-split heuristic) recognize
  implications whose antecedent is an `And` or `Or` of arithmetic predicates as
  relevant case-split candidates. Previously, `Arith.isRelevantPred` only matched
  `Not`, `LE`, `LT`, `Eq`, and `Dvd`. With `splitImp := false` (the default),
  implications `p → q` are added as split candidates only when `p` is
  arith-relevant, so a hypothesis like `(b ≤ e ∧ e < b + c → a ≤ e ∧ e < a + d)`
  was never registered as a candidate. cutsat/lia would then find a satisfying
  assignment for the constraints it had been told about, but that assignment
  would not necessarily satisfy the original implication, yielding the bad
  counterexample reported in #13575.

- [#13585](https://github.com/leanprover/lean4/pull/13585)
  adds a `ringMaxDegree` configuration option (default `1024`) that bounds the maximum degree of polynomials processed by the `grind` ring solver. Equality constraints whose polynomial exceeds this threshold are discarded (with an issue reported once per goal), preventing pathological degree explosion on inputs such as `r ^ (2 ^ 250 - 1)`.

- [#13558](https://github.com/leanprover/lean4/pull/13558)
  adds the option `grind.ematch.diagnostics`, which tracks how E-matching theorem instances depend on each other. When enabled, `grind` records, for every new theorem instance, the set of previous instances whose generated terms participated in the match. This produces a hyper-graph `{thm_1, ..., thm_n} => thm` describing the provenance of each instantiation.

- [#13560](https://github.com/leanprover/lean4/pull/13560)
  fixes a bug in `propagateBetaEqs` (in `Lean.Meta.Tactic.Grind.Beta`)
  where new equalities/terms introduced by beta reduction were added to the goal
  without checking the generation threshold. The generation of the new fact
  is the maximum generation of the lambda, the function `f`, and its
  arguments, plus one. Without the threshold check, beta reduction can
  cascade indefinitely on self-similar lambdas such as
  `(fun b => f (b + 1)) = fun b => f b`, which kept producing
  `f n = f (n + 1)` for every `n`. The fix aggregates argument generations
  before the threshold check and bails out when the resulting generation
  reaches `maxGeneration`.

- [#13301](https://github.com/leanprover/lean4/pull/13301)
  adds a `try? => tac` syntax that runs `evalSuggest` directly on a given tactic, useful for testing the `try?` machinery in isolation. It also adds a server_interactive test (`cancellation_par.lean`) that demonstrates a cancellation bug with parallel tactic combinators.

- [#13532](https://github.com/leanprover/lean4/pull/13532)
  notifies satellite solvers about asserted equalities `lhs = rhs` even though `lhs = rhs` is not internalized in the E-graph (an existing optimization). The notification lets solvers that do not inspect equivalence classes (such as the homomorphism extension) react to asserted equalities directly. It fires before the equivalence-class merge so that solvers that mark `lhs` and `rhs` as their internal terms have them registered before `Solvers.mergeTerms` fires `processNewEq`.

- [#13476](https://github.com/leanprover/lean4/pull/13476)
  refines how the `apply` tactic (and related tactics like `rewrite`) name and tag the remaining subgoals. Assigned metavariables are now filtered out *before* computing subgoal tags. As a consequence, when only one unassigned subgoal remains, it inherits the tag of the input goal instead of being given a fresh suffixed tag.

- [#13474](https://github.com/leanprover/lean4/pull/13474)
  fixes a bug in `sym =>` interactive mode where goals whose metavariable was assigned by `isDefEq` (e.g. via `apply Eq.refl`) were not pruned. `pruneSolvedGoals` previously only filtered out goals flagged as inconsistent, so an already-assigned goal would linger as an unsolved goal. It now also removes goals whose metavariable is already assigned.

- [#13472](https://github.com/leanprover/lean4/pull/13472)
  fixes a bug in `sym =>` interactive mode where satellite solvers (`lia`, `ring`, `linarith`) would throw an internal error if their automatic `intros + assertAll` preprocessing step already closed the goal. Previously, `evalCheck` used `liftAction` which discarded the closure result, so the subsequent `liftGoalM` call failed due to the absence of a main goal. `liftAction` is now split so the caller can distinguish the closed and subgoals cases and skip the solver body when preprocessing already finished the job.

- [#13453](https://github.com/leanprover/lean4/pull/13453)
  fixes a kernel error in `grind` when propagating a `Nat` equality to an order structure whose carrier type is not `Int` (e.g. `Rat`). The auxiliary `Lean.Grind.Order.of_nat_eq` lemma was specialized to `Int`, so the kernel rejected the application when the cast destination differed.

- [#13451](https://github.com/leanprover/lean4/pull/13451)
  fixes a bug in `Sym.introCore.finalize` where the original metavariable was unconditionally assigned via a delayed assignment, even when no binders were introduced. As a result, `Sym.intros` would return `.failed` while the goal metavariable had already been silently assigned, confusing downstream code that relies on `isAssigned` (e.g. VC filters in `mvcgen'`).

- [#13448](https://github.com/leanprover/lean4/pull/13448)
  fixes a regression in `Sym.simp` where rewrite rules whose LHS contains a lambda over a pattern variable (e.g. `∃ x, a = x`) failed to match targets with semantically equivalent structure.

- [#13088](https://github.com/leanprover/lean4/pull/13088)
  wires the `PowIdentity` typeclass (from https://github.com/leanprover/lean4/pull/13086) into the `grind` ring solver's Groebner basis engine.

- [#13086](https://github.com/leanprover/lean4/pull/13086)
  adds a `Lean.Grind.PowIdentity` typeclass stating that `x ^ p = x` for all elements of a commutative semiring, with `p` as an `outParam`.

- [#13289](https://github.com/leanprover/lean4/pull/13289)
  adds the shared infrastructure for arithmetic normalization in `Sym.Arith/`,
  laying the groundwork for both `Sym.simp`'s arith pre-simproc and the eventual
  unification of grind's `CommRing` module.

- [#13272](https://github.com/leanprover/lean4/pull/13272)
  extends the sym canonicalizer to apply reductions (projection, match/ite/cond, Nat
  arithmetic) in all positions, not just inside types. Previously, a value `v` appearing in a
  type `T(v)` could remain unreduced while `T(v)` was normalized, breaking the invariant that
  definitionally equal types are structurally identical after canonicalization.

- [#13271](https://github.com/leanprover/lean4/pull/13271)
  refactors instance canonicalization in the sym canonicalizer to properly handle
  \`Grind.nestedProof\` and \`Grind.nestedDecidable\` markers. Previously, the canonicalizer
  would report an issue when it failed to resynthesize propositional instances that were
  provided by \`grind\` itself or by the user via \`haveI\`. Now, resynthesis failure gracefully
  falls back to the original instance in value positions, while remaining strict inside types.

- [#13202](https://github.com/leanprover/lean4/pull/13202)
  fixes a heartbeat timeout from an environment extension at the end of the file that cannot be avoided by raising the limit.

```

# Compiler

```markdown

- [#13796](https://github.com/leanprover/lean4/pull/13796)
  optimizes `String.compare` to turn it into 1 instead of 2 `memcmp` calls.

- [#13788](https://github.com/leanprover/lean4/pull/13788)
  generates specialized code for invoking `dec` on values whose shape is known. This puts branch prediction pressure off `lean_dec_ref_cold` as the shape of the constructor should now be compiled into the executable.

- [#13669](https://github.com/leanprover/lean4/pull/13669)
  optimizes `lean_dec_ref_cold` by outlining the "freezing cold" path and performing a small microarchitecural optimization. The latter is better as it makes clear to LLVM that we believe the pointer to only use 48 bits.

- [#13545](https://github.com/leanprover/lean4/pull/13545)
  upgrades LLVM from version 19 to version 22. This brings general performance improvements of up to 5% instructions depending on benchmark.

- [#13493](https://github.com/leanprover/lean4/pull/13493)
  ensures that `import` gracefully processes `EINTR` errors from the filesystem.

- [#13464](https://github.com/leanprover/lean4/pull/13464)
  replaces `exit(-1)` with `_exit(-1)` in the forked child branches of `lean_io_process_spawn` (the `chdir` failure and `execvp` failure paths). `exit` flushes inherited C stdio buffers, which share underlying file descriptors with the parent. If the parent had a file handle open with unflushed data, that data would be written to the file in the child and then again when the parent later flushes, resulting in duplicated output. `_exit` skips the stdio flush, so the parent's buffered writes are no longer duplicated into inherited files.

- [#13435](https://github.com/leanprover/lean4/pull/13435)
  fixes a bug in EmitC that can be caused by working with the string literal `"\x01abc"` in
  Lean and causes a C compiler error.

- [#13427](https://github.com/leanprover/lean4/pull/13427)
  fixes two minor bugs in `io.cpp`:
  1. A resource leak in a Windows error path of `Std.Time.Database.Windows.getNextTransition`
  2. A buffer overrun in `IO.appPath` on linux when the executable is a symlink at max path length.

- [#13421](https://github.com/leanprover/lean4/pull/13421)
  fixes an issue in the expand reset reuse pass that causes segfaults in very rare situations.

- [#13409](https://github.com/leanprover/lean4/pull/13409)
   specialize qsort properly onto the lt function

- [#13401](https://github.com/leanprover/lean4/pull/13401)
  adds the option `LEAN_MI_SECURE` to our CMake build. It can be configured with values `0`
  through `4`. Every increment enables additional memory safety mitigations in mimalloc, at the cost
  of 2%-20% instruction count, depending on the benchmark. The option is disabled by default in our
  release builds as most of our users do not use the Lean runtime in security sensitive situations.
  Distributors and organization deploying production Lean code should consider enabling the option as
  a hardening measure. The effects of the various levels can be found at  https://github.com/microsoft/mimalloc/blob/v2.2.7/include/mimalloc/types.h#L56-L60.

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  fixes a heap buffer overflow in `lean_io_prim_handle_read` that was triggered through an
  integer overflow in the size computation of an allocation. In addition it places several checked
  arithmetic operations on all relevant allocation paths to have potential future overflows be turned
  into crashes instead. The offending code now throws an out of memory error instead.

- [#13384](https://github.com/leanprover/lean4/pull/13384)
  fixes a compiler panic when a structure constructor receives a noncomputable instance as an instance-implicit argument.

- [#13234](https://github.com/leanprover/lean4/pull/13234)
  fixes a build issue when Lean is not linked against libuv.

- [#13233](https://github.com/leanprover/lean4/pull/13233)
  fixes runtime build issues when `LEAN_MULTI_THREAD` is not set.

- [#13270](https://github.com/leanprover/lean4/pull/13270)
  adds `Runtime.hold`, which ensures its argument remains alive until the callsite by holding a reference to it. This can be useful for unsafe code (such as an FFI) that relies on a Lean object not being freed until after some point in the program.

- [#13258](https://github.com/leanprover/lean4/pull/13258)
  adds a `Core.checkInterrupted` call in `checkInferTypeCache` on cache miss, allowing cancellation to be detected during large type inference traversals. Previously, `inferTypeImp` could run for >100ms without any interruption check when processing large expressions (e.g. BVDecide proof terms), making IDE cancellation unresponsive.

- [#13242](https://github.com/leanprover/lean4/pull/13242)
  fixes the compiler handling of pattern matching on the `String` constructor to conform to the new `String` representation.

- [#13128](https://github.com/leanprover/lean4/pull/13128)
  fixes the Windows dev build by using `CMAKE_RELATIVE_LIBRARY_OUTPUT_DIRECTORY` instead of the hardcoded `lib/lean` path for the Lake plugin. On Windows, DLLs must be placed next to executables in `bin/`, but the plugin path was hardcoded to `lib/lean`, causing stage0 DLLs to not be found.

```

# Pretty Printing

```markdown

- [#13761](https://github.com/leanprover/lean4/pull/13761)
  fixes an issue where the `pp.universes` option would cause constants with no universes to not use unexpanders or dot notation. For example, `p ↔ q` would pretty print as `Iff p q` even though `Iff` has no universe levels.

- [#13446](https://github.com/leanprover/lean4/pull/13446)
  improves metavariable pretty printing and their hovers in the InfoView. The hovers in the InfoView now include information about specific metavariables — it includes information such as the kind of the metavariable, whether it is a blocked delayed assignment and which metavariables it is blocked on, and the differences in what variables exist the metavariable's local context. Additionally, named metavariables now pretty print with tombstones if they are inaccessible. Delayed assignment pretty printing now more reliably follows chains of assignments to find the pending metavariable.

- [#13438](https://github.com/leanprover/lean4/pull/13438)
  makes the universe level pretty printer instantiate level metavariables when `pp.instantiateMVars` is true.

- [#13030](https://github.com/leanprover/lean4/pull/13030)
  improves pretty printing of level metavariables: they now print with a per-definition index rather than their per-module internal identifiers. Furthermore, `+` is printed uniformly in level expressions with surrounding spaces. **Breaking metaprogramming change:** level pretty printing should use `delabLevel` or `MessageData.ofLevel`; functions such as `format` or `toString` do not have access to the indices, since they are stored in the current metacontext. Absent index information, metavariables print with the raw internal identifier as `?_mvar.nnn`. **Note:** The heartbeat counter also increases quicker due to counting allocations that record level metavariable indices. In some tests we needed to increase `maxHeartbeats` by 20–50% to compensate, without a corresponding slowdown.

```

# Documentation

```markdown

- [#13864](https://github.com/leanprover/lean4/pull/13864)
  updates the pipe operator docstrings for accurracy and helpfulness. Such operators are not idiomatic Haskell, so the old text was incorrect, and it's better to explain the behavior than to reference other languages anyway.

- [#13656](https://github.com/leanprover/lean4/pull/13656)
  documents how to perform an LLVM upgrade.

```

# Server

```markdown

- [#13525](https://github.com/leanprover/lean4/pull/13525)
  adds `FromJson`/`ToJson` instances for `Unit` - encoded as `{}` - and documentation for `FromJson`/`ToJson`.

- [#13260](https://github.com/leanprover/lean4/pull/13260)
  adds server-side support for incremental diagnostics via a new `isIncremental` field on `PublishDiagnosticsParams` that is only used by the language server when clients set `incrementalDiagnosticSupport` in `LeanClientCapabilities`.

- [#13348](https://github.com/leanprover/lean4/pull/13348)
  fixes a bug where tactic auto-completion would produce tactic completion items in the entire trailing whitespace of an empty tactic block. Since #13229 further restricted top-level `by` blocks to be indentation- sensitive, this PR adjusts the logic to only display completion items at a "proper" indentation level.

- [#13257](https://github.com/leanprover/lean4/pull/13257)
  adds test infrastructure and tests for tactic completion in empty `by` blocks.

```

# Lake

```markdown

- [#13949](https://github.com/leanprover/lean4/pull/13949)
  adds a `LAKE_RESTORE_ARTIFACTS` environment variable that overrides the workspace's default `restoreAllArtifacts` configuration, mirroring how `LAKE_ARTIFACT_CACHE` overrides `enableArtifactCache`.

- [#13936](https://github.com/leanprover/lean4/pull/13936)
  fixes an issue where `depPkgs` was not properly set for a transitive dependency that was overriden by a package at a higher level in the dependency graph.

- [#13843](https://github.com/leanprover/lean4/pull/13843)
  makes `lake lint --builtin-lint` import module-system targets at the public (`OLeanLevel.exported`) level instead of `private`. Environment linters now lint the public surface of such modules, matching how downstream consumers see them. Non-module targets retain their previous behaviour (`private` level), and text-linter warnings recorded via `lintLogExt` are preserved across the level change because that extension stores uniform OLean entries.

- [#13563](https://github.com/leanprover/lean4/pull/13563)
  makes `Glob.ofString?` public, allowing removing the last use of `open private` from Mathlib.

- [#13683](https://github.com/leanprover/lean4/pull/13683)
  moves the compiled Lake configurations (e.g., `lakefile.olean`) from the package's `.lake/config` directory to the workspace's `.lake/config`. This removes a potential source contention between workspaces sharing a dependency.

- [#13601](https://github.com/leanprover/lean4/pull/13601)
  changes Lake's module import graph processing to await the completion of any `needs` targets or other extra dependencies (such as cloud releases). This both enables the `needs` targets to influence header processing and prevents them from racing with said processing.

- [#13600](https://github.com/leanprover/lean4/pull/13600)
  fixes a Lake issue where the IR for a `meta import`'s transitive imports was not included in the import artifacts Lake provided to Lean (e.g., via `--setup`). When using the Lake artifact cache, this could produce "missing data file" errors due to absent IR.

- [#13559](https://github.com/leanprover/lean4/pull/13559)
  fixes a race condition in the Lake build monitor's draining of the job queue.

- [#13513](https://github.com/leanprover/lean4/pull/13513)
  extends `lake lint --builtin-lint` to also support text linters (i.e. those using `logLint`/`logLintIf`), in addition to the environment linters added in #13431. Text-linter warnings emitted during the build are persisted into each module's `.olean` via a new `Lean.Linter.lintLogExt` environment extension; `lake lint` re-runs the build for the target modules and reads the entries back, reporting them alongside the environment linter output.

- [#13516](https://github.com/leanprover/lean4/pull/13516)
  adds `namespace Lake` to `Lake.Util.Opaque`, which was missing it. This is technically a breaking change for any code which used `Opaque` without `open Lake`, but hopefully no one was doing that.

- [#13500](https://github.com/leanprover/lean4/pull/13500)
  adds a check for empty `lake build` invocations (as an empty build usually indicates a misconfiguration). Builds with no jobs will now print "Nothing to build." and invocations of `lake build` with no default targets configured will produce a warning. This will be promoted to an error in the future. The warning (and future error) can be suppressed with the new `--allow-empty` CLI option.

- [#13431](https://github.com/leanprover/lean4/pull/13431)
  adds builtin environment linting support to Lake, accessible via `lake lint` flags. It also introduces two builtin linters upstreamed from Mathlib (`defLemma` and `checkUnivs`) and a `builtinLint` package configuration option.

- [#13456](https://github.com/leanprover/lean4/pull/13456)
  adds a type abbreviation `GitRev` to Lake, which is used for `String` values that signify Git revisions. Such revisions may be a SHA1 commit hash, a branch name, or one of Git's more complex specifiers.

- [#13423](https://github.com/leanprover/lean4/pull/13423)
  adds `JobAction.reuse` and `JobAction.unpack` which provide more information captions for what a job is doing for the build monitor. `reuse` is set when using an artifact from the Lake cache, `unpack` is set when unpacking module `.ltar` archives and release (Reservoir or GitHub) archives.

- [#13393](https://github.com/leanprover/lean4/pull/13393)
  adds a basic support for `lake builtin-lint` command that is used to run environment linters and in the future will be extend to deal with the core syntax linters.

- [#13340](https://github.com/leanprover/lean4/pull/13340)
  fixes a Lake issue where library builds would not produce informative errors about bad imports (unlike module builds).

- [#13282](https://github.com/leanprover/lean4/pull/13282)
  introduces `LakefileConfig`, which can be constructed from a Lake configuration file without all the information required to construct a full `Package`. Also, workspaces now have a well-formedness property attached which ensures the workspace indices of its packages match their index in the workspace. Finally, the facet configuration map now has its own type: `FacetConfigMap`.

- [#13277](https://github.com/leanprover/lean4/pull/13277)
  fixes a public-facing typo in a function name: `Module.checkArtifactsExsist` ->  `Module.checkArtifactsExist`.

```

# Other

```markdown

- [#13185](https://github.com/leanprover/lean4/pull/13185)
  adds new incremental module serialization functions that save/load a single module at a time with explicit sharing via dep regions and compactor state, generalizing the existing batch saveModuleDataParts API.

- [#13740](https://github.com/leanprover/lean4/pull/13740)
  extends `lake shake --explain` to also cover reasons for keeping imports that go beyond direct references, such as shake annotations.

- [#13530](https://github.com/leanprover/lean4/pull/13530)
  adds a `trace.profiler.serve` option that, when enabled, serves the Firefox Profiler-compatible profile JSON on an ephemeral `127.0.0.1` port and opens `https://profiler.firefox.com/from-url/...` in the user's default browser, à la `samply`. The server shuts down once the profile has been fetched.

- [#13630](https://github.com/leanprover/lean4/pull/13630)
  fixes an "Unknown constant" error when `set_option diagnostics true` is enabled in module mode under a `public section`. Diagnostic output may reference private declarations such as `_match_*` and `_sparseCasesOn_*` that are recorded in unfold counters; constructing the message previously failed because the environment was in exporting mode and could not resolve those names. The diagnostic-printing paths in `Lean.Meta.Diagnostics.reportDiag` and `Lean.Meta.Tactic.Simp.Diagnostics.reportDiag` now run under `withoutExporting`.

- [#13589](https://github.com/leanprover/lean4/pull/13589)
  ensures that the `lean --error=tag` flag actually sets a non-zero exit code on promoted errors.

- [#13553](https://github.com/leanprover/lean4/pull/13553)
  fixes a typo in the error message thrown by `runInitAttrs` when initializer execution has not been enabled. The message previously referred to `enableInitializerExecution` (singular), but the actual function is `enableInitializersExecution` (plural).

- [#13520](https://github.com/leanprover/lean4/pull/13520)
  extends the `grind` homomorphism demo with predicates to be applied atoms.

- [#13499](https://github.com/leanprover/lean4/pull/13499)
  fixes the architecture detection for `leantar` on Linux aarch64, ensuring it is properly bundled with Lean.

- [#13497](https://github.com/leanprover/lean4/pull/13497)
  adds an example for the Lean hackathon in Paris. It demonstrates how users can implement https://hackmd.io/Qd0nkWdzQImVe7TDGSAGbA

- [#13132](https://github.com/leanprover/lean4/pull/13132)
  adds a `linter.redundantVisibility` option (default `true`) that warns
  when a visibility modifier has no effect because it matches the default for the
  current context:

  - `private` outside a `public section` in a `module` file, where declarations
    are already module-scoped by default
  - `public` in a non-`module` file or inside a `public section`, where
    declarations are already public by default

- [#13211](https://github.com/leanprover/lean4/pull/13211)
  adds an `unlock_limits` command that sets `maxHeartbeats`, `maxRecDepth`, and `synthInstance.maxHeartbeats` to 0, disabling all core resource limits. Also makes `maxRecDepth 0` mean "no limit" (matching the existing behavior of `maxHeartbeats 0`).

- [#13226](https://github.com/leanprover/lean4/pull/13226)
  updates `release_checklist.py` to handle the `CACHE STRING ""` suffix on CMake version variables. The `CACHE STRING` format was introduced in the `releases/v4.30.0` branch, but the script's parsing wasn't updated to match, causing false failures.

```
