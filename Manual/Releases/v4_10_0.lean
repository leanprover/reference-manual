/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.10.0 (2024-07-31)" =>
%%%
tag := "release-v4.10.0"
file := "v4.10.0"
%%%

````markdown
### Language features, tactics, and metaprograms

* `split` tactic:
  * [#4401](https://github.com/leanprover/lean4/pull/4401) improves the strategy `split` uses to generalize discriminants of matches and adds `trace.split.failure` trace class for diagnosing issues.

* `rw` tactic:
  * [#4385](https://github.com/leanprover/lean4/pull/4385) prevents the tactic from claiming pre-existing goals are new subgoals.
  * [dac1da](https://github.com/leanprover/lean4/commit/dac1dacc5b39911827af68247d575569d9c399b5) adds configuration for ordering new goals, like for `apply`.

* `simp` tactic:
  * [#4430](https://github.com/leanprover/lean4/pull/4430) adds `dsimproc`s for `if` expressions (`ite` and `dite`).
  * [#4434](https://github.com/leanprover/lean4/pull/4434) improves heuristics for unfolding. Equational lemmas now have priorities where more-specific equationals lemmas are tried first before a possible catch-all.
  * [#4481](https://github.com/leanprover/lean4/pull/4481) fixes an issue where function-valued `OfNat` numeric literals would become denormalized.
  * [#4467](https://github.com/leanprover/lean4/pull/4467) fixes an issue where dsimp theorems might not apply to literals.
  * [#4484](https://github.com/leanprover/lean4/pull/4484) fixes the source position for the warning for deprecated simp arguments.
  * [#4258](https://github.com/leanprover/lean4/pull/4258) adds docstrings for `dsimp` configuration.
  * [#4567](https://github.com/leanprover/lean4/pull/4567) improves the accuracy of used simp lemmas reported by `simp?`.
  * [fb9727](https://github.com/leanprover/lean4/commit/fb97275dcbb683efe6da87ed10a3f0cd064b88fd) adds (but does not implement) the simp configuration option `implicitDefEqProofs`, which will enable including `rfl`-theorems in proof terms.
* `omega` tactic:
  * [#4360](https://github.com/leanprover/lean4/pull/4360) makes the tactic generate error messages lazily, improving its performance when used in tactic combinators.
* `bv_omega` tactic:
  * [#4579](https://github.com/leanprover/lean4/pull/4579) works around changes to the definition of `Fin.sub` in this release.
* [#4490](https://github.com/leanprover/lean4/pull/4490) sets up groundwork for a tactic index in generated documentation, as there was in Lean 3. See PR description for details.

* **Commands**
  * [#4370](https://github.com/leanprover/lean4/pull/4370) makes the `variable` command fully elaborate binders during validation, fixing an issue where some errors would be reported only at the next declaration.
  * [#4408](https://github.com/leanprover/lean4/pull/4408) fixes a discrepancy in universe parameter order between `theorem` and `def` declarations.
  * [#4493](https://github.com/leanprover/lean4/pull/4493) and
    [#4482](https://github.com/leanprover/lean4/pull/4482) fix a discrepancy in the elaborators for `theorem`, `def`, and `example`,
    making `Prop`-valued `example`s and other definition commands elaborate like `theorem`s.
  * [8f023b](https://github.com/leanprover/lean4/commit/8f023b85c554186ae562774b8122322d856c674e), [3c4d6b](https://github.com/leanprover/lean4/commit/3c4d6ba8648eb04d90371eb3fdbd114d16949501) and [0783d0](https://github.com/leanprover/lean4/commit/0783d0fcbe31b626fbd3ed2f29d838e717f09101) change the `#reduce` command to be able to control what gets reduced.
    For example, `#reduce (proofs := true) (types := false) e` reduces both proofs and types in the expression `e`.
    By default, neither proofs or types are reduced.
  * [#4489](https://github.com/leanprover/lean4/pull/4489) fixes an elaboration bug in `#check_tactic`.
  * [#4505](https://github.com/leanprover/lean4/pull/4505) adds support for `open _root_.<namespace>`.

* **Options**
  * [#4576](https://github.com/leanprover/lean4/pull/4576) adds the `debug.byAsSorry` option. Setting `set_option debug.byAsSorry true` causes all `by ...` terms to elaborate as `sorry`.
  * [7b56eb](https://github.com/leanprover/lean4/commit/7b56eb20a03250472f4b145118ae885274d1f8f7) and [d8e719](https://github.com/leanprover/lean4/commit/d8e719f9ab7d049e423473dfc7a32867d32c856f) add the `debug.skipKernelTC` option. Setting `set_option debug.skipKernelTC true` turns off kernel typechecking. This is meant for temporarily working around kernel performance issues, and it compromises soundness since buggy tactics may produce invalid proofs, which will not be caught if this option is set to true.

* [#4301](https://github.com/leanprover/lean4/pull/4301)
  adds a linter to flag situations where a local variable's name is one of
  the argumentless constructors of its type. This can arise when a user either
  doesn't open a namespace or doesn't add a dot or leading qualifier, as
  in the following:

  ```lean
  inductive Tree (α : Type) where
    | leaf
    | branch (left : Tree α) (val : α) (right : Tree α)

  def depth : Tree α → Nat
    | leaf => 0
  ```

  With this linter, the `leaf` pattern is highlighted as a local
  variable whose name overlaps with the constructor `Tree.leaf`.

  The linter can be disabled with `set_option linter.constructorNameAsVariable false`.

  Additionally, the error message that occurs when a name in a pattern that takes arguments isn't valid now suggests similar names that would be valid. This means that the following definition:

  ```lean
  def length (list : List α) : Nat :=
    match list with
    | nil => 0
    | cons x xs => length xs + 1
  ```

  now results in the following warning:

  ```
  warning: Local variable 'nil' resembles constructor 'List.nil' - write '.nil' (with a dot) or 'List.nil' to use the constructor.
  note: this linter can be disabled with `set_option linter.constructorNameAsVariable false`
  ```

  and error:

  ```
  invalid pattern, constructor or constant marked with '[match_pattern]' expected

  Suggestion: 'List.cons' is similar
  ```

* **Metaprogramming**
  * [#4454](https://github.com/leanprover/lean4/pull/4454) adds public `Name.isInternalDetail` function for filtering declarations using naming conventions for internal names.

* **Other fixes or improvements**
  * [#4416](https://github.com/leanprover/lean4/pull/4416) sorts the output of `#print axioms` for determinism.
  * [#4528](https://github.com/leanprover/lean4/pull/4528) fixes error message range for the cdot focusing tactic.

### Language server, widgets, and IDE extensions

* [#4443](https://github.com/leanprover/lean4/pull/4443) makes the watchdog be more resilient against badly behaving clients.

### Pretty printing

* [#4433](https://github.com/leanprover/lean4/pull/4433) restores fallback pretty printers when context is not available, and documents `addMessageContext`.
* [#4556](https://github.com/leanprover/lean4/pull/4556) introduces `pp.maxSteps` option and sets the default value of `pp.deepTerms` to `false`. Together, these keep excessively large or deep terms from overwhelming the Infoview.

### Library
* [#4560](https://github.com/leanprover/lean4/pull/4560) splits `GetElem` class into `GetElem` and `GetElem?`.
  This enables removing `Decidable` instance arguments from `GetElem.getElem?` and `GetElem.getElem!`, improving their rewritability.
  See the docstrings for these classes for more information.
* `Array`
  * [#4389](https://github.com/leanprover/lean4/pull/4389) makes `Array.toArrayAux_eq` be a `simp` lemma.
  * [#4399](https://github.com/leanprover/lean4/pull/4399) improves robustness of the proof for `Array.reverse_data`.
* `List`
  * [#4469](https://github.com/leanprover/lean4/pull/4469) and [#4475](https://github.com/leanprover/lean4/pull/4475) improve the organization of the `List` API.
  * [#4470](https://github.com/leanprover/lean4/pull/4470) improves the `List.set` and `List.concat` API.
  * [#4472](https://github.com/leanprover/lean4/pull/4472) upstreams lemmas about `List.filter` from Batteries.
  * [#4473](https://github.com/leanprover/lean4/pull/4473) adjusts `@[simp]` attributes.
  * [#4488](https://github.com/leanprover/lean4/pull/4488) makes `List.getElem?_eq_getElem` be a simp lemma.
  * [#4487](https://github.com/leanprover/lean4/pull/4487) adds missing `List.replicate` API.
  * [#4521](https://github.com/leanprover/lean4/pull/4521) adds lemmas about `List.map`.
  * [#4500](https://github.com/leanprover/lean4/pull/4500) changes `List.length_cons` to use `as.length + 1` instead of `as.length.succ`.
  * [#4524](https://github.com/leanprover/lean4/pull/4524) fixes the statement of `List.filter_congr`.
  * [#4525](https://github.com/leanprover/lean4/pull/4525) changes binder explicitness in `List.bind_map`.
  * [#4550](https://github.com/leanprover/lean4/pull/4550) adds `maximum?_eq_some_iff'` and `minimum?_eq_some_iff?`.
* [#4400](https://github.com/leanprover/lean4/pull/4400) switches the normal forms for indexing `List` and `Array` to `xs[n]` and `xs[n]?`.
* `HashMap`
  * [#4372](https://github.com/leanprover/lean4/pull/4372) fixes linearity in `HashMap.insert` and `HashMap.erase`, leading to a 40% speedup in a replace-heavy workload.
* `Option`
  * [#4403](https://github.com/leanprover/lean4/pull/4403) generalizes type of `Option.forM` from `Unit` to `PUnit`.
  * [#4504](https://github.com/leanprover/lean4/pull/4504) remove simp attribute from `Option.elim` and instead adds it to individual reduction lemmas, making unfolding less aggressive.
* `Nat`
  * [#4242](https://github.com/leanprover/lean4/pull/4242) adds missing theorems for `n + 1` and `n - 1` normal forms.
  * [#4486](https://github.com/leanprover/lean4/pull/4486) makes `Nat.min_assoc` be a simp lemma.
  * [#4522](https://github.com/leanprover/lean4/pull/4522) moves `@[simp]` from `Nat.pred_le` to `Nat.sub_one_le`.
  * [#4532](https://github.com/leanprover/lean4/pull/4532) changes various `Nat.succ n` to `n + 1`.
* `Int`
  * [#3850](https://github.com/leanprover/lean4/pull/3850) adds complete div/mod simprocs for `Int`.
* `String`/`Char`
  * [#4357](https://github.com/leanprover/lean4/pull/4357) make the byte size interface be `Nat`-valued with functions `Char.utf8Size` and `String.utf8ByteSize`.
  * [#4438](https://github.com/leanprover/lean4/pull/4438) upstreams `Char.ext` from Batteries and adds some `Char` documentation to the manual.
* `Fin`
  * [#4421](https://github.com/leanprover/lean4/pull/4421) adjusts `Fin.sub` to be more performant in definitional equality checks.
* `Prod`
  * [#4526](https://github.com/leanprover/lean4/pull/4526) adds missing `Prod.map` lemmas.
  * [#4533](https://github.com/leanprover/lean4/pull/4533) fixes binder explicitness in lemmas.
* `BitVec`
  * [#4428](https://github.com/leanprover/lean4/pull/4428) adds missing `simproc` for `BitVec` equality.
  * [#4417](https://github.com/leanprover/lean4/pull/4417) adds `BitVec.twoPow` and lemmas, toward bitblasting multiplication for LeanSAT.
* `Std` library
  * [#4499](https://github.com/leanprover/lean4/pull/4499) introduces `Std`, a library situated between `Init` and `Lean`, providing functionality not in the prelude both to Lean's implementation and to external users.
* **Other fixes or improvements**
  * [#3056](https://github.com/leanprover/lean4/pull/3056) standardizes on using `(· == a)` over `(a == ·)`.
  * [#4502](https://github.com/leanprover/lean4/pull/4502) fixes errors reported by running the library through the the Batteries linters.

### Lean internals

* [#4391](https://github.com/leanprover/lean4/pull/4391) makes `getBitVecValue?` recognize `BitVec.ofNatLt`.
* [#4410](https://github.com/leanprover/lean4/pull/4410) adjusts `instantiateMVars` algorithm to zeta reduce `let` expressions while beta reducing instantiated metavariables.
* [#4420](https://github.com/leanprover/lean4/pull/4420) fixes occurs check for metavariable assignments to also take metavariable types into account.
* [#4425](https://github.com/leanprover/lean4/pull/4425) fixes `forEachModuleInDir` to iterate over each Lean file exactly once.
* [#3886](https://github.com/leanprover/lean4/pull/3886) adds support to build Lean core oleans using Lake.
* **Defeq and WHNF algorithms**
  * [#4387](https://github.com/leanprover/lean4/pull/4387) improves performance of `isDefEq` by eta reducing lambda-abstracted terms during metavariable assignments, since these are beta reduced during metavariable instantiation anyway.
  * [#4388](https://github.com/leanprover/lean4/pull/4388) removes redundant code in `isDefEqQuickOther`.
* **Typeclass inference**
  * [#4530](https://github.com/leanprover/lean4/pull/4530) fixes handling of metavariables when caching results at `synthInstance?`.
* **Elaboration**
  * [#4426](https://github.com/leanprover/lean4/pull/4426) makes feature where the "don't know how to synthesize implicit argument" error reports the name of the argument more reliable.
  * [#4497](https://github.com/leanprover/lean4/pull/4497) fixes a name resolution bug for generalized field notation (dot notation).
  * [#4536](https://github.com/leanprover/lean4/pull/4536) blocks the implicit lambda feature for `(e :)` notation.
  * [#4562](https://github.com/leanprover/lean4/pull/4562) makes it be an error for there to be two functions with the same name in a `where`/`let rec` block.
* Recursion principles
  * [#4549](https://github.com/leanprover/lean4/pull/4549) refactors `findRecArg`, extracting `withRecArgInfo`.
    Errors are now reported in parameter order rather than the order they are tried (non-indices are tried first).
    For every argument, it will say why it wasn't tried, even if the reason is obvious (e.g. a fixed prefix or is `Prop`-typed, etc.).
* Porting core C++ to Lean
  * [#4474](https://github.com/leanprover/lean4/pull/4474) takes a step to refactor `constructions` toward a future port to Lean.
  * [#4498](https://github.com/leanprover/lean4/pull/4498) ports `mk_definition_inferring_unsafe` to Lean.
  * [#4516](https://github.com/leanprover/lean4/pull/4516) ports `recOn` construction to Lean.
  * [#4517](https://github.com/leanprover/lean4/pull/4517), [#4653](https://github.com/leanprover/lean4/pull/4653), and [#4651](https://github.com/leanprover/lean4/pull/4651) port `below` and `brecOn` construction to Lean.
* Documentation
  * [#4501](https://github.com/leanprover/lean4/pull/4501) adds a more-detailed docstring for `PersistentEnvExtension`.
* **Other fixes or improvements**
  * [#4382](https://github.com/leanprover/lean4/pull/4382) removes `@[inline]` attribute from `NameMap.find?`, which caused respecialization at each call site.
  * [5f9ded](https://github.com/leanprover/lean4/commit/5f9dedfe5ee9972acdebd669f228f487844a6156) improves output of `trace.Elab.snapshotTree`.
  * [#4424](https://github.com/leanprover/lean4/pull/4424) removes "you might need to open '{dir}' in your editor" message that is now handled by Lake and the VS Code extension.
  * [#4451](https://github.com/leanprover/lean4/pull/4451) improves the performance of `CollectMVars` and `FindMVar`.
  * [#4479](https://github.com/leanprover/lean4/pull/4479) adds missing `DecidableEq` and `Repr` instances for intermediate structures used by the `BitVec` and `Fin` simprocs.
  * [#4492](https://github.com/leanprover/lean4/pull/4492) adds tests for a previous `isDefEq` issue.
  * [9096d6](https://github.com/leanprover/lean4/commit/9096d6fc7180fe533c504f662bcb61550e4a2492) removes `PersistentHashMap.size`.
  * [#4508](https://github.com/leanprover/lean4/pull/4508) fixes `@[implemented_by]` for functions defined by well-founded recursion.
  * [#4509](https://github.com/leanprover/lean4/pull/4509) adds additional tests for `apply?` tactic.
  * [d6eab3](https://github.com/leanprover/lean4/commit/d6eab393f4df9d473b5736d636b178eb26d197e6) fixes a benchmark.
  * [#4563](https://github.com/leanprover/lean4/pull/4563) adds a workaround for a bug in `IndPredBelow.mkBelowMatcher`.
* **Cleanup:** [#4380](https://github.com/leanprover/lean4/pull/4380), [#4431](https://github.com/leanprover/lean4/pull/4431), [#4494](https://github.com/leanprover/lean4/pull/4494), [e8f768](https://github.com/leanprover/lean4/commit/e8f768f9fd8cefc758533bc76e3a12b398ed4a39), [de2690](https://github.com/leanprover/lean4/commit/de269060d17a581ed87f40378dbec74032633b27), [d3a756](https://github.com/leanprover/lean4/commit/d3a7569c97123d022828106468d54e9224ed8207), [#4404](https://github.com/leanprover/lean4/pull/4404), [#4537](https://github.com/leanprover/lean4/pull/4537).

### Compiler, runtime, and FFI

* [d85d3d](https://github.com/leanprover/lean4/commit/d85d3d5f3a09ff95b2ee47c6f89ef50b7e339126) fixes criterion for tail-calls in ownership calculation.
* [#3963](https://github.com/leanprover/lean4/pull/3963) adds validation of UTF-8 at the C++-to-Lean boundary in the runtime.
* [#4512](https://github.com/leanprover/lean4/pull/4512) fixes missing unboxing in interpreter when loading initialized value.
* [#4477](https://github.com/leanprover/lean4/pull/4477) exposes the compiler flags for the bundled C compiler (clang).

### Lake

* [#4384](https://github.com/leanprover/lean4/pull/4384) deprecates `inputFile` and replaces it with `inputBinFile` and `inputTextFile`. Unlike `inputBinFile` (and `inputFile`), `inputTextFile` normalizes line endings, which helps ensure text file traces are platform-independent.
* [#4371](https://github.com/leanprover/lean4/pull/4371) simplifies dependency resolution code.
* [#4439](https://github.com/leanprover/lean4/pull/4439) touches up the Lake configuration DSL and makes other improvements:
  string literals can now be used instead of identifiers for names,
  avoids using French quotes in `lake new` and `lake init` templates,
  changes the `exe` template to use `Main` for the main module,
  improves the `math` template error if `lean-toolchain` fails to download,
  and downgrades unknown configuration fields from an error to a warning to improve cross-version compatibility.
* [#4496](https://github.com/leanprover/lean4/pull/4496) tweaks `require` syntax and updates docs. Now `require` in TOML for a package name such as `doc-gen4` does not need French quotes.
* [#4485](https://github.com/leanprover/lean4/pull/4485) fixes a bug where package versions in indirect dependencies would take precedence over direct dependencies.
* [#4478](https://github.com/leanprover/lean4/pull/4478) fixes a bug where Lake incorrectly included the module dynamic library in a platform-independent trace.
* [#4529](https://github.com/leanprover/lean4/pull/4529) fixes some issues with bad import errors.
  A bad import in an executable no longer prevents the executable's root
  module from being built. This also fixes a problem where the location
  of a transitive bad import would not been shown.
  The root module of the executable now respects `nativeFacets`.
* [#4564](https://github.com/leanprover/lean4/pull/4564) fixes a bug where non-identifier script names could not be entered on the CLI without French quotes.
* [#4566](https://github.com/leanprover/lean4/pull/4566) addresses a few issues with precompiled libraries.
  * Fixes a bug where Lake would always precompile the package of a module.
  * If a module is precompiled, it now precompiles its imports. Previously, it would only do this if imported.
* [#4495](https://github.com/leanprover/lean4/pull/4495), [#4692](https://github.com/leanprover/lean4/pull/4692), [#4849](https://github.com/leanprover/lean4/pull/4849)
  add a new type of `require` that fetches package metadata from a
  registry API endpoint (e.g. Reservoir) and then clones a Git package
  using the information provided. To require such a dependency, the new
  syntax is:

  ```lean
  require <scope> / <pkg-name> [@ git <rev>]
  -- Examples:
  require "leanprover" / "doc-gen4"
  require "leanprover-community" / "proofwidgets" @ git "v0.0.39"
  ```

  Or in TOML:
  ```toml
  [[require]]
  name = "<pkg-name>"
  scope = "<scope>"
  rev = "<rev>"
  ```

  Unlike with Git dependencies, Lake can make use of the richer
  information provided by the registry to determine the default branch of
  the package. This means for repositories of packages like `doc-gen4`
  which have a default branch that is not `master`, Lake will now use said
  default branch (e.g., in `doc-gen4`'s case, `main`).

  Lake also supports configuring the registry endpoint via an environment
  variable: `RESERVIOR_API_URL`. Thus, any server providing a similar
  interface to Reservoir can be used as the registry. Further
  configuration options paralleling those of Cargo's [Alternative Registries](https://doc.rust-lang.org/cargo/reference/registries.html)
  and [Source Replacement](https://doc.rust-lang.org/cargo/reference/source-replacement.html)
  will come in the future.

### DevOps/CI
* [#4427](https://github.com/leanprover/lean4/pull/4427) uses Namespace runners for CI for `leanprover/lean4`.
* [#4440](https://github.com/leanprover/lean4/pull/4440) fixes speedcenter tests in CI.
* [#4441](https://github.com/leanprover/lean4/pull/4441) fixes that workflow change would break CI for unrebased PRs.
* [#4442](https://github.com/leanprover/lean4/pull/4442) fixes Wasm release-ci.
* [6d265b](https://github.com/leanprover/lean4/commit/6d265b42b117eef78089f479790587a399da7690) fixes for `github.event.pull_request.merge_commit_sha` sometimes not being available.
* [16cad2](https://github.com/leanprover/lean4/commit/16cad2b45c6a77efe4dce850dcdbaafaa7c91fc3) adds optimization for CI to not fetch complete history.
* [#4544](https://github.com/leanprover/lean4/pull/4544) causes releases to be marked as prerelease on GitHub.
* [#4446](https://github.com/leanprover/lean4/pull/4446) switches Lake to using `src/lake/lakefile.toml` to avoid needing to load a version of Lake to build Lake.
* Nix
  * [5eb5fa](https://github.com/leanprover/lean4/commit/5eb5fa49cf9862e99a5bccff8d4ca1a062f81900) fixes `update-stage0-commit` for Nix.
  * [#4476](https://github.com/leanprover/lean4/pull/4476) adds gdb to Nix shell.
  * [e665a0](https://github.com/leanprover/lean4/commit/e665a0d716dc42ba79b339b95e01eb99fe932cb3) fixes `update-stage0` for Nix.
  * [4808eb](https://github.com/leanprover/lean4/commit/4808eb7c4bfb98f212b865f06a97d46c44978a61) fixes `cacheRoots` for Nix.
  * [#3811](https://github.com/leanprover/lean4/pull/3811) adds platform-dependent flag to lib target.
  * [#4587](https://github.com/leanprover/lean4/pull/4587) adds linking of `-lStd` back into nix build flags on darwin.

### Breaking changes

* `Char.csize` is replaced by `Char.utf8Size` ([#4357](https://github.com/leanprover/lean4/pull/4357)).
* Library lemmas now are in terms of `(· == a)` over `(a == ·)` ([#3056](https://github.com/leanprover/lean4/pull/3056)).
* Now the normal forms for indexing into `List` and `Array` is `xs[n]` and `xs[n]?` rather than using functions like `List.get` ([#4400](https://github.com/leanprover/lean4/pull/4400)).
* Sometimes terms created via a sequence of unifications will be more eta reduced than before and proofs will require adaptation ([#4387](https://github.com/leanprover/lean4/pull/4387)).
* The `GetElem` class has been split into two; see the docstrings for `GetElem` and `GetElem?` for more information ([#4560](https://github.com/leanprover/lean4/pull/4560)).

````
