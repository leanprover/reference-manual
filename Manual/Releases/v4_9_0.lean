/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.9.0 (2024-07-01)" =>
%%%
tag := "release-v4.9.0"
file := "v4.9.0"
%%%

````markdown
### Language features, tactics, and metaprograms

* **Definition transparency**
  * [#4053](https://github.com/leanprover/lean4/pull/4053) adds the `seal` and `unseal` commands, which make definitions locally be irreducible or semireducible.
  * [#4061](https://github.com/leanprover/lean4/pull/4061) marks functions defined by well-founded recursion with `@[irreducible]` by default,
    which should prevent the expensive and often unfruitful unfolding of such definitions (see breaking changes below).
* **Incrementality**
  * [#3940](https://github.com/leanprover/lean4/pull/3940) extends incremental elaboration into various steps inside of declarations:
    definition headers, bodies, and tactics.

    [Screen recording](https://github.com/leanprover/lean4/assets/109126/c9d67b6f-c131-4bc3-a0de-7d63eaf1bfc9).
  * [250994](https://github.com/leanprover/lean4/commit/250994166ce036ab8644e459129f51ea79c1c2d2)
    and [67338b](https://github.com/leanprover/lean4/commit/67338bac2333fa39a8656e8f90574784e4c23d3d)
    add `@[incremental]` attribute to mark an elaborator as supporting incremental elaboration.
  * [#4259](https://github.com/leanprover/lean4/pull/4259) improves resilience by ensuring incremental commands and tactics are reached only in supported ways.
  * [#4268](https://github.com/leanprover/lean4/pull/4268) adds special handling for `:= by` so that stray tokens in tactic blocks do not inhibit incrementality.
  * [#4308](https://github.com/leanprover/lean4/pull/4308) adds incremental `have` tactic.
  * [#4340](https://github.com/leanprover/lean4/pull/4340) fixes incorrect info tree reuse.
  * [#4364](https://github.com/leanprover/lean4/pull/4364) adds incrementality for careful command macros such as `set_option in theorem`, `theorem foo.bar`, and `lemma`.
  * [#4395](https://github.com/leanprover/lean4/pull/4395) adds conservative fix for whitespace handling to avoid incremental reuse leading to goals in front of the text cursor being shown.
  * [#4407](https://github.com/leanprover/lean4/pull/4407) fixes non-incremental commands in macros blocking further incremental reporting.
  * [#4436](https://github.com/leanprover/lean4/pull/4436) fixes incremental reporting when there are nested tactics in terms.
  * [#4459](https://github.com/leanprover/lean4/pull/4459) adds incrementality support for `next` and `if` tactics.
  * [#4554](https://github.com/leanprover/lean4/pull/4554) disables incrementality for tactics in terms in tactics.
* **Functional induction**
  * [#4135](https://github.com/leanprover/lean4/pull/4135) ensures that the names used for functional induction are reserved.
  * [#4327](https://github.com/leanprover/lean4/pull/4327) adds support for structural recursion on reflexive types.
    For example,
    ```lean4
    inductive Many (α : Type u) where
      | none : Many α
      | more : α → (Unit → Many α) → Many α

    def Many.map {α β : Type u} (f : α → β) : Many α → Many β
      | .none => .none
      | .more x xs => .more (f x) (fun _ => (xs ()).map f)

    #check Many.map.induct
    /-
    Many.map.induct {α β : Type u} (f : α → β) (motive : Many α → Prop)
      (case1 : motive Many.none)
      (case2 : ∀ (x : α) (xs : Unit → Many α), motive (xs ()) → motive (Many.more x xs)) :
      ∀ (a : Many α), motive a
    -/
    ```
* [#3903](https://github.com/leanprover/lean4/pull/3903) makes the Lean frontend normalize all line endings to LF before processing.
  This lets Lean be insensitive to CRLF vs LF line endings, improving the cross-platform experience and making Lake hashes be faithful to what Lean processes.
* [#4130](https://github.com/leanprover/lean4/pull/4130) makes the tactic framework be able to recover from runtime errors (for example, deterministic timeouts or maximum recursion depth errors).
* `split` tactic
  * [#4211](https://github.com/leanprover/lean4/pull/4211) fixes `split at h` when `h` has forward dependencies.
  * [#4349](https://github.com/leanprover/lean4/pull/4349) allows `split` for `if`-expressions to work on non-propositional goals.
* `apply` tactic
  * [#3929](https://github.com/leanprover/lean4/pull/3929) makes error message for `apply` show implicit arguments in unification errors as needed.
    Modifies `MessageData` type (see breaking changes below).
* `cases` tactic
  * [#4224](https://github.com/leanprover/lean4/pull/4224) adds support for unification of offsets such as `x + 20000 = 20001` in `cases` tactic.
* `omega` tactic
  * [#4073](https://github.com/leanprover/lean4/pull/4073) lets `omega` fall back to using classical `Decidable` instances when setting up contradiction proofs.
  * [#4141](https://github.com/leanprover/lean4/pull/4141) and [#4184](https://github.com/leanprover/lean4/pull/4184) fix bugs.
  * [#4264](https://github.com/leanprover/lean4/pull/4264) improves `omega` error message if no facts found in local context.
  * [#4358](https://github.com/leanprover/lean4/pull/4358) improves expression matching in `omega` by using `match_expr`.
* `simp` tactic
  * [#4176](https://github.com/leanprover/lean4/pull/4176) makes names of erased lemmas clickable.
  * [#4208](https://github.com/leanprover/lean4/pull/4208) adds a pretty printer for discrimination tree keys.
  * [#4202](https://github.com/leanprover/lean4/pull/4202) adds `Simp.Config.index` configuration option,
    which controls whether to use the full discrimination tree when selecting candidate simp lemmas.
    When `index := false`, only the head function is taken into account, like in Lean 3.
    This feature can help users diagnose tricky simp failures or issues in code from libraries
    developed using Lean 3 and then ported to Lean 4.

    In the following example, it will report that `foo` is a problematic theorem.
    ```lean
    opaque f : Nat → Nat → Nat

    @[simp] theorem foo : f x (x, y).2 = y := by sorry

    example : f a b ≤ b := by
      set_option diagnostics true in
      simp (config := { index := false })
    /-
    [simp] theorems with bad keys
      foo, key: f _ (@Prod.mk ℕ ℕ _ _).2
    -/
    ```
    With the information above, users can annotate theorems such as `foo` using `no_index` for problematic subterms. Example:
    ```lean
    opaque f : Nat → Nat → Nat

    @[simp] theorem foo : f x (no_index (x, y).2) = y := by sorry

    example : f a b ≤ b := by
      simp -- `foo` is still applied with `index := true`
    ```
  * [#4274](https://github.com/leanprover/lean4/pull/4274) prevents internal `match` equational theorems from appearing in simp trace.
  * [#4177](https://github.com/leanprover/lean4/pull/4177) and [#4359](https://github.com/leanprover/lean4/pull/4359) make `simp` continue even if a simp lemma does not elaborate, if the tactic state is in recovery mode.
  * [#4341](https://github.com/leanprover/lean4/pull/4341) fixes panic when applying `@[simp]` to malformed theorem syntax.
  * [#4345](https://github.com/leanprover/lean4/pull/4345) fixes `simp` so that it does not use the forward version of a user-specified backward theorem.
  * [#4352](https://github.com/leanprover/lean4/pull/4352) adds missing `dsimp` simplifications for fixed parameters of generated congruence theorems.
  * [#4362](https://github.com/leanprover/lean4/pull/4362) improves trace messages for `simp` so that constants are hoverable.
* **Elaboration**
  * [#4046](https://github.com/leanprover/lean4/pull/4046) makes subst notation (`he ▸ h`) try rewriting in both directions even when there is no expected type available.
  * [#3328](https://github.com/leanprover/lean4/pull/3328) adds support for identifiers in autoparams (for example, `rfl` in `(h : x = y := by exact rfl)`).
  * [#4096](https://github.com/leanprover/lean4/pull/4096) changes how the type in `let` and `have` is elaborated, requiring that any tactics in the type be evaluated before proceeding, improving performance.
  * [#4215](https://github.com/leanprover/lean4/pull/4215) ensures the expression tree elaborator commits to the computed "max type" for the entire arithmetic expression.
  * [#4267](https://github.com/leanprover/lean4/pull/4267) cases signature elaboration errors to show even if there are parse errors in the body.
  * [#4368](https://github.com/leanprover/lean4/pull/4368) improves error messages when numeric literals fail to synthesize an `OfNat` instance,
    including special messages warning when the expected type of the numeral can be a proposition.
  * [#4643](https://github.com/leanprover/lean4/pull/4643) fixes issue leading to nested error messages and info trees vanishing, where snapshot subtrees were not restored on reuse.
  * [#4657](https://github.com/leanprover/lean4/pull/4657) calculates error suppression per snapshot, letting elaboration errors appear even when there are later parse errors ([RFC #3556](https://github.com/leanprover/lean4/issues/3556)).
* **Metaprogramming**
  * [#4167](https://github.com/leanprover/lean4/pull/4167) adds `Lean.MVarId.revertAll` to revert all free variables.
  * [#4169](https://github.com/leanprover/lean4/pull/4169) adds `Lean.MVarId.ensureNoMVar` to ensure the goal's target contains no expression metavariables.
  * [#4180](https://github.com/leanprover/lean4/pull/4180) adds `cleanupAnnotations` parameter to `forallTelescope` methods.
  * [#4307](https://github.com/leanprover/lean4/pull/4307) adds support for parser aliases in syntax quotations.
* Work toward implementing `grind` tactic
  * [0a515e](https://github.com/leanprover/lean4/commit/0a515e2ec939519dafb4b99daa81d6bf3c411404)
    and [#4164](https://github.com/leanprover/lean4/pull/4164)
    add `grind_norm` and `grind_norm_proc` attributes and `@[grind_norm]` theorems.
  * [#4170](https://github.com/leanprover/lean4/pull/4170), [#4221](https://github.com/leanprover/lean4/pull/4221),
    and [#4249](https://github.com/leanprover/lean4/pull/4249) create `grind` preprocessor and core module.
  * [#4235](https://github.com/leanprover/lean4/pull/4235) and [d6709e](https://github.com/leanprover/lean4/commit/d6709eb1576c5d40fc80462637dc041f970e4d9f)
    add special `cases` tactic to `grind` along with `@[grind_cases]` attribute to mark types that this `cases` tactic should automatically apply to.
  * [#4243](https://github.com/leanprover/lean4/pull/4243) adds special `injection?` tactic to `grind`.
* **Other fixes or improvements**
  * [#4065](https://github.com/leanprover/lean4/pull/4065) fixes a bug in the `Nat.reduceLeDiff` simproc.
  * [#3969](https://github.com/leanprover/lean4/pull/3969) makes deprecation warnings activate even for generalized field notation ("dot notation").
  * [#4132](https://github.com/leanprover/lean4/pull/4132) fixes the `sorry` term so that it does not activate the implicit lambda feature
  * [9803c5](https://github.com/leanprover/lean4/commit/9803c5dd63dc993628287d5f998525e74af03839)
    and [47c8e3](https://github.com/leanprover/lean4/commit/47c8e340d65b01f4d9f011686e3dda0d4bb30a20)
    move `cdot` and `calc` parsers to `Lean` namespace.
  * [#4252](https://github.com/leanprover/lean4/pull/4252) fixes the `case` tactic so that it is usable in macros by having it erase macro scopes from the tag.
  * [26b671](https://github.com/leanprover/lean4/commit/26b67184222e75529e1b166db050aaebee323d2d)
    and [cc33c3](https://github.com/leanprover/lean4/commit/cc33c39cb022d8a3166b1e89677c78835ead1fc7)
    extract `haveId` syntax.
  * [#4335](https://github.com/leanprover/lean4/pull/4335) fixes bugs in partial `calc` tactic when there is mdata or metavariables.
  * [#4329](https://github.com/leanprover/lean4/pull/4329) makes `termination_by?` report unused each unused parameter as `_`.
* **Docs:** [#4238](https://github.com/leanprover/lean4/pull/4238), [#4294](https://github.com/leanprover/lean4/pull/4294),
  [#4338](https://github.com/leanprover/lean4/pull/4338).

### Language server, widgets, and IDE extensions
* [#4066](https://github.com/leanprover/lean4/pull/4066) fixes features like "Find References" when browsing core Lean sources.
* [#4254](https://github.com/leanprover/lean4/pull/4254) allows embedding user widgets in structured messages.
  Companion PR is [vscode-lean4#449](https://github.com/leanprover/vscode-lean4/pull/449).
* [#4445](https://github.com/leanprover/lean4/pull/4445) makes watchdog more resilient against badly behaving clients.

### Library
* [#4059](https://github.com/leanprover/lean4/pull/4059) upstreams many `List` and `Array` operations and theorems from Batteries.
* [#4055](https://github.com/leanprover/lean4/pull/4055) removes the unused `Inhabited` instance for `Subtype`.
* [#3967](https://github.com/leanprover/lean4/pull/3967) adds dates in existing `@[deprecated]` attributes.
* [#4231](https://github.com/leanprover/lean4/pull/4231) adds boilerplate `Char`, `UInt`, and `Fin` theorems.
* [#4205](https://github.com/leanprover/lean4/pull/4205) fixes the `MonadStore` type classes to use `semiOutParam`.
* [#4350](https://github.com/leanprover/lean4/pull/4350) renames `IsLawfulSingleton` to `LawfulSingleton`.
* `Nat`
  * [#4094](https://github.com/leanprover/lean4/pull/4094) swaps `Nat.zero_or` and `Nat.or_zero`.
  * [#4098](https://github.com/leanprover/lean4/pull/4098) and [#4145](https://github.com/leanprover/lean4/pull/4145)
    change the definition of `Nat.mod` so that `n % (m + n)` reduces when `n` is literal without relying on well-founded recursion,
    which becomes irreducible by default in [#4061](https://github.com/leanprover/lean4/pull/4061).
  * [#4188](https://github.com/leanprover/lean4/pull/4188) redefines `Nat.testBit` to be more performant.
  * Theorems: [#4199](https://github.com/leanprover/lean4/pull/4199).
* `Array`
  * [#4074](https://github.com/leanprover/lean4/pull/4074) improves the functional induction principle `Array.feraseIdx.induct`.
* `List`
  * [#4172](https://github.com/leanprover/lean4/pull/4172) removes `@[simp]` from `List.length_pos`.
* `Option`
  * [#4037](https://github.com/leanprover/lean4/pull/4037) adds theorems to simplify `Option`-valued dependent if-then-else.
  * [#4314](https://github.com/leanprover/lean4/pull/4314) removes `@[simp]` from `Option.bind_eq_some`.
* `BitVec`
  * Theorems: [#3920](https://github.com/leanprover/lean4/pull/3920), [#4095](https://github.com/leanprover/lean4/pull/4095),
    [#4075](https://github.com/leanprover/lean4/pull/4075), [#4148](https://github.com/leanprover/lean4/pull/4148),
    [#4165](https://github.com/leanprover/lean4/pull/4165), [#4178](https://github.com/leanprover/lean4/pull/4178),
    [#4200](https://github.com/leanprover/lean4/pull/4200), [#4201](https://github.com/leanprover/lean4/pull/4201),
    [#4298](https://github.com/leanprover/lean4/pull/4298), [#4299](https://github.com/leanprover/lean4/pull/4299),
    [#4257](https://github.com/leanprover/lean4/pull/4257), [#4179](https://github.com/leanprover/lean4/pull/4179),
    [#4321](https://github.com/leanprover/lean4/pull/4321), [#4187](https://github.com/leanprover/lean4/pull/4187).
  * [#4193](https://github.com/leanprover/lean4/pull/4193) adds simprocs for reducing `x >>> i` and `x <<< i` where `i` is a bitvector literal.
  * [#4194](https://github.com/leanprover/lean4/pull/4194) adds simprocs for reducing `(x <<< i) <<< j` and `(x >>> i) >>> j` where `i` and `j` are natural number literals.
  * [#4229](https://github.com/leanprover/lean4/pull/4229) redefines `rotateLeft`/`rotateRight` to use modulo reduction of shift offset.
  * [0d3051](https://github.com/leanprover/lean4/commit/0d30517dca094a07bcb462252f718e713b93ffba) makes `<num>#<term>` bitvector literal notation global.
* `Char`/`String`
  * [#4143](https://github.com/leanprover/lean4/pull/4143) modifies `String.substrEq` to avoid linter warnings in downstream code.
  * [#4233](https://github.com/leanprover/lean4/pull/4233) adds simprocs for `Char` and `String` inequalities.
  * [#4348](https://github.com/leanprover/lean4/pull/4348) upstreams Mathlib lemmas.
  * [#4354](https://github.com/leanprover/lean4/pull/4354) upstreams basic `String` lemmas.
* `HashMap`
  * [#4248](https://github.com/leanprover/lean4/pull/4248) fixes implicitness of typeclass arguments in `HashMap.ofList`.
* `IO`
  * [#4036](https://github.com/leanprover/lean4/pull/4036) adds `IO.Process.getCurrentDir` and `IO.Process.setCurrentDir` for adjusting the current process's working directory.
* **Cleanup:** [#4077](https://github.com/leanprover/lean4/pull/4077), [#4189](https://github.com/leanprover/lean4/pull/4189),
  [#4304](https://github.com/leanprover/lean4/pull/4304).
* **Docs:** [#4001](https://github.com/leanprover/lean4/pull/4001), [#4166](https://github.com/leanprover/lean4/pull/4166),
  [#4332](https://github.com/leanprover/lean4/pull/4332).

### Lean internals
* **Defeq and WHNF algorithms**
  * [#4029](https://github.com/leanprover/lean4/pull/4029) remove unnecessary `checkpointDefEq`
  * [#4206](https://github.com/leanprover/lean4/pull/4206) fixes `isReadOnlyOrSyntheticOpaque` to respect metavariable depth.
  * [#4217](https://github.com/leanprover/lean4/pull/4217) fixes missing occurs check for delayed assignments.
* **Definition transparency**
  * [#4052](https://github.com/leanprover/lean4/pull/4052) adds validation to application of `@[reducible]`/`@[semireducible]`/`@[irreducible]` attributes (with `local`/`scoped` modifiers as well).
    Setting `set_option allowUnsafeReductibility true` turns this validation off.
* **Inductive types**
  * [#3591](https://github.com/leanprover/lean4/pull/3591) fixes a bug where indices could be incorrectly promoted to parameters.
  * [#3398](https://github.com/leanprover/lean4/pull/3398) fixes a bug in the injectivity theorem generator.
  * [#4342](https://github.com/leanprover/lean4/pull/4342) fixes elaboration of mutual inductives with instance parameters.
* **Diagnostics and profiling**
  * [#3986](https://github.com/leanprover/lean4/pull/3986) adds option `trace.profiler.useHeartbeats` to switch `trace.profiler.threshold` to being in terms of heartbeats instead of milliseconds.
  * [#4082](https://github.com/leanprover/lean4/pull/4082) makes `set_option diagnostics true` report kernel diagnostic information.
* **Typeclass resolution**
  * [#4119](https://github.com/leanprover/lean4/pull/4119) fixes multiple issues with TC caching interacting with `synthPendingDepth`, adds `maxSynthPendingDepth` option with default value `1`.
  * [#4210](https://github.com/leanprover/lean4/pull/4210) ensures local instance cache does not contain multiple copies of the same instance.
  * [#4216](https://github.com/leanprover/lean4/pull/4216) fix handling of metavariables, to avoid needing to set the option `backward.synthInstance.canonInstances` to `false`.
* **Other fixes or improvements**
  * [#4080](https://github.com/leanprover/lean4/pull/4080) fixes propagation of state for `Lean.Elab.Command.liftCoreM` and `Lean.Elab.Command.liftTermElabM`.
  * [#3944](https://github.com/leanprover/lean4/pull/3944) makes the `Repr` deriving handler be consistent between `structure` and `inductive` for how types and proofs are erased.
  * [#4113](https://github.com/leanprover/lean4/pull/4113) propagates `maxHeartbeats` to kernel to control "(kernel) deterministic timeout" error.
  * [#4125](https://github.com/leanprover/lean4/pull/4125) reverts [#3970](https://github.com/leanprover/lean4/pull/3970) (monadic generalization of `FindExpr`).
  * [#4128](https://github.com/leanprover/lean4/pull/4128) catches stack overflow in auto-bound implicits feature.
  * [#4129](https://github.com/leanprover/lean4/pull/4129) adds `tryCatchRuntimeEx` combinator to replace `catchRuntimeEx` reader state.
  * [#4155](https://github.com/leanprover/lean4/pull/4155) simplifies the expression canonicalizer.
  * [#4151](https://github.com/leanprover/lean4/pull/4151) and [#4369](https://github.com/leanprover/lean4/pull/4369)
    add many missing trace classes.
  * [#4185](https://github.com/leanprover/lean4/pull/4185) makes congruence theorem generators clean up type annotations of argument types.
  * [#4192](https://github.com/leanprover/lean4/pull/4192) fixes restoration of infotrees when auto-bound implicit feature is activated,
    fixing a pretty printing error in hovers and strengthening the unused variable linter.
  * [dfb496](https://github.com/leanprover/lean4/commit/dfb496a27123c3864571aec72f6278e2dad1cecf) fixes `declareBuiltin` to allow it to be called multiple times per declaration.
  * [#4569](https://github.com/leanprover/lean4/pull/4569) fixes an issue introduced in a merge conflict, where the interrupt exception was swallowed by some `tryCatchRuntimeEx` uses.
  * [#4584](https://github.com/leanprover/lean4/pull/4584) (backported as [b056a0](https://github.com/leanprover/lean4/commit/b056a0b395bb728512a3f3e83bf9a093059d4301)) adapts kernel interruption to the new cancellation system.
  * Cleanup: [#4112](https://github.com/leanprover/lean4/pull/4112), [#4126](https://github.com/leanprover/lean4/pull/4126), [#4091](https://github.com/leanprover/lean4/pull/4091), [#4139](https://github.com/leanprover/lean4/pull/4139), [#4153](https://github.com/leanprover/lean4/pull/4153).
  * Tests: [030406](https://github.com/leanprover/lean4/commit/03040618b8f9b35b7b757858483e57340900cdc4), [#4133](https://github.com/leanprover/lean4/pull/4133).

### Compiler, runtime, and FFI
* [#4100](https://github.com/leanprover/lean4/pull/4100) improves reset/reuse algorithm; it now runs a second pass relaxing the constraint that reused memory cells must only be for the exact same constructor.
* [#2903](https://github.com/leanprover/lean4/pull/2903) fixes segfault in old compiler from mishandling `noConfusion` applications.
* [#4311](https://github.com/leanprover/lean4/pull/4311) fixes bug in constant folding.
* [#3915](https://github.com/leanprover/lean4/pull/3915) documents the runtime memory layout for inductive types.

### Lake
* [#4518](https://github.com/leanprover/lean4/pull/4518) makes trace reading more robust. Lake now rebuilds if trace files are invalid or unreadable and is backwards compatible with previous pure numeric traces.
* [#4057](https://github.com/leanprover/lean4/pull/4057) adds support for docstrings on `require` commands.
* [#4088](https://github.com/leanprover/lean4/pull/4088) improves hovers for `family_def` and `library_data` commands.
* [#4147](https://github.com/leanprover/lean4/pull/4147) adds default `README.md` to package templates
* [#4261](https://github.com/leanprover/lean4/pull/4261) extends `lake test` help page, adds help page for `lake check-test`,
  adds `lake lint` and tag `@[lint_driver]`, adds support for specifying test and lint drivers from dependencies,
  adds `testDriverArgs` and `lintDriverArgs` options, adds support for library test drivers,
  makes `lake check-test` and `lake check-lint` only load the package without dependencies.
* [#4270](https://github.com/leanprover/lean4/pull/4270) adds `lake pack` and `lake unpack` for packing and unpacking Lake build artifacts from an archive.
* [#4083](https://github.com/leanprover/lean4/pull/4083)
  Switches the manifest format to use `major.minor.patch` semantic
  versions. Major version increments indicate breaking changes (e.g., new
  required fields and semantic changes to existing fields). Minor version
  increments (after `0.x`) indicate backwards-compatible extensions (e.g.,
  adding optional fields, removing fields). This change is backwards
  compatible. Lake will still successfully read old manifests with numeric
  versions. It will treat the numeric version `N` as semantic version
  `0.N.0`. Lake will also accept manifest versions with `-` suffixes
  (e.g., `x.y.z-foo`) and then ignore the suffix.
* [#4273](https://github.com/leanprover/lean4/pull/4273) adds a lift from `JobM` to `FetchM` for backwards compatibility reasons.
* [#4351](https://github.com/leanprover/lean4/pull/4351) fixes `LogIO`-to-`CliM`-lifting performance issues.
* [#4343](https://github.com/leanprover/lean4/pull/4343) make Lake store the dependency trace for a build in
  the cached build long and then verifies that it matches the trace of the current build before replaying the log.
* [#4402](https://github.com/leanprover/lean4/pull/4402) moves the cached log into the trace file (no more `.log.json`).
  This means logs are no longer cached on fatal errors and this ensures that an out-of-date log is not associated with an up-to-date trace.
  Separately, `.hash` file generation was changed to be more reliable as well.
  The `.hash` files are deleted as part of the build and always regenerate with `--rehash`.
* **Other fixes or improvements**
  * [#4056](https://github.com/leanprover/lean4/pull/4056) cleans up tests
  * [#4244](https://github.com/leanprover/lean4/pull/4244) fixes `noRelease` test when Lean repo is tagged
  * [#4346](https://github.com/leanprover/lean4/pull/4346) improves `tests/serve`
  * [#4356](https://github.com/leanprover/lean4/pull/4356) adds build log path to the warning for a missing or invalid build log.

### DevOps
* [#3984](https://github.com/leanprover/lean4/pull/3984) adds a script (`script/rebase-stage0.sh`) for `git rebase -i` that automatically updates each stage0.
* [#4108](https://github.com/leanprover/lean4/pull/4108) finishes renamings from transition to Std to Batteries.
* [#4109](https://github.com/leanprover/lean4/pull/4109) adjusts the Github bug template to mention testing using [live.lean-lang.org](https://live.lean-lang.org).
* [#4136](https://github.com/leanprover/lean4/pull/4136) makes CI rerun only when `full-ci` label is added or removed.
* [#4175](https://github.com/leanprover/lean4/pull/4175) and [72b345](https://github.com/leanprover/lean4/commit/72b345c621a9a06d3a5a656da2b793a5eea5f168)
  switch to using `#guard_msgs` to run tests as much as possible.
* [#3125](https://github.com/leanprover/lean4/pull/3125) explains the Lean4 `pygments` lexer.
* [#4247](https://github.com/leanprover/lean4/pull/4247) sets up a procedure for preparing release notes.
* [#4032](https://github.com/leanprover/lean4/pull/4032) modernizes build instructions and workflows.
* [#4255](https://github.com/leanprover/lean4/pull/4255) moves some expensive checks from merge queue to releases.
* [#4265](https://github.com/leanprover/lean4/pull/4265) adds aarch64 macOS as native compilation target for CI.
* [f05a82](https://github.com/leanprover/lean4/commit/f05a82799a01569edeb5e2594cd7d56282320f9e) restores macOS aarch64 install suffix in CI
* [#4317](https://github.com/leanprover/lean4/pull/4317) updates build instructions for macOS.
* [#4333](https://github.com/leanprover/lean4/pull/4333) adjusts workflow to update Batteries in manifest when creating `lean-pr-testing-NNNN` Mathlib branches.
* [#4355](https://github.com/leanprover/lean4/pull/4355) simplifies `lean4checker` step of release checklist.
* [#4361](https://github.com/leanprover/lean4/pull/4361) adds installing elan to `pr-release` CI step.
* [#4628](https://github.com/leanprover/lean4/pull/4628) fixes the Windows build, which was missing an exported symbol.

### Breaking changes
While most changes could be considered to be a breaking change, this section makes special note of API changes.

* `Nat.zero_or` and `Nat.or_zero` have been swapped ([#4094](https://github.com/leanprover/lean4/pull/4094)).
* `IsLawfulSingleton` is now `LawfulSingleton` ([#4350](https://github.com/leanprover/lean4/pull/4350)).
* The `BitVec` literal notation is now `<num>#<term>` rather than `<term>#<term>`, and it is global rather than scoped. Use `BitVec.ofNat w x` rather than `x#w` when `x` is a not a numeric literal ([0d3051](https://github.com/leanprover/lean4/commit/0d30517dca094a07bcb462252f718e713b93ffba)).
* `BitVec.rotateLeft` and `BitVec.rotateRight` now take the shift modulo the bitwidth ([#4229](https://github.com/leanprover/lean4/pull/4229)).
* These are no longer simp lemmas:
  `List.length_pos` ([#4172](https://github.com/leanprover/lean4/pull/4172)),
  `Option.bind_eq_some` ([#4314](https://github.com/leanprover/lean4/pull/4314)).
* Types in `let` and `have` (both the expressions and tactics) may fail to elaborate due to new restrictions on what sorts of elaboration problems may be postponed ([#4096](https://github.com/leanprover/lean4/pull/4096)).
  In particular, tactics embedded in the type will no longer make use of the type of `value` in expressions such as `let x : type := value; body`.
* Now functions defined by well-founded recursion are marked with `@[irreducible]` by default ([#4061](https://github.com/leanprover/lean4/pull/4061)).
  Existing proofs that hold by definitional equality (e.g. `rfl`) can be
  rewritten to explicitly unfold the function definition (using `simp`,
  `unfold`, `rw`), or the recursive function can be temporarily made
  semireducible (using `unseal f in` before the command), or the function
  definition itself can be marked as `@[semireducible]` to get the previous
  behavior.
* Due to [#3929](https://github.com/leanprover/lean4/pull/3929):
  * The `MessageData.ofPPFormat` constructor has been removed.
    Its functionality has been split into two:

    - for lazy structured messages, please use `MessageData.lazy`;
    - for embedding `Format` or `FormatWithInfos`, use `MessageData.ofFormatWithInfos`.

    An example migration can be found in [#3929](https://github.com/leanprover/lean4/pull/3929/files#diff-5910592ab7452a0e1b2616c62d22202d2291a9ebb463145f198685aed6299867L109).

  * The `MessageData.ofFormat` constructor has been turned into a function.
    If you need to inspect `MessageData`, you can pattern-match on `MessageData.ofFormatWithInfos`.

````
