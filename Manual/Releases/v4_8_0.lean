/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.8.0 (2024-06-05)" =>
%%%
tag := "release-v4.8.0"
file := "v4.8.0"
%%%

````markdown
### Language features, tactics, and metaprograms

* **Functional induction principles.**
  [#3432](https://github.com/leanprover/lean4/pull/3432), [#3620](https://github.com/leanprover/lean4/pull/3620),
  [#3754](https://github.com/leanprover/lean4/pull/3754), [#3762](https://github.com/leanprover/lean4/pull/3762),
  [#3738](https://github.com/leanprover/lean4/pull/3738), [#3776](https://github.com/leanprover/lean4/pull/3776),
  [#3898](https://github.com/leanprover/lean4/pull/3898).

  Derived from the definition of a (possibly mutually) recursive function,
  a **functional induction principle** is created that is tailored to proofs about that function.

  For example from:
  ```
  def ackermann : Nat → Nat → Nat
    | 0, m => m + 1
    | n+1, 0 => ackermann n 1
    | n+1, m+1 => ackermann n (ackermann (n + 1) m)
  ```
  we get
  ```
  ackermann.induct (motive : Nat → Nat → Prop) (case1 : ∀ (m : Nat), motive 0 m)
    (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
    (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m))
    (x x : Nat) : motive x x
  ```

  It can be used in the `induction` tactic using the `using` syntax:
  ```
  induction n, m using ackermann.induct
  ```
* The termination checker now recognizes more recursion patterns without an
  explicit `termination_by`. In particular the idiom of counting up to an upper
  bound, as in
  ```
  def Array.sum (arr : Array Nat) (i acc : Nat) : Nat :=
    if _ : i < arr.size then
      Array.sum arr (i+1) (acc + arr[i])
    else
      acc
  ```
  is recognized without having to say `termination_by arr.size - i`.
  * [#3630](https://github.com/leanprover/lean4/pull/3630) makes `termination_by?` not use `sizeOf` when not needed
  * [#3652](https://github.com/leanprover/lean4/pull/3652) improves the `termination_by` syntax.
  * [#3658](https://github.com/leanprover/lean4/pull/3658) changes how termination arguments are elaborated.
  * [#3665](https://github.com/leanprover/lean4/pull/3665) refactors GuessLex to allow inferring more complex termination arguments
  * [#3666](https://github.com/leanprover/lean4/pull/3666) infers termination arguments such as `xs.size - i`
* [#3629](https://github.com/leanprover/lean4/pull/3629),
  [#3655](https://github.com/leanprover/lean4/pull/3655),
  [#3747](https://github.com/leanprover/lean4/pull/3747):
  Adds `@[induction_eliminator]` and `@[cases_eliminator]` attributes to be able to define custom eliminators
  for the `induction` and `cases` tactics, replacing the `@[eliminator]` attribute.
  Gives custom eliminators for `Nat` so that `induction` and `cases` put goal states into terms of `0` and `n + 1`
  rather than `Nat.zero` and `Nat.succ n`.
  Added option `tactic.customEliminators` to control whether to use custom eliminators.
  Added a hack for `rcases`/`rintro`/`obtain` to use the custom eliminator for `Nat`.
* **Shorter instances names.** There is a new algorithm for generating names for anonymous instances.
  Across Std and Mathlib, the median ratio between lengths of new names and of old names is about 72%.
  With the old algorithm, the longest name was 1660 characters, and now the longest name is 202 characters.
  The new algorithm's 95th percentile name length is 67 characters, versus 278 for the old algorithm.
  While the new algorithm produces names that are 1.2% less unique,
  it avoids cross-project collisions by adding a module-based suffix
  when it does not refer to declarations from the same "project" (modules that share the same root).
  [#3089](https://github.com/leanprover/lean4/pull/3089)
  and [#3934](https://github.com/leanprover/lean4/pull/3934).
* [8d2adf](https://github.com/leanprover/lean4/commit/8d2adf521d2b7636347a5b01bfe473bf0fcfaf31)
  Importing two different files containing proofs of the same theorem is no longer considered an error.
  This feature is particularly useful for theorems that are automatically generated on demand (e.g., equational theorems).
* [84b091](https://github.com/leanprover/lean4/commit/84b0919a116e9be12f933e764474f45d964ce85c)
  Lean now generates an error if the type of a theorem is **not** a proposition.
* **Definition transparency.** [47a343](https://github.com/leanprover/lean4/commit/47a34316fc03ce936fddd2d3dce44784c5bcdfa9). `@[reducible]`, `@[semireducible]`, and `@[irreducible]` are now scoped and able to be set for imported declarations.
* `simp`/`dsimp`
  * [#3607](https://github.com/leanprover/lean4/pull/3607) enables kernel projection reduction in `dsimp`
  * [b24fbf](https://github.com/leanprover/lean4/commit/b24fbf44f3aaa112f5d799ef2a341772d1eb222d)
    and [acdb00](https://github.com/leanprover/lean4/commit/acdb0054d5a0efa724cff596ac26852fad5724c4):
    `dsimproc` command
    to define defeq-preserving simplification procedures.
  * [#3624](https://github.com/leanprover/lean4/pull/3624) makes `dsimp` normalize raw nat literals as `OfNat.ofNat` applications.
  * [#3628](https://github.com/leanprover/lean4/pull/3628) makes `simp` correctly handle `OfScientific.ofScientific` literals.
  * [#3654](https://github.com/leanprover/lean4/pull/3654) makes `dsimp?` report used simprocs.
  * [dee074](https://github.com/leanprover/lean4/commit/dee074dcde03a37b7895a4901df2e4fa490c73c7) fixes equation theorem
    handling in `simp` for non-recursive definitions.
  * [#3819](https://github.com/leanprover/lean4/pull/3819) improved performance when simp encounters a loop.
  * [#3821](https://github.com/leanprover/lean4/pull/3821) fixes discharger/cache interaction.
  * [#3824](https://github.com/leanprover/lean4/pull/3824) keeps `simp` from breaking `Char` literals.
  * [#3838](https://github.com/leanprover/lean4/pull/3838) allows `Nat` instances matching to be more lenient.
  * [#3870](https://github.com/leanprover/lean4/pull/3870) documentation for `simp` configuration options.
  * [#3972](https://github.com/leanprover/lean4/pull/3972) fixes simp caching.
  * [#4044](https://github.com/leanprover/lean4/pull/4044) improves cache behavior for "well-behaved" dischargers.
* `omega`
  * [#3639](https://github.com/leanprover/lean4/pull/3639), [#3766](https://github.com/leanprover/lean4/pull/3766),
    [#3853](https://github.com/leanprover/lean4/pull/3853), [#3875](https://github.com/leanprover/lean4/pull/3875):
    introduces a term canonicalizer.
  * [#3736](https://github.com/leanprover/lean4/pull/3736) improves handling of positivity for the modulo operator for `Int`.
  * [#3828](https://github.com/leanprover/lean4/pull/3828) makes it work as a `simp` discharger.
  * [#3847](https://github.com/leanprover/lean4/pull/3847) adds helpful error messages.
* `rfl`
  * [#3671](https://github.com/leanprover/lean4/pull/3671), [#3708](https://github.com/leanprover/lean4/pull/3708): upstreams the `@[refl]` attribute and the `rfl` tactic.
  * [#3751](https://github.com/leanprover/lean4/pull/3751) makes `apply_rfl` not operate on `Eq` itself.
  * [#4067](https://github.com/leanprover/lean4/pull/4067) improves error message when there are no goals.
* [#3719](https://github.com/leanprover/lean4/pull/3719) upstreams the `rw?` tactic, with fixes and improvements in
  [#3783](https://github.com/leanprover/lean4/pull/3783), [#3794](https://github.com/leanprover/lean4/pull/3794),
  [#3911](https://github.com/leanprover/lean4/pull/3911).
* `conv`
  * [#3659](https://github.com/leanprover/lean4/pull/3659) adds a `conv` version of the `calc` tactic.
  * [#3763](https://github.com/leanprover/lean4/pull/3763) makes `conv` clean up using `try with_reducible rfl` instead of `try rfl`.
* `#guard_msgs`
  * [#3617](https://github.com/leanprover/lean4/pull/3617) introduces whitespace protection using the `⏎` character.
  * [#3883](https://github.com/leanprover/lean4/pull/3883):
    The `#guard_msgs` command now has options to change whitespace normalization and sensitivity to message ordering.
    For example, `#guard_msgs (whitespace := lax) in cmd` collapses whitespace before checking messages,
    and `#guard_msgs (ordering := sorted) in cmd` sorts the messages in lexicographic order before checking.
  * [#3931](https://github.com/leanprover/lean4/pull/3931) adds an unused variables ignore function for `#guard_msgs`.
  * [#3912](https://github.com/leanprover/lean4/pull/3912) adds a diff between the expected and actual outputs. This feature is currently
    disabled by default, but can be enabled with `set_option guard_msgs.diff true`.
    Depending on user feedback, this option may default to `true` in a future version of Lean.
* `do` **notation**
  * [#3820](https://github.com/leanprover/lean4/pull/3820) makes it an error to lift `(<- ...)` out of a pure `if ... then ... else ...`
* **Lazy discrimination trees**
  * [#3610](https://github.com/leanprover/lean4/pull/3610) fixes a name collision for `LazyDiscrTree` that could lead to cache poisoning.
  * [#3677](https://github.com/leanprover/lean4/pull/3677) simplifies and fixes `LazyDiscrTree` handling for `exact?`/`apply?`.
  * [#3685](https://github.com/leanprover/lean4/pull/3685) moves general `exact?`/`apply?` functionality into `LazyDiscrTree`.
  * [#3769](https://github.com/leanprover/lean4/pull/3769) has lemma selection improvements for `rw?` and `LazyDiscrTree`.
  * [#3818](https://github.com/leanprover/lean4/pull/3818) improves ordering of matches.
* [#3590](https://github.com/leanprover/lean4/pull/3590) adds `inductive.autoPromoteIndices` option to be able to disable auto promotion of indices in the `inductive` command.
* **Miscellaneous bug fixes and improvements**
  * [#3606](https://github.com/leanprover/lean4/pull/3606) preserves `cache` and `dischargeDepth` fields in `Lean.Meta.Simp.Result.mkEqSymm`.
  * [#3633](https://github.com/leanprover/lean4/pull/3633) makes `elabTermEnsuringType` respect `errToSorry`, improving error recovery of the `have` tactic.
  * [#3647](https://github.com/leanprover/lean4/pull/3647) enables `noncomputable unsafe` definitions, for deferring implementations until later.
  * [#3672](https://github.com/leanprover/lean4/pull/3672) adjust namespaces of tactics.
  * [#3725](https://github.com/leanprover/lean4/pull/3725) fixes `Ord` derive handler for indexed inductive types with unused alternatives.
  * [#3893](https://github.com/leanprover/lean4/pull/3893) improves performance of derived `Ord` instances.
  * [#3771](https://github.com/leanprover/lean4/pull/3771) changes error reporting for failing tactic macros. Improves `rfl` error message.
  * [#3745](https://github.com/leanprover/lean4/pull/3745) fixes elaboration of generalized field notation if the object of the notation is an optional parameter.
  * [#3799](https://github.com/leanprover/lean4/pull/3799) makes commands such as `universe`, `variable`, `namespace`, etc. require that their argument appear in a later column.
    Commands that can optionally parse an `ident` or parse any number of `ident`s generally should require
    that the `ident` use `colGt`. This keeps typos in commands from being interpreted as identifiers.
  * [#3815](https://github.com/leanprover/lean4/pull/3815) lets the `split` tactic be used for writing code.
  * [#3822](https://github.com/leanprover/lean4/pull/3822) adds missing info in `induction` tactic for `with` clauses of the form `| cstr a b c => ?_`.
  * [#3806](https://github.com/leanprover/lean4/pull/3806) fixes `withSetOptionIn` combinator.
  * [#3844](https://github.com/leanprover/lean4/pull/3844) removes unused `trace.Elab.syntax` option.
  * [#3896](https://github.com/leanprover/lean4/pull/3896) improves hover and go-to-def for `attribute` command.
  * [#3989](https://github.com/leanprover/lean4/pull/3989) makes linter options more discoverable.
  * [#3916](https://github.com/leanprover/lean4/pull/3916) fixes go-to-def for syntax defined with `@[builtin_term_parser]`.
  * [#3962](https://github.com/leanprover/lean4/pull/3962) fixes how `solveByElim` handles `symm` lemmas, making `exact?`/`apply?` usable again.
  * [#3968](https://github.com/leanprover/lean4/pull/3968) improves the `@[deprecated]` attribute, adding `(since := "<date>")` field.
  * [#3768](https://github.com/leanprover/lean4/pull/3768) makes `#print` command show structure fields.
  * [#3974](https://github.com/leanprover/lean4/pull/3974) makes `exact?%` behave like `by exact?` rather than `by apply?`.
  * [#3994](https://github.com/leanprover/lean4/pull/3994) makes elaboration of `he ▸ h` notation more predictable.
  * [#3991](https://github.com/leanprover/lean4/pull/3991) adjusts transparency for `decreasing_trivial` macros.
  * [#4092](https://github.com/leanprover/lean4/pull/4092) improves performance of `binop%` and `binrel%` expression tree elaborators.
* **Docs:** [#3748](https://github.com/leanprover/lean4/pull/3748), [#3796](https://github.com/leanprover/lean4/pull/3796),
[#3800](https://github.com/leanprover/lean4/pull/3800), [#3874](https://github.com/leanprover/lean4/pull/3874),
[#3863](https://github.com/leanprover/lean4/pull/3863), [#3862](https://github.com/leanprover/lean4/pull/3862),
[#3891](https://github.com/leanprover/lean4/pull/3891), [#3873](https://github.com/leanprover/lean4/pull/3873),
[#3908](https://github.com/leanprover/lean4/pull/3908), [#3872](https://github.com/leanprover/lean4/pull/3872).

### Language server and IDE extensions

* [#3602](https://github.com/leanprover/lean4/pull/3602) enables `import` auto-completions.
* [#3608](https://github.com/leanprover/lean4/pull/3608) fixes issue [leanprover/vscode-lean4#392](https://github.com/leanprover/vscode-lean4/issues/392).
  Diagnostic ranges had an off-by-one error that would misplace goal states for example.
* [#3014](https://github.com/leanprover/lean4/pull/3014) introduces snapshot trees, foundational work for incremental tactics and parallelism.
  [#3849](https://github.com/leanprover/lean4/pull/3849) adds basic incrementality API.
* [#3271](https://github.com/leanprover/lean4/pull/3271) adds support for server-to-client requests.
* [#3656](https://github.com/leanprover/lean4/pull/3656) fixes jump to definition when there are conflicting names from different files.
  Fixes issue [#1170](https://github.com/leanprover/lean4/issues/1170).
* [#3691](https://github.com/leanprover/lean4/pull/3691), [#3925](https://github.com/leanprover/lean4/pull/3925),
  [#3932](https://github.com/leanprover/lean4/pull/3932) keep semantic tokens synchronized (used for semantic highlighting), with performance improvements.
* [#3247](https://github.com/leanprover/lean4/pull/3247) and [#3730](https://github.com/leanprover/lean4/pull/3730)
  add diagnostics to run "Restart File" when a file dependency is saved.
* [#3722](https://github.com/leanprover/lean4/pull/3722) uses the correct module names when displaying references.
* [#3728](https://github.com/leanprover/lean4/pull/3728) makes errors in header reliably appear and makes the "Import out of date" warning be at "hint" severity.
  [#3739](https://github.com/leanprover/lean4/pull/3739) simplifies the text of this warning.
* [#3778](https://github.com/leanprover/lean4/pull/3778) fixes [#3462](https://github.com/leanprover/lean4/issues/3462),
  where info nodes from before the cursor would be used for computing completions.
* [#3985](https://github.com/leanprover/lean4/pull/3985) makes trace timings appear in Infoview.

### Pretty printing

* [#3797](https://github.com/leanprover/lean4/pull/3797) fixes the hovers over binders so that they show their types.
* [#3640](https://github.com/leanprover/lean4/pull/3640) and [#3735](https://github.com/leanprover/lean4/pull/3735): Adds attribute `@[pp_using_anonymous_constructor]` to make structures pretty print as `⟨x, y, z⟩`
  rather than as `{a := x, b := y, c := z}`.
  This attribute is applied to `Sigma`, `PSigma`, `PProd`, `Subtype`, `And`, and `Fin`.
* [#3749](https://github.com/leanprover/lean4/pull/3749)
  Now structure instances pretty print with parent structures' fields inlined.
  That is, if `B` extends `A`, then `{ toA := { x := 1 }, y := 2 }` now pretty prints as `{ x := 1, y := 2 }`.
  Setting option `pp.structureInstances.flatten` to false turns this off.
* [#3737](https://github.com/leanprover/lean4/pull/3737), [#3744](https://github.com/leanprover/lean4/pull/3744)
  and [#3750](https://github.com/leanprover/lean4/pull/3750):
  Option `pp.structureProjections` is renamed to `pp.fieldNotation`, and there is now a suboption `pp.fieldNotation.generalized`
  to enable pretty printing function applications using generalized field notation (defaults to true).
  Field notation can be disabled on a function-by-function basis using the `@[pp_nodot]` attribute.
  The notation is not used for theorems.
* [#4071](https://github.com/leanprover/lean4/pull/4071) fixes interaction between app unexpanders and `pp.fieldNotation.generalized`
* [#3625](https://github.com/leanprover/lean4/pull/3625) makes `delabConstWithSignature` (used by `#check`) have the ability to put arguments "after the colon"
  to avoid printing inaccessible names.
* [#3798](https://github.com/leanprover/lean4/pull/3798),
  [#3978](https://github.com/leanprover/lean4/pull/3978),
  [#3798](https://github.com/leanprover/lean4/pull/3980):
  Adds options `pp.mvars` (default: true) and `pp.mvars.withType` (default: false).
  When `pp.mvars` is false, expression metavariables pretty print as `?_` and universe metavariables pretty print as `_`.
  When `pp.mvars.withType` is true, expression metavariables pretty print with a type ascription.
  These can be set when using `#guard_msgs` to make tests not depend on the particular names of metavariables.
* [#3917](https://github.com/leanprover/lean4/pull/3917) makes binders hoverable and gives them docstrings.
* [#4034](https://github.com/leanprover/lean4/pull/4034) makes hovers for RHS terms in `match` expressions in the Infoview reliably show the correct term.

### Library

* `Bool`/`Prop`
  * [#3508](https://github.com/leanprover/lean4/pull/3508) improves `simp` confluence for `Bool` and `Prop` terms.
  * Theorems: [#3604](https://github.com/leanprover/lean4/pull/3604)
* `Nat`
  * [#3579](https://github.com/leanprover/lean4/pull/3579) makes `Nat.succ_eq_add_one` be a simp lemma, now that `induction`/`cases` uses `n + 1` instead of `Nat.succ n`.
  * [#3808](https://github.com/leanprover/lean4/pull/3808) replaces `Nat.succ` simp rules with simprocs.
  * [#3876](https://github.com/leanprover/lean4/pull/3876) adds faster `Nat.repr` implementation in C.
* `Int`
  * Theorems: [#3890](https://github.com/leanprover/lean4/pull/3890)
* `UInt`s
  * [#3960](https://github.com/leanprover/lean4/pull/3960) improves performance of upcasting.
* `Array` and `Subarray`
  * [#3676](https://github.com/leanprover/lean4/pull/3676) removes `Array.eraseIdxAux`, `Array.eraseIdxSzAux`, and `Array.eraseIdx'`.
  * [#3648](https://github.com/leanprover/lean4/pull/3648) simplifies `Array.findIdx?`.
  * [#3851](https://github.com/leanprover/lean4/pull/3851) renames fields of `Subarray`.
* `List`
  * [#3785](https://github.com/leanprover/lean4/pull/3785) upstreams tail-recursive List operations and `@[csimp]` lemmas.
* `BitVec`
  * Theorems: [#3593](https://github.com/leanprover/lean4/pull/3593),
  [#3593](https://github.com/leanprover/lean4/pull/3593), [#3597](https://github.com/leanprover/lean4/pull/3597),
  [#3598](https://github.com/leanprover/lean4/pull/3598), [#3721](https://github.com/leanprover/lean4/pull/3721),
  [#3729](https://github.com/leanprover/lean4/pull/3729), [#3880](https://github.com/leanprover/lean4/pull/3880),
  [#4039](https://github.com/leanprover/lean4/pull/4039).
  * [#3884](https://github.com/leanprover/lean4/pull/3884) protects `Std.BitVec`.
* `String`
  * [#3832](https://github.com/leanprover/lean4/pull/3832) fixes `String.splitOn`.
  * [#3959](https://github.com/leanprover/lean4/pull/3959) adds `String.Pos.isValid`.
  * [#3959](https://github.com/leanprover/lean4/pull/3959) UTF-8 string validation.
  * [#3961](https://github.com/leanprover/lean4/pull/3961) adds a model implementation for UTF-8 encoding and decoding.
* `IO`
  * [#4097](https://github.com/leanprover/lean4/pull/4097) adds `IO.getTaskState` which returns whether a task is finished, actively running, or waiting on other Tasks to finish.

* **Refactors**
  * [#3605](https://github.com/leanprover/lean4/pull/3605) reduces imports for `Init.Data.Nat` and `Init.Data.Int`.
  * [#3613](https://github.com/leanprover/lean4/pull/3613) reduces imports for `Init.Omega.Int`.
  * [#3634](https://github.com/leanprover/lean4/pull/3634) upstreams `Std.Data.Nat`
    and [#3635](https://github.com/leanprover/lean4/pull/3635) upstreams `Std.Data.Int`.
  * [#3790](https://github.com/leanprover/lean4/pull/3790) reduces more imports for `omega`.
  * [#3694](https://github.com/leanprover/lean4/pull/3694) extends `GetElem` interface with `getElem!` and `getElem?` to simplify containers like `RBMap`.
  * [#3865](https://github.com/leanprover/lean4/pull/3865) renames `Option.toMonad` (see breaking changes below).
  * [#3882](https://github.com/leanprover/lean4/pull/3882) unifies `lexOrd` with `compareLex`.
* **Other fixes or improvements**
  * [#3765](https://github.com/leanprover/lean4/pull/3765) makes `Quotient.sound` be a `theorem`.
  * [#3645](https://github.com/leanprover/lean4/pull/3645) fixes `System.FilePath.parent` in the case of absolute paths.
  * [#3660](https://github.com/leanprover/lean4/pull/3660) `ByteArray.toUInt64LE!` and `ByteArray.toUInt64BE!` were swapped.
  * [#3881](https://github.com/leanprover/lean4/pull/3881), [#3887](https://github.com/leanprover/lean4/pull/3887) fix linearity issues in `HashMap.insertIfNew`, `HashSet.erase`, and `HashMap.erase`.
    The `HashMap.insertIfNew` fix improves `import` performance.
  * [#3830](https://github.com/leanprover/lean4/pull/3830) ensures linearity in `Parsec.many*Core`.
  * [#3930](https://github.com/leanprover/lean4/pull/3930) adds `FS.Stream.isTty` field.
  * [#3866](https://github.com/leanprover/lean4/pull/3866) deprecates `Option.toBool` in favor of `Option.isSome`.
  * [#3975](https://github.com/leanprover/lean4/pull/3975) upstreams `Data.List.Init` and `Data.Array.Init` material from Std.
  * [#3942](https://github.com/leanprover/lean4/pull/3942) adds instances that make `ac_rfl` work without Mathlib.
  * [#4010](https://github.com/leanprover/lean4/pull/4010) changes `Fin.induction` to use structural induction.
  * [02753f](https://github.com/leanprover/lean4/commit/02753f6e4c510c385efcbf71fa9a6bec50fce9ab)
    fixes bug in `reduceLeDiff` simproc.
  * [#4097](https://github.com/leanprover/lean4/pull/4097)
    adds `IO.TaskState` and `IO.getTaskState` to get the task from the Lean runtime's task manager.
* **Docs:** [#3615](https://github.com/leanprover/lean4/pull/3615), [#3664](https://github.com/leanprover/lean4/pull/3664),
  [#3707](https://github.com/leanprover/lean4/pull/3707), [#3734](https://github.com/leanprover/lean4/pull/3734),
  [#3868](https://github.com/leanprover/lean4/pull/3868), [#3861](https://github.com/leanprover/lean4/pull/3861),
  [#3869](https://github.com/leanprover/lean4/pull/3869), [#3858](https://github.com/leanprover/lean4/pull/3858),
  [#3856](https://github.com/leanprover/lean4/pull/3856), [#3857](https://github.com/leanprover/lean4/pull/3857),
  [#3867](https://github.com/leanprover/lean4/pull/3867), [#3864](https://github.com/leanprover/lean4/pull/3864),
  [#3860](https://github.com/leanprover/lean4/pull/3860), [#3859](https://github.com/leanprover/lean4/pull/3859),
  [#3871](https://github.com/leanprover/lean4/pull/3871), [#3919](https://github.com/leanprover/lean4/pull/3919).

### Lean internals

* **Defeq and WHNF algorithms**
  * [#3616](https://github.com/leanprover/lean4/pull/3616) gives better support for reducing `Nat.rec` expressions.
  * [#3774](https://github.com/leanprover/lean4/pull/3774) add tracing for "non-easy" WHNF cases.
  * [#3807](https://github.com/leanprover/lean4/pull/3807) fixes an `isDefEq` performance issue, now trying structure eta *after* lazy delta reduction.
  * [#3816](https://github.com/leanprover/lean4/pull/3816) fixes `.yesWithDeltaI` behavior to prevent increasing transparency level when reducing projections.
  * [#3837](https://github.com/leanprover/lean4/pull/3837) improves heuristic at `isDefEq`.
  * [#3965](https://github.com/leanprover/lean4/pull/3965) improves `isDefEq` for constraints of the form `t.i =?= s.i`.
  * [#3977](https://github.com/leanprover/lean4/pull/3977) improves `isDefEqProj`.
  * [#3981](https://github.com/leanprover/lean4/pull/3981) adds universe constraint approximations to be able to solve `u =?= max u ?v` using `?v = u`.
    These approximations are only applied when universe constraints cannot be postponed anymore.
  * [#4004](https://github.com/leanprover/lean4/pull/4004) improves `isDefEqProj` during typeclass resolution.
  * [#4012](https://github.com/leanprover/lean4/pull/4012) adds `backward.isDefEq.lazyProjDelta` and `backward.isDefEq.lazyWhnfCore` backwards compatibility flags.
* **Kernel**
  * [#3966](https://github.com/leanprover/lean4/pull/3966) removes dead code.
  * [#4035](https://github.com/leanprover/lean4/pull/4035) fixes mismatch for `TheoremVal` between Lean and C++.
* **Discrimination trees**
  * [423fed](https://github.com/leanprover/lean4/commit/423fed79a9de75705f34b3e8648db7e076c688d7)
    and [3218b2](https://github.com/leanprover/lean4/commit/3218b25974d33e92807af3ce42198911c256ff1d):
    simplify handling of dependent/non-dependent pi types.
* **Typeclass instance synthesis**
  * [#3638](https://github.com/leanprover/lean4/pull/3638) eta-reduces synthesized instances
  * [ce350f](https://github.com/leanprover/lean4/commit/ce350f348161e63fccde6c4a5fe1fd2070e7ce0f) fixes a linearity issue
  * [917a31](https://github.com/leanprover/lean4/commit/917a31f694f0db44d6907cc2b1485459afe74d49)
    improves performance by considering at most one answer for subgoals not containing metavariables.
    [#4008](https://github.com/leanprover/lean4/pull/4008) adds `backward.synthInstance.canonInstances` backward compatibility flag.
* **Definition processing**
  * [#3661](https://github.com/leanprover/lean4/pull/3661), [#3767](https://github.com/leanprover/lean4/pull/3767) changes automatically generated equational theorems to be named
    using suffix `.eq_<idx>` instead of `._eq_<idx>`, and `.eq_def` instead of `._unfold`. (See breaking changes below.)
    [#3675](https://github.com/leanprover/lean4/pull/3675) adds a mechanism to reserve names.
    [#3803](https://github.com/leanprover/lean4/pull/3803) fixes reserved name resolution inside namespaces and fixes handling of `match`er declarations and equation lemmas.
  * [#3662](https://github.com/leanprover/lean4/pull/3662) causes auxiliary definitions nested inside theorems to become `def`s if they are not proofs.
  * [#4006](https://github.com/leanprover/lean4/pull/4006) makes proposition fields of `structure`s be theorems.
  * [#4018](https://github.com/leanprover/lean4/pull/4018) makes it an error for a theorem to be `extern`.
  * [#4047](https://github.com/leanprover/lean4/pull/4047) improves performance making equations for well-founded recursive definitions.
* **Refactors**
  * [#3614](https://github.com/leanprover/lean4/pull/3614) avoids unfolding in `Lean.Meta.evalNat`.
  * [#3621](https://github.com/leanprover/lean4/pull/3621) centralizes functionality for `Fix`/`GuessLex`/`FunInd` in the `ArgsPacker` module.
  * [#3186](https://github.com/leanprover/lean4/pull/3186) rewrites the UnusedVariable linter to be more performant.
  * [#3589](https://github.com/leanprover/lean4/pull/3589) removes coercion from `String` to `Name` (see breaking changes below).
  * [#3237](https://github.com/leanprover/lean4/pull/3237) removes the `lines` field from `FileMap`.
  * [#3951](https://github.com/leanprover/lean4/pull/3951) makes msg parameter to `throwTacticEx` optional.
* **Diagnostics**
  * [#4016](https://github.com/leanprover/lean4/pull/4016), [#4019](https://github.com/leanprover/lean4/pull/4019),
    [#4020](https://github.com/leanprover/lean4/pull/4020), [#4030](https://github.com/leanprover/lean4/pull/4030),
    [#4031](https://github.com/leanprover/lean4/pull/4031),
    [c3714b](https://github.com/leanprover/lean4/commit/c3714bdc6d46845c0428735b283c5b48b23cbcf7),
    [#4049](https://github.com/leanprover/lean4/pull/4049) adds `set_option diagnostics true` for diagnostic counters.
    Tracks number of unfolded declarations, instances, reducible declarations, used instances, recursor reductions,
    `isDefEq` heuristic applications, among others.
    This option is suggested in exceptional situations, such as at deterministic timeout and maximum recursion depth.
  * [283587](https://github.com/leanprover/lean4/commit/283587987ab2eb3b56fbc3a19d5f33ab9e04a2ef)
    adds diagnostic information for `simp`.
  * [#4043](https://github.com/leanprover/lean4/pull/4043) adds diagnostic information for congruence theorems.
  * [#4048](https://github.com/leanprover/lean4/pull/4048) display diagnostic information
    for `set_option diagnostics true in <tactic>` and `set_option diagnostics true in <term>`.
* **Other features**
  * [#3800](https://github.com/leanprover/lean4/pull/3800) adds environment extension to record which definitions use structural or well-founded recursion.
  * [#3801](https://github.com/leanprover/lean4/pull/3801) `trace.profiler` can now export to Firefox Profiler.
  * [#3918](https://github.com/leanprover/lean4/pull/3918), [#3953](https://github.com/leanprover/lean4/pull/3953) adds `@[builtin_doc]` attribute to make docs and location of a declaration available as a builtin.
  * [#3939](https://github.com/leanprover/lean4/pull/3939) adds the `lean --json` CLI option to print messages as JSON.
  * [#3075](https://github.com/leanprover/lean4/pull/3075) improves `test_extern` command.
  * [#3970](https://github.com/leanprover/lean4/pull/3970) gives monadic generalization of `FindExpr`.
* **Docs:** [#3743](https://github.com/leanprover/lean4/pull/3743), [#3921](https://github.com/leanprover/lean4/pull/3921),
  [#3954](https://github.com/leanprover/lean4/pull/3954).
* **Other fixes:** [#3622](https://github.com/leanprover/lean4/pull/3622),
  [#3726](https://github.com/leanprover/lean4/pull/3726), [#3823](https://github.com/leanprover/lean4/pull/3823),
  [#3897](https://github.com/leanprover/lean4/pull/3897), [#3964](https://github.com/leanprover/lean4/pull/3964),
  [#3946](https://github.com/leanprover/lean4/pull/3946), [#4007](https://github.com/leanprover/lean4/pull/4007),
  [#4026](https://github.com/leanprover/lean4/pull/4026).

### Compiler, runtime, and FFI

* [#3632](https://github.com/leanprover/lean4/pull/3632) makes it possible to allocate and free thread-local runtime resources for threads not started by Lean itself.
* [#3627](https://github.com/leanprover/lean4/pull/3627) improves error message about compacting closures.
* [#3692](https://github.com/leanprover/lean4/pull/3692) fixes deadlock in `IO.Promise.resolve`.
* [#3753](https://github.com/leanprover/lean4/pull/3753) catches error code from `MoveFileEx` on Windows.
* [#4028](https://github.com/leanprover/lean4/pull/4028) fixes a double `reset` bug in `ResetReuse` transformation.
* [6e731b](https://github.com/leanprover/lean4/commit/6e731b4370000a8e7a5cfb675a7f3d7635d21f58)
  removes `interpreter` copy constructor to avoid potential memory safety issues.

### Lake

* **TOML Lake configurations**. [#3298](https://github.com/leanprover/lean4/pull/3298), [#4104](https://github.com/leanprover/lean4/pull/4104).

  Lake packages can now use TOML as a alternative configuration file format instead of Lean. If the default `lakefile.lean` is missing, Lake will also look for a `lakefile.toml`. The TOML version of the configuration supports a restricted set of the Lake configuration options, only including those which can easily mapped to a TOML data structure. The TOML syntax itself fully compiles with the TOML v1.0.0 specification.

  As part of the introduction of this new feature, we have been helping maintainers of some major packages within the ecosystem switch to this format. For example, the following is Aesop's new `lakefile.toml`:


  **[leanprover-community/aesop/lakefile.toml](https://raw.githubusercontent.com/leanprover-community/aesop/de11e0ecf372976e6d627c210573146153090d2d/lakefile.toml)**
  ```toml
  name = "aesop"
  defaultTargets = ["Aesop"]
  testRunner = "test"
  precompileModules = false

  [[require]]
  name = "batteries"
  git = "https://github.com/leanprover-community/batteries"
  rev = "main"

  [[lean_lib]]
  name = "Aesop"

  [[lean_lib]]
  name = "AesopTest"
  globs = ["AesopTest.+"]
  leanOptions = {linter.unusedVariables = false}

  [[lean_exe]]
  name = "test"
  srcDir = "scripts"
  ```

  To assist users who wish to transition their packages between configuration file formats, there is also a new `lake translate-config` command for migrating to/from TOML.

  Running `lake translate-config toml` will produce a `lakefile.toml` version of a package's `lakefile.lean`. Any configuration options unsupported by the TOML format will be discarded during translation, but the original `lakefile.lean` will remain so that you can verify the translation looks good before deleting it.

* **Build progress overhaul.** [#3835](https://github.com/leanprover/lean4/pull/3835), [#4115](https://github.com/leanprover/lean4/pull/4115), [#4127](https://github.com/leanprover/lean4/pull/4127), [#4220](https://github.com/leanprover/lean4/pull/4220), [#4232](https://github.com/leanprover/lean4/pull/4232), [#4236](https://github.com/leanprover/lean4/pull/4236).

  Builds are now managed by a top-level Lake build monitor, this makes the output of Lake builds more standardized and enables producing prettier and more configurable progress reports.

  As part of this change, job isolation has improved. Stray I/O and other build related errors in custom targets are now properly isolated and caught as part of their job. Import errors no longer cause Lake to abort the entire build and are instead localized to the build jobs of the modules in question.

  Lake also now uses ANSI escape sequences to add color and produce progress lines that update in-place; this can be toggled on and off using `--ansi` / `--no-ansi`.


  `--wfail` and `--iofail` options have been added that causes a build to fail if any of the jobs log a warning (`--wfail`) or produce any output or log information messages (`--iofail`). Unlike some other build systems, these options do **NOT** convert these logs into errors, and Lake does not abort jobs on such a log (i.e., dependent jobs will still continue unimpeded).

* `lake test`. [#3779](https://github.com/leanprover/lean4/pull/3779).

  Lake now has a built-in `test` command which will run a script or executable labelled `@[test_runner]` (in Lean) or defined as the `testRunner` (in TOML) in the root package.

  Lake also provides a `lake check-test` command which will exit with code `0` if the package has a properly configured test runner or error with `1` otherwise.

* `lake lean`. [#3793](https://github.com/leanprover/lean4/pull/3793).

  The new command `lake lean <file> [-- <args...>]` functions like `lake env lean <file> <args...>`, except that it builds the imports of `file` before running `lean`. This makes it very useful for running test or example code that imports modules that are not guaranteed to have been built beforehand.

* **Miscellaneous bug fixes and improvements**
  * [#3609](https://github.com/leanprover/lean4/pull/3609) `LEAN_GITHASH` environment variable to override the detected Git hash for Lean when computing traces, useful for testing custom builds of Lean.
  * [#3795](https://github.com/leanprover/lean4/pull/3795) improves relative package directory path normalization in the pre-rename check.
  * [#3957](https://github.com/leanprover/lean4/pull/3957) fixes handling of packages that appear multiple times in a dependency tree.
  * [#3999](https://github.com/leanprover/lean4/pull/3999) makes it an error for there to be a mismatch between a package name and what it is required as. Also adds a special message for the `std`-to-`batteries` rename.
  * [#4033](https://github.com/leanprover/lean4/pull/4033) fixes quiet mode.
* **Docs:** [#3704](https://github.com/leanprover/lean4/pull/3704).

### DevOps

* [#3536](https://github.com/leanprover/lean4/pull/3536) and [#3833](https://github.com/leanprover/lean4/pull/3833)
  add a checklist for the release process.
* [#3600](https://github.com/leanprover/lean4/pull/3600) runs nix-ci more uniformly.
* [#3612](https://github.com/leanprover/lean4/pull/3612) avoids argument limits when building on Windows.
* [#3682](https://github.com/leanprover/lean4/pull/3682) builds Lean's `.o` files in parallel to rest of core.
* [#3601](https://github.com/leanprover/lean4/pull/3601)
  changes the way Lean is built on Windows (see breaking changes below).
  As a result, Lake now dynamically links executables with `supportInterpreter := true` on Windows
  to `libleanshared.dll` and `libInit_shared.dll`. Therefore, such executables will not run
  unless those shared libraries are co-located with the executables or part of `PATH`.
  Running the executable via `lake exe` will ensure these libraries are part of `PATH`.

  In a related change, the signature of the `nativeFacets` Lake configuration options has changed
  from a static `Array` to a function `(shouldExport : Bool) → Array`.
  See its docstring or Lake's [README](https://github.com/leanprover/lean4/blob/releases/v4.8.0/src/lake/README.md) for further details on the changed option.
* [#3690](https://github.com/leanprover/lean4/pull/3690) marks "Build matrix complete" as canceled if the build is canceled.
* [#3700](https://github.com/leanprover/lean4/pull/3700), [#3702](https://github.com/leanprover/lean4/pull/3702),
  [#3701](https://github.com/leanprover/lean4/pull/3701), [#3834](https://github.com/leanprover/lean4/pull/3834),
  [#3923](https://github.com/leanprover/lean4/pull/3923): fixes and improvements for std and mathlib CI.
* [#3712](https://github.com/leanprover/lean4/pull/3712) fixes `nix build .` on macOS.
* [#3717](https://github.com/leanprover/lean4/pull/3717) replaces `shell.nix` in devShell with `flake.nix`.
* [#3715](https://github.com/leanprover/lean4/pull/3715) and [#3790](https://github.com/leanprover/lean4/pull/3790) add test result summaries.
* [#3971](https://github.com/leanprover/lean4/pull/3971) prevents stage0 changes via the merge queue.
* [#3979](https://github.com/leanprover/lean4/pull/3979) adds handling for `changes-stage0` label.
* [#3952](https://github.com/leanprover/lean4/pull/3952) adds a script to summarize GitHub issues.
* [18a699](https://github.com/leanprover/lean4/commit/18a69914da53dbe37c91bc2b9ce65e1dc01752b6)
  fixes asan linking

### Breaking changes

* Due to the major Lake build refactor, code using the affected parts of the Lake API or relying on the previous output format of Lake builds is likely to have been broken. We have tried to minimize the breakages and, where possible, old definitions have been marked `@[deprecated]` with a reference to the new alternative.

* Executables configured with `supportInterpreter := true` on Windows should now be run via `lake exe` to function properly.

* Automatically generated equational theorems are now named using suffix `.eq_<idx>` instead of `._eq_<idx>`, and `.eq_def` instead of `._unfold`. Example:
```
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

theorem ex : fact 0 = 1 := by unfold fact; decide

#check fact.eq_1
-- fact.eq_1 : fact 0 = 1

#check fact.eq_2
-- fact.eq_2 (n : Nat) : fact (Nat.succ n) = (n + 1) * fact n

#check fact.eq_def
/-
fact.eq_def :
  ∀ (x : Nat),
    fact x =
      match x with
      | 0 => 1
      | Nat.succ n => (n + 1) * fact n
-/
```

* The coercion from `String` to `Name` was removed. Previously, it was `Name.mkSimple`, which does not separate strings at dots, but experience showed that this is not always the desired coercion. For the previous behavior, manually insert a call to `Name.mkSimple`.

* The `Subarray` fields `as`, `h₁` and `h₂` have been renamed to `array`, `start_le_stop`, and `stop_le_array_size`, respectively. This more closely follows standard Lean conventions. Deprecated aliases for the field projections were added; these will be removed in a future release.

* The change to the instance name algorithm (described above) can break projects that made use of the auto-generated names.

* `Option.toMonad` has been renamed to `Option.getM` and the unneeded `[Monad m]` instance argument has been removed.

````
