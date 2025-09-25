/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: figure out why this is needed with the new codegen
set_option maxRecDepth 9000

#doc (Manual) "Lean 4.20.0 (2025-06-02)" =>
%%%
tag := "release-v4.20.0"
file := "v4.20.0"
%%%

````markdown
For this release, 346 changes landed. In addition to the 108 feature additions and 85 fixes listed below there were 6 refactoring changes, 7 documentation improvements, 8 performance improvements, 4 improvements to the test suite and 126 other changes.

## Highlights

The Lean v4.20.0 release brings multiple new features, bug fixes, improvements to Lake, and groundwork for the module system.

### Language Features

* [#6432](https://github.com/leanprover/lean4/pull/6432) implements tactics called `extract_lets` and `lift_lets` that
  manipulate `let`/`let_fun` expressions. The `extract_lets` tactic
  creates new local declarations extracted from any `let` and `let_fun`
  expressions in the main goal. For top-level lets in the target, it is
  like the `intros` tactic, but in general it can extract lets from deeper
  subexpressions as well. The `lift_lets` tactic moves `let` and `let_fun`
  expressions as far out of an expression as possible, but it does not
  extract any new local declarations. The option `extract_lets +lift`
  combines these behaviors.

* [#7806](https://github.com/leanprover/lean4/pull/7806) modifies the syntaxes of the `ext`, `intro` and `enter` conv
  tactics to accept `_`. The introduced binder is an inaccessible name.

* [#7830](https://github.com/leanprover/lean4/pull/7830) modifies the syntax of `induction`, `cases`, and other tactics
  that use `Lean.Parser.Tactic.inductionAlts`. If a case omits `=> ...`
  then it is assumed to be `=> ?_`. Example:
  ```lean
  example (p : Nat × Nat) : p.1 = p.1 := by
    cases p with | _ p1 p2
    /-
    case mk
    p1 p2 : Nat
    ⊢ (p1, p2).fst = (p1, p2).fst
    -/
  ```
  This works with multiple cases as well. Example:
  ```lean
  example (n : Nat) : n + 1 = 1 + n := by
    induction n with | zero | succ n ih
    /-
    case zero
    ⊢ 0 + 1 = 1 + 0

    case succ
    n : Nat
    ih : n + 1 = 1 + n
    ⊢ n + 1 + 1 = 1 + (n + 1)
    -/
  ```
  The `induction n with | zero | succ n ih` is short for `induction n with
  | zero | succ n ih => ?_`, which is short for `induction n with | zero
  => ?_ | succ n ih => ?_`. Note that a consequence of parsing is that
  only the last alternative can omit `=>`. Any `=>`-free alternatives
  before an alternative with `=>` will be a part of that alternative.

* [#7831](https://github.com/leanprover/lean4/pull/7831) adds extensibility to the `evalAndSuggest` procedure used to
  implement `try?`. Users can now implement their own handlers for any
  tactic.
  ```lean
  -- Install a `TryTactic` handler for `assumption`
  @[try_tactic assumption]
  def evalTryApply : TryTactic := fun tac => do
    -- We just use the default implementation, but return a different tactic.
    evalAssumption tac
    `(tactic| (trace "worked"; assumption))

  /-- info: Try this: · trace "worked"; assumption -/
  #guard_msgs (info) in
  example (h : False) : False := by
    try? (max := 1) -- at most one solution

  -- `try?` uses `evalAndSuggest` the attribute `[try_tactic]` is used to extend `evalAndSuggest`.
  -- Let's define our own `try?` that uses `evalAndSuggest`
  elab stx:"my_try?" : tactic => do
    -- Things to try
    let toTry ← `(tactic| attempt_all | assumption | apply True | rfl)
    evalAndSuggest stx toTry

  /--
  info: Try these:
  • · trace "worked"; assumption
  • rfl
  -/
  #guard_msgs (info) in
  example (a : Nat) (h : a = a) : a = a := by
    my_try?
  ```

* [#8055](https://github.com/leanprover/lean4/pull/8055) adds an implementation of an async IO multiplexing framework as
  well as an implementation of it for the `Timer` API in order to
  demonstrate it.

* [#8088](https://github.com/leanprover/lean4/pull/8088) adds the “unfolding” variant of the functional induction and
  functional cases principles, under the name `foo.induct_unfolding` resp.
  `foo.fun_cases_unfolding`. These theorems combine induction over the
  structure of a recursive function with the unfolding of that function,
  and should be more reliable, easier to use and more efficient than just
  case-splitting and then rewriting with equational theorems.

  For example instead of

  ```
  ackermann.induct
    (motive : Nat → Nat → Prop)
    (case1 : ∀ (m : Nat), motive 0 m)
    (case2 : ∀ (n : Nat), motive n 1 → motive (Nat.succ n) 0)
    (case3 : ∀ (n m : Nat), motive (n + 1) m → motive n (ackermann (n + 1) m) → motive (Nat.succ n) (Nat.succ m))
    (x x : Nat) : motive x x
  ```

  one gets

  ```
  ackermann.fun_cases_unfolding
    (motive : Nat → Nat → Nat → Prop)
    (case1 : ∀ (m : Nat), motive 0 m (m + 1))
    (case2 : ∀ (n : Nat), motive n.succ 0 (ackermann n 1))
    (case3 : ∀ (n m : Nat), motive n.succ m.succ (ackermann n (ackermann (n + 1) m)))
    (x✝ x✝¹ : Nat) : motive x✝ x✝¹ (ackermann x✝ x✝¹)
  ```

* [#8097](https://github.com/leanprover/lean4/pull/8097) adds support for inductive and coinductive predicates defined
  using lattice theoretic structures on `Prop`. These are syntactically
  defined using `greatest_fixpoint` or `least_fixpoint` termination
  clauses for recursive `Prop`-valued functions. The functionality relies
  on `partial_fixpoint` machinery and requires function definitions to be
  monotone. For non-mutually recursive predicates, an appropriate
  (co)induction proof principle (given by Park induction) is generated.

### Library Highlights

[#8004](https://github.com/leanprover/lean4/pull/8004) adds extensional hash maps and hash sets under the names
  `Std.ExtDHashMap`, `Std.ExtHashMap` and `Std.ExtHashSet`. Extensional
  hash maps work like regular hash maps, except that they have
  extensionality lemmas which make them easier to use in proofs. This
  however makes it also impossible to regularly iterate over its entries.

Other notable library developments in this release include:
- Updates to the `Option` API,
- Async runtime developments: added support for multiplexing via UDP and TCP sockets, as well as channels,
- New `BitVec` definitions related to overflow handling,
- New lemmas for `Nat.lcm`, and `Int` variants for `Nat.gcd` and `Nat.lcm`,
- Upstreams from Mathlib related to `Nat` and `Int`,
- Additions to numeric types APIs, such as `UIntX.ofInt`, `Fin.ofNat'_mul` and `Fin.mul_ofNat'`, `Int.toNat_sub''`,
- Updates to `Perm` API in `Array`, `List`, and added support for `Vector`,
- Additional lemmas for `Array`/`List`/`Vector`.

### Breaking Changes

* [#7474](https://github.com/leanprover/lean4/pull/7474) updates `rw?`, `show_term`, and other tactic-suggesting tactics
  to suggest `expose_names` when necessary and validate tactics prior to
  suggesting them, as `exact?` already did, and it also ensures all such
  tactics produce hover info in the messages showing tactic suggestions.

  This introduces a **breaking change** in the `TryThis` API: the `type?` parameter
  of `addRewriteSuggestion` is now an `LOption`, not an `Option`, to obviate the need
  for a hack we previously used to indicate that a rewrite closed the goal.

* [#7789](https://github.com/leanprover/lean4/pull/7789) fixes `lean` potentially changing or interpreting arguments
  after `--run`.

  **Breaking change**: The Lean file to run must now be passed directly
  after `--run`, which accidentally was not enforced before.

* [#7813](https://github.com/leanprover/lean4/pull/7813) fixes an issue where `let n : Nat := sorry` in the Infoview
  pretty prints as ``n : ℕ := sorry `«Foo:17:17»``. This was caused by
  top-level expressions being pretty printed with the same rules as
  Infoview hovers. Closes [#6715](https://github.com/leanprover/lean4/issues/6715). Refactors `Lean.Widget.ppExprTagged`; now
  it takes a delaborator, and downstream users should configure their own
  pretty printer option overrides if necessary if they used the `explicit`
  argument (see `Lean.Widget.makePopup.ppExprForPopup` for an example).
  **Breaking change:** `ppExprTagged` does not set `pp.proofs` on the root
  expression.

* [#7855](https://github.com/leanprover/lean4/pull/7855) moves `ReflBEq` to `Init.Core` and changes `LawfulBEq` to extend
  `ReflBEq`.

  **Breaking changes:**
  - The `refl` field of `ReflBEq` has been renamed to `rfl` to match
  `LawfulBEq`
  - `LawfulBEq` extends `ReflBEq`, so in particular `LawfulBEq.rfl` is no
  longer valid

* [#7873](https://github.com/leanprover/lean4/pull/7873) fixes a number of bugs related to the handling of the source
  search path in the language server, where deleting files could cause
  several features to stop functioning and both untitled files and files
  that don't exist on disc could have conflicting module names.

  See the PR description for the details on changes in URI <-> module name conversion.

  **Breaking changes:**
  - `Server.documentUriFromModule` has been renamed to
  `Server.documentUriFromModule?` and doesn't take a `SearchPath` argument
  anymore, as the `SearchPath` is now computed from the `LEAN_SRC_PATH`
  environment variable. It has also been moved from `Lean.Server.GoTo` to
  `Lean.Server.Utils`.
  - `Server.moduleFromDocumentUri` does not take a `SearchPath` argument
  anymore and won't return an `Option` anymore. It has also been moved
  from `Lean.Server.GoTo` to `Lean.Server.Utils`.
  - The `System.SearchPath.searchModuleNameOfUri` function has been
  removed. It is recommended to use `Server.moduleFromDocumentUri`
  instead.
  - The `initSrcSearchPath` function has been renamed to
  `getSrcSearchPath` and has been moved from `Lean.Util.Paths` to
  `Lean.Util.Path`. It also doesn't need to take a `pkgSearchPath`
  argument anymore.

* [#7967](https://github.com/leanprover/lean4/pull/7967) adds a `bootstrap` option to Lake which is used to identify the
  core Lean package. This enables Lake to use the current stage's include
  directory rather than the Lean toolchains when compiling Lean with Lean
  in core.

  **Breaking change:** The Lean library directory is no longer part of
  `getLeanLinkSharedFlags`. FFI users should provide this option
  separately when linking to Lean (e.g.. via `s!"-L{(←getLeanLibDir).toString}"`).
  See the FFI example for a demonstration.

## Language

* [#6325](https://github.com/leanprover/lean4/pull/6325) ensures that environments can be loaded, repeatedly, without
  executing arbitrary code

* [#6432](https://github.com/leanprover/lean4/pull/6432) implements tactics called `extract_lets` and `lift_lets` that
  manipulate `let`/`let_fun` expressions. The `extract_lets` tactic
  creates new local declarations extracted from any `let` and `let_fun`
  expressions in the main goal. For top-level lets in the target, it is
  like the `intros` tactic, but in general it can extract lets from deeper
  subexpressions as well. The `lift_lets` tactic moves `let` and `let_fun`
  expressions as far out of an expression as possible, but it does not
  extract any new local declarations. The option `extract_lets +lift`
  combines these behaviors.

* [#7474](https://github.com/leanprover/lean4/pull/7474) updates `rw?`, `show_term`, and other tactic-suggesting tactics
  to suggest `expose_names` when necessary and validate tactics prior to
  suggesting them, as `exact?` already did, and it also ensures all such
  tactics produce hover info in the messages showing tactic suggestions.

* [#7797](https://github.com/leanprover/lean4/pull/7797) adds a monolithic `CommRing` class, for internal use by `grind`,
  and includes instances for `Int`/`BitVec`/`IntX`/`UIntX`.

* [#7803](https://github.com/leanprover/lean4/pull/7803) adds normalization rules for function composition to `grind`.

* [#7806](https://github.com/leanprover/lean4/pull/7806) modifies the syntaxes of the `ext`, `intro` and `enter` conv
  tactics to accept `_`. The introduced binder is an inaccessible name.

* [#7808](https://github.com/leanprover/lean4/pull/7808) adds missing forall normalization rules to `grind`.

* [#7816](https://github.com/leanprover/lean4/pull/7816) fixes an issue where `x.f.g` wouldn't work but `(x.f).g` would
  when `x.f` is generalized field notation. The problem was that `x.f.g`
  would assume `x : T` should be the first explicit argument to `T.f`. Now
  it uses consistent argument insertion rules. Closes #6400.

* [#7825](https://github.com/leanprover/lean4/pull/7825) improves support for `Nat` in the `cutsat` procedure used in
  `grind`:

  - `cutsat` no longer *pollutes* the local context with facts of the form
  `-1 * NatCast.natCast x <= 0` for each `x : Nat`. These facts are now
  stored internally in the `cutsat` state.
  - A single context is now used for all `Nat` terms.

* [#7829](https://github.com/leanprover/lean4/pull/7829) fixes an issue in the cutsat counterexamples. It removes the
  optimization (`Cutsat.State.terms`) that was used to avoid the new
  theorem `eq_def`. In the two new tests, prior to this PR, `cutsat`
  produced a bogus counterexample with `b := 2`.

* [#7830](https://github.com/leanprover/lean4/pull/7830) modifies the syntax of `induction`, `cases`, and other tactics
  that use `Lean.Parser.Tactic.inductionAlts`. If a case omits `=> ...`
  then it is assumed to be `=> ?_`. Example:
  ```lean
  example (p : Nat × Nat) : p.1 = p.1 := by
    cases p with | _ p1 p2
    /-
    case mk
    p1 p2 : Nat
    ⊢ (p1, p2).fst = (p1, p2).fst
    -/
  ```
  This works with multiple cases as well. Example:
  ```lean
  example (n : Nat) : n + 1 = 1 + n := by
    induction n with | zero | succ n ih
    /-
    case zero
    ⊢ 0 + 1 = 1 + 0

    case succ
    n : Nat
    ih : n + 1 = 1 + n
    ⊢ n + 1 + 1 = 1 + (n + 1)
    -/
  ```
  The `induction n with | zero | succ n ih` is short for `induction n with
  | zero | succ n ih => ?_`, which is short for `induction n with | zero
  => ?_ | succ n ih => ?_`. Note that a consequence of parsing is that
  only the last alternative can omit `=>`. Any `=>`-free alternatives
  before an alternative with `=>` will be a part of that alternative.

* [#7831](https://github.com/leanprover/lean4/pull/7831) adds extensibility to the `evalAndSuggest` procedure used to
  implement `try?`. Users can now implement their own handlers for any
  tactic. The new test demonstrates how this feature works.

* [#7859](https://github.com/leanprover/lean4/pull/7859) allows the LRAT parser to accept any proof that derives the
  empty clause at somepoint, not necessarily in the last line. Some tools
  like lrat-trim occasionally include deletions after the derivation of
  the empty clause but the proof is sound as long as it soundly derives
  the empty clause somewhere.

* [#7861](https://github.com/leanprover/lean4/pull/7861) fixes an issue that prevented theorems from being activated in
  `grind`.

* [#7862](https://github.com/leanprover/lean4/pull/7862) improves the normalization of `Bool` terms in `grind`. Recall
  that `grind` currently does not case split on Boolean terms to reduce
  the size of the search space.

* [#7864](https://github.com/leanprover/lean4/pull/7864) adds support to `grind` for case splitting on implications of
  the form `p -> q` and `(h : p) -> q h`. See the new option `(splitImp :=
  true)`.

* [#7865](https://github.com/leanprover/lean4/pull/7865) adds a missing propagation rule for implication in `grind`. It
  also avoids unnecessary case-splits on implications.

* [#7870](https://github.com/leanprover/lean4/pull/7870) adds a mixin typeclass for `Lean.Grind.CommRing` recording the
  characteristic of the ring, and constructs instances for `Int`, `IntX`,
  `UIntX`, and `BitVec`.

* [#7885](https://github.com/leanprover/lean4/pull/7885) fixes the counterexamples produced by the cutsat procedure in
  `grind` for examples containing `Nat` terms.

* [#7892](https://github.com/leanprover/lean4/pull/7892) improves the support for `funext` in `grind`. We will push
  another PR to minimize the number of case-splits later.

* [#7902](https://github.com/leanprover/lean4/pull/7902) introduces a dedicated option for checking whether elaborators
  are running in the language server.

* [#7905](https://github.com/leanprover/lean4/pull/7905) fixes an issue introduced bug #6125 where an `inductive` or
  `structure` with an autoimplicit parameter with a type that has a
  metavariable would lead to a panic. Closes #7788.

* [#7907](https://github.com/leanprover/lean4/pull/7907) fixes two bugs in `grind`.
  1. Model-based theory combination was creating type incorrect terms.
  2. `Nat.cast` vs `NatCast.natCast` issue during normalization.

* [#7914](https://github.com/leanprover/lean4/pull/7914) adds a function hook `PersistentEnvExtension.saveEntriesFn` that
  can be used to store server-only metadata such as position information
  and docstrings that should not affect (re)builds.

* [#7920](https://github.com/leanprover/lean4/pull/7920) introduces a fast path based on comparing the (cached) hash
  value to the `DecidableEq` instance of the core expression data type in
  `bv_decide`'s bitblaster.

* [#7926](https://github.com/leanprover/lean4/pull/7926) fixes two issues that were preventing `grind` to solve
  `getElem?_eq_some_iff`.
  1. Missing propagation rule for `Exists p = False`
  2. Missing conditions at `isCongrToPrevSplit` a filter for discarding
  unnecessary case-splits.

* [#7937](https://github.com/leanprover/lean4/pull/7937) implements a lookahead feature to reduce the size of the search
  space in `grind`. It is currently effective only for arithmetic atoms.

* [#7949](https://github.com/leanprover/lean4/pull/7949) adds the attribute `[grind ext]`. It is used to select which
  `[ext]` theorems should be used by `grind`. The option `grind +extAll`
  instructs `grind` to use all `[ext]` theorems available in the
  environment.
  After update stage0, we need to add the builtin `[grind ext]`
  annotations to key theorems such as `funext`.

* [#7950](https://github.com/leanprover/lean4/pull/7950) modifies `all_goals` so that in recovery mode it commits changes
  to the state only for those goals for which the tactic succeeds (while
  preserving the new message log state). Before, we were trusting that
  failing tactics left things in a reasonable state, but now we roll back
  and admit the goal. The changes also fixes a bug where we were rolling
  back only the metacontext state and not the tactic state, leading to an
  inconsistent state (a goal list with metavariables not in the
  metacontext). Closes #7883

* [#7952](https://github.com/leanprover/lean4/pull/7952) makes two improvements to the local context when there are
  autobound implicits in `variable`s. First, the local context no longer
  has two copies of every variable (the local context is rebuilt if the
  types of autobound implicits have metavariables). Second, these
  metavariables get names using the same algorithm used by binders that
  appear in declarations (with `mkForallFVars'` instead of
  `mkForallFVars`).

* [#7957](https://github.com/leanprover/lean4/pull/7957) ensures that `mkAppM` can be used to construct terms that are
  only type-correct at at default transparency, even if we are in
  `withReducible` (e.g. in simp), so that simp does not stumble over
  simplifying `let` expression with simplifiable type.reliable.

* [#7961](https://github.com/leanprover/lean4/pull/7961) fixes a bug in bv_decide where if it was presented with a match
  on an enum with as many arms as constructors but the last arm being a
  default match it would (wrongly) give up on the match.

* [#7975](https://github.com/leanprover/lean4/pull/7975) reduces the priority of the parent projections of
  `Lean.Grind.CommRing`, to avoid these being used in typeclass inference
  in Mathlib.

* [#7976](https://github.com/leanprover/lean4/pull/7976) ensure that `bv_decide` can handle the simp normal form of a
  shift.

* [#7978](https://github.com/leanprover/lean4/pull/7978) adds a repro for a non-determinism problem in `grind`.

* [#7980](https://github.com/leanprover/lean4/pull/7980) adds a simple type for representing monomials in a `CommRing`.
  This is going to be used in `grind`.

* [#7986](https://github.com/leanprover/lean4/pull/7986) implements reverse lexicographical and graded reverse
  lexicographical orders for `CommRing` monomials.

* [#7989](https://github.com/leanprover/lean4/pull/7989) adds functions and theorems for `CommRing` multivariate
  polynomials.

* [#7992](https://github.com/leanprover/lean4/pull/7992) add a function for converting `CommRing` expressions into
  multivariate polynomials.

* [#7997](https://github.com/leanprover/lean4/pull/7997) removes all type annotations (optional paramters, auto
  parameters, out params, semi-out params, not just optional parameters as
  before) from the type of functional induction principles.

* [#8011](https://github.com/leanprover/lean4/pull/8011) adds `IsCharP` support to the multivariate‑polynomial library in
  `CommRing`.

* [#8012](https://github.com/leanprover/lean4/pull/8012) adds the option `debug.terminalTacticsAsSorry`. When enabled,
  terminal tactics such as `grind` and `omega` are replaced with `sorry`.
  Useful for debugging and fixing bootstrapping issues.

* [#8014](https://github.com/leanprover/lean4/pull/8014) makes `RArray` universe polymorphic.

* [#8016](https://github.com/leanprover/lean4/pull/8016) fixes several issues in the `CommRing` multivariate polynomial
  library:
  1. Replaces the previous array type with the universe polymorphic
  `RArray`.
  2. Properly eliminates cancelled monomials.
  3. Sorts monomials in decreasing order.
  4. Marks the parameter `p` of the `IsCharP` class as an output
  parameter.
  5. Adds `LawfulBEq` instances for the types `Power`, `Mon`, and `Poly`.

* [#8025](https://github.com/leanprover/lean4/pull/8025) simplifies the `CommRing` monomials, and adds
  1. Monomial `lcm`
  2. Monomial division
  3. S-polynomials

* [#8029](https://github.com/leanprover/lean4/pull/8029) implements basic support for `CommRing` in `grind`. Terms are
  already being reified and normalized. We still need to process the
  equations, but `grind` can already prove simple examples such as:
  ```lean
  open Lean.Grind in
  example [CommRing α] (x : α) : (x + 1)*(x - 1) = x^2 - 1 := by
    grind +ring

* [#8032](https://github.com/leanprover/lean4/pull/8032) adds support to `grind` for detecting unsatisfiable commutative
  ring equations when the ring characteristic is known. Examples:
  ```lean
  example (x : Int) : (x + 1)*(x - 1) = x^2 → False := by
    grind +ring

* [#8033](https://github.com/leanprover/lean4/pull/8033) adds functions for converting `CommRing` reified terms back into
  Lean expressions.

* [#8036](https://github.com/leanprover/lean4/pull/8036) fixes a linearity issue in `bv_decide`'s bitblaster, caused by
  the fact that the higher order combinators `AIG.RefVec.zip` and
  `AIG.RefVec.fold` were not being properly specialised.

* [#8042](https://github.com/leanprover/lean4/pull/8042) makes `IntCast` a field of `Lean.Grind.CommRing`, along with
  additional axioms relating it to negation of `OfNat`. This allows use to
  use existing instances which are not definitionally equal to the
  previously given construction.

* [#8043](https://github.com/leanprover/lean4/pull/8043) adds `NullCert` type for representing Nullstellensatz
  certificates that will be produced by the new commutative ring procedure
  in `grind`.

* [#8050](https://github.com/leanprover/lean4/pull/8050) fixes missing trace messages when produced inside `realizeConst`

* [#8055](https://github.com/leanprover/lean4/pull/8055) adds an implementation of an async IO multiplexing framework as
  well as an implementation of it for the `Timer` API in order to
  demonstrate it.

* [#8064](https://github.com/leanprover/lean4/pull/8064) adds a failing `grind` test, showing a bug where grind is trying
  to assign a metavariable incorrectly.

* [#8065](https://github.com/leanprover/lean4/pull/8065) adds a (failing) test case for an obstacle I've been running
  into setting up `grind` for `HashMap`.

* [#8068](https://github.com/leanprover/lean4/pull/8068) ensures that for modules opted into the experimental module
  system, we do not import module docstrings or declaration ranges.

* [#8076](https://github.com/leanprover/lean4/pull/8076) fixes `simp?!`, `simp_all?!` and `dsimp?!` to do auto-unfolding.

* [#8077](https://github.com/leanprover/lean4/pull/8077) adds simprocs to simplify appends of non-overlapping Bitvector
  adds. We add a simproc instead of just a `simp` lemma to ensure that we
  correctly rewrite bitvector appends. Since bitvector appends lead to
  computation at the bitvector width level, it seems to be more stable to
  write a simproc.

* [#8083](https://github.com/leanprover/lean4/pull/8083) fixes #8081.

* [#8086](https://github.com/leanprover/lean4/pull/8086) makes sure that the functional induction priciples for mutually
  recursive structural functions with extra parameters are split deeply,
  as expected.

* [#8088](https://github.com/leanprover/lean4/pull/8088) adds the “unfolding” variant of the functional induction and
  functional cases principles, under the name `foo.induct_unfolding` resp.
  `foo.fun_cases_unfolding`. These theorems combine induction over the
  structure of a recursive function with the unfolding of that function,
  and should be more reliable, easier to use and more efficient than just
  case-splitting and then rewriting with equational theorems.

* [#8090](https://github.com/leanprover/lean4/pull/8090) adjusts the experimental module system to elide theorem bodies
  (i.e. proofs) from being imported into other modules.

* [#8094](https://github.com/leanprover/lean4/pull/8094) fixes the generation of functional induction principles for
  functions with nested nested well-founded recursion and late fixed
  parameters. This is a follow-up for #7166. Fixes #8093.

* [#8096](https://github.com/leanprover/lean4/pull/8096) lets `induction` accept eliminator where the motive application
  in the conclusion has complex arguments; these are abstracted over using
  `kabstract` if possible. This feature will go well with unfolding
  induction principles (#8088).

* [#8097](https://github.com/leanprover/lean4/pull/8097) adds support for inductive and coinductive predicates defined
  using lattice theoretic structures on `Prop`. These are syntactically
  defined using `greatest_fixpoint` or `least_fixpoint` termination
  clauses for recursive `Prop`-valued functions. The functionality relies
  on `partial_fixpoint` machinery and requires function definitions to be
  monotone. For non-mutually recursive predicates, an appropriate
  (co)induction proof principle (given by Park induction) is generated.

* [#8101](https://github.com/leanprover/lean4/pull/8101) fixes a parallelism regression where linters that e.g. check for
  errors in the command would no longer find such messages.

* [#8102](https://github.com/leanprover/lean4/pull/8102) allows ASCII `<-` in `if let` clauses, for consistency with
  bind, where both are allowed. Fixes #8098.

* [#8111](https://github.com/leanprover/lean4/pull/8111) adds the helper type class `NoZeroNatDivisors` for the
  commutative ring procedure in `grind`. Core only implements it for
  `Int`. It can be instantiated in Mathlib for any type `A` that
  implements `NoZeroSMulDivisors Nat A`.
  See `findSimp?` and `PolyDerivation` for details on how this instance
  impacts the commutative ring procedure.

* [#8122](https://github.com/leanprover/lean4/pull/8122) implements the generation of compact proof terms for
  Nullstellensatz certificates in the new commutative ring procedure in
  `grind`. Some examples:
  ```lean
  example [CommRing α] (x y : α) : x = 1 → y = 2 → 2*x + y = 4 := by
    grind +ring

* [#8126](https://github.com/leanprover/lean4/pull/8126) implements the main loop of the new commutative ring procedure
  in `grind`. In the main loop, for each polynomial `p` in the todo queue,
  the procedure:
  - Simplifies it using the current basis.
  - Computes critical pairs with polynomials already in the basis and adds
  them to the queue.

* [#8128](https://github.com/leanprover/lean4/pull/8128) implements equality propagation in the new commutative ring
  procedure in `grind`. The idea is to propagate implied equalities back
  to the `grind` core module that does congruence closure. In the
  following example, the equalities: `x^2*y = 1` and `x*y^2 - y = 0` imply
  that `y*x` is equal to `y*x*y`, which implies by congruence that `f
  (y*x) = f (y*x*y)`.
  ```lean
  example [CommRing α] (x y : α) (f : α → Nat) : x^2*y = 1 → x*y^2 - y = 0 → f (y*x) = f (y*x*y) := by
    grind +ring
  ```

* [#8129](https://github.com/leanprover/lean4/pull/8129) updates the If-Normalization example, to separately give an
  implementation and subsequently prove the spec (using fun_induction),
  instead of previously building a term in the subtype directly. At the
  same time, adds a (failing) `grind` test case illustrating a problem
  with unused match witnesses.

* [#8131](https://github.com/leanprover/lean4/pull/8131) adds a configuration option that controls the maximum number of
  steps the commutative-ring procedure in `grind` performs.

* [#8133](https://github.com/leanprover/lean4/pull/8133) fixes the monomial order used by the commutative ring procedure
  in `grind`. The following new test now terminates quickly.
  ```lean
  example [CommRing α] (a b c : α)
    : a + b + c = 3 →
      a^2 + b^2 + c^2 = 5 →
      a^3 + b^3 + c^3 = 7 →
      a^4 + b^4 + c^4 = 9 := by
    grind +ring
  ```

* [#8134](https://github.com/leanprover/lean4/pull/8134) ensures that `set_option grind.debug true` works properly when
  using `grind +ring`. It also adds the helper functions `mkPropEq` and
  `mkExpectedPropHint`.

* [#8137](https://github.com/leanprover/lean4/pull/8137) improves equality propagation (also known as theory combination)
  and polynomial simplification for rings that do not implement the
  `NoZeroNatDivisors` class. With these fixes, `grind` can now solve:
  ```lean
  example [CommRing α] (a b c : α) (f : α → Nat)
    : a + b + c = 3 →
      a^2 + b^2 + c^2 = 5 →
      a^3 + b^3 + c^3 = 7 →
      f (a^4 + b^4) + f (9 - c^4) ≠ 1 := by
    grind +ring
  ```
  This example uses the commutative ring procedure, the linear integer
  arithmetic solver, and congruence closure.
  For rings that implement `NoZeroNatDivisors`, a polynomial is now also
  divided by the greatest common divisor (gcd) of its coefficients when it
  is inserted into the basis.

* [#8157](https://github.com/leanprover/lean4/pull/8157) fixes an incompatibility of `replayConst` as used by e.g.
  `aesop` with `native_decide`-using tactics such as `bv_decide`

* [#8158](https://github.com/leanprover/lean4/pull/8158) fixes the `grind +splitImp` and the arrow propagator. Given `p :
  Prop`, the propagator was incorrectly assuming `A` was always a
  proposition in an arrow `A -> p`. also adds a missing
  normalization rule to `grind`.

* [#8159](https://github.com/leanprover/lean4/pull/8159) adds support for the following import variants to the
  experimental module system:

  * `private import`: Makes the imported constants available only in
  non-exported contexts such as proofs. In particular, the import will not
  be loaded, or required to exist at all, when the current module is
  imported into other modules.
  * `import all`: Makes non-exported information such as proofs of the
  imported module available in non-exported contexts in the current
  module. Main purpose is to allow for reasoning about imported
  definitions when they would otherwise be opaque. TODO: adjust name
  resolution so that imported `private` decls are accessible through
  syntax.

* [#8161](https://github.com/leanprover/lean4/pull/8161) changes `Lean.Grind.CommRing` to inline the `NatCast` instance
  (i.e. to be provided by the user) rather than constructing one from the
  existing data. Without this change we can't construct instances in
  Mathlib that `grind` can use.

* [#8163](https://github.com/leanprover/lean4/pull/8163) adds some currently failing tests for `grind +ring`, resulting
  in either kernel type mismatches (bugs) or a kernel deep recursion
  (perhaps just a too-large problem).

* [#8167](https://github.com/leanprover/lean4/pull/8167) improves the heuristics used to compute the basis and simplify
  polynomials in the commutative procedure used in `grind`.

* [#8168](https://github.com/leanprover/lean4/pull/8168) fixes a bug when constructing the proof term for a
  Nullstellensatz certificate produced by the new commutative ring
  procedure in `grind`. The kernel was rejecting the proof term.

* [#8170](https://github.com/leanprover/lean4/pull/8170) adds the infrastructure for creating stepwise proof terms in the
  commutative procedure used in `grind`.

* [#8189](https://github.com/leanprover/lean4/pull/8189) implements **stepwise proof terms** in the commutative ring
  procedure used by `grind`. These terms serve as an alternative
  representation to the traditional Nullstellensatz certificates, aiming
  to address the **exponential worst-case complexity** often associated
  with certificate construction.

* [#8231](https://github.com/leanprover/lean4/pull/8231) changes the behaviour of `apply?` so that the `sorry` it uses to
  close the goal is non-synthetic. (Recall that correct use of synthetic
  sorries requires that the tactic also generates an error message, which
  we don't want to do in this situation.) Either this PR or #8230 are
  sufficient to defend against the problem reported in #8212.

* [#8254](https://github.com/leanprover/lean4/pull/8254) fixes unintended inlining of `ToJson`, `FromJson`, and `Repr`
  instances, which was causing exponential compilation times in `deriving`
  clauses for large structures.

## Library

* [#6081](https://github.com/leanprover/lean4/pull/6081) adds an `inheritEnv` field to `IO.Process.SpawnArgs`. If
  `false`, the spawned process does not inherit its parent's environment.

* [#7108](https://github.com/leanprover/lean4/pull/7108) proves `List.head_of_mem_head?` and the analogous
  `List.getLast_of_mem_getLast?`.

* [#7400](https://github.com/leanprover/lean4/pull/7400) adds lemmas for the `filter`, `map` and `filterMap` functions of
  the hash map.

* [#7659](https://github.com/leanprover/lean4/pull/7659) adds SMT-LIB operators to detect overflow
  `BitVec.(umul_overflow, smul_overflow)`, according to the definitions
  [here](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2),
  and the theorems proving equivalence of such definitions with the
  `BitVec` library functions (`umulOverflow_eq`, `smulOverflow_eq`).
  Support theorems for these proofs are `BitVec.toInt_one_of_lt,
  BitVec.toInt_mul_toInt_lt, BitVec.le_toInt_mul_toInt,
  BitVec.toNat_mul_toNat_lt, BitVec.two_pow_le_toInt_mul_toInt_iff,
  BitVec.toInt_mul_toInt_lt_neg_two_pow_iff` and `Int.neg_mul_le_mul,
  Int.bmod_eq_self_of_le_mul_two, Int.mul_le_mul_of_natAbs_le,
  Int.mul_le_mul_of_le_of_le_of_nonneg_of_nonpos, Int.pow_lt_pow`. The PR
  also includes a set of tests.

* [#7671](https://github.com/leanprover/lean4/pull/7671) contains the theorem proving that signed division x.toInt /
  y.toInt only overflows when `x = intMin w` and `y = allOnes w` (for `0 <
  w`).
  To show that this is the *only* case in which overflow happens, we refer
  to overflow for negation
  (`BitVec.sdivOverflow_eq_negOverflow_of_neg_one`): in fact,
  `x.toInt/(allOnes w).toInt = - x.toInt`, i.e., the overflow conditions
  are the same as `negOverflow` for `x`, and then reason about the signs
  of the operands with the respective theorems.
  These BitVec theorems themselves rely on numerous `Int.ediv_*` theorems,
  that carefully set the bounds of signed division for integers.

* [#7761](https://github.com/leanprover/lean4/pull/7761) implements the core theorem for the Bitwuzla rewrites
  [NORM_BV_NOT_OR_SHL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L1495-L1510)
  and
  [BV_ADD_SHL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L395-L401),
  which convert the mixed-boolean-arithmetic expression into a purely
  arithmetic expression:

  ```lean
  theorem add_shiftLeft_eq_or_shiftLeft {x y : BitVec w} :
      x + (y <<< x) =  x ||| (y <<< x)
  ```

* [#7770](https://github.com/leanprover/lean4/pull/7770) adds a shared mutex (or read-write lock) as `Std.SharedMutex`.

* [#7774](https://github.com/leanprover/lean4/pull/7774) adds `Option.pfilter`, a variant of `Option.filter` and several
  lemmas for it and other `Option` functions. These lemmas are split off
  from #7400.

* [#7791](https://github.com/leanprover/lean4/pull/7791) adds lemmas about `Nat.lcm`.

* [#7802](https://github.com/leanprover/lean4/pull/7802) adds `Int.gcd` and `Int.lcm` variants of all `Nat.gcd` and
  `Nat.lcm` lemmas.

* [#7818](https://github.com/leanprover/lean4/pull/7818) deprecates `Option.merge` and `Option.liftOrGet` in favor of
  `Option.zipWith`.

* [#7819](https://github.com/leanprover/lean4/pull/7819) extends `Std.Channel` to provide a full sync and async API, as
  well as unbounded, zero sized and bounded channels.

* [#7835](https://github.com/leanprover/lean4/pull/7835) adds `BitVec.[toInt_append|toFin_append]`.

* [#7847](https://github.com/leanprover/lean4/pull/7847) removes `@[simp]` from all deprecated theorems. `simp` will
  still use such lemmas, without any warning message.

* [#7851](https://github.com/leanprover/lean4/pull/7851) partially reverts #7818, because the function called
  `Option.zipWith` in that PR does not actually correspond to
  `List.zipWith`. We choose `Option.merge` as the name instead.

* [#7855](https://github.com/leanprover/lean4/pull/7855) moves `ReflBEq` to `Init.Core` and changes `LawfulBEq` to extend
  `ReflBEq`.

* [#7856](https://github.com/leanprover/lean4/pull/7856) changes definitions and theorems not to use the membership
  instance on `Option` unless the theorem is specifically about the
  membership instance.

* [#7869](https://github.com/leanprover/lean4/pull/7869) fixes a regression introduced in #7445 where the new
  `Array.emptyWithCapacity` was accidentally not tagged with the correct
  function to actually allocate the capacity.

* [#7871](https://github.com/leanprover/lean4/pull/7871) generalizes the typeclass assumptions on monadic `Option`
  functions.

* [#7879](https://github.com/leanprover/lean4/pull/7879) adds `Int.toNat_emod`, analogous to `Int.toNat_add/mul`.

* [#7880](https://github.com/leanprover/lean4/pull/7880) adds the functions `UIntX.ofInt`, and basic lemmas.

* [#7886](https://github.com/leanprover/lean4/pull/7886) adds `UIntX.pow` and `Pow UIntX Nat` instances, and similarly
  for signed fixed-width integers. These are currently only the naive
  implementation, and will need to be subsequently replaced via
  `@[extern]` with fast implementations (tracked at #7887).

* [#7888](https://github.com/leanprover/lean4/pull/7888) adds `Fin.ofNat'_mul` and `Fin.mul_ofNat'`, parallel to the
  existing lemmas about `add`.

* [#7889](https://github.com/leanprover/lean4/pull/7889) adds `Int.toNat_sub''` a variant of `Int.toNat_sub` taking
  inequality hypotheses, rather than expecting the arguments to be casts
  of natural numbers. This is parallel to the existing `toNat_add` and
  `toNat_mul`.

* [#7890](https://github.com/leanprover/lean4/pull/7890) adds missing lemmas about `Int.bmod`, parallel to lemmas about
  the other `mod` variants.

* [#7891](https://github.com/leanprover/lean4/pull/7891) adds the rfl simp lemma `Int.cast x = x` for `x : Int`.

* [#7893](https://github.com/leanprover/lean4/pull/7893) adds `BitVec.pow` and `Pow (BitVec w) Nat`. The implementation
  is the naive one, and should later be replaced by an `@[extern]`. This
  is tracked at https://github.com/leanprover/lean4/issues/7887.

* [#7897](https://github.com/leanprover/lean4/pull/7897) cleans up the `Option` development, upstreaming some results
  from mathlib in the process.

* [#7899](https://github.com/leanprover/lean4/pull/7899) shuffles some results about integers around to make sure that
  all material that currently exists about `Int.bmod` is located in
  `DivMod/Lemmas.lean` and not downstream of that.

* [#7901](https://github.com/leanprover/lean4/pull/7901) adds `instance [Pure f] : Inhabited (OptionT f α)`, so that
  `Inhabited (OptionT Id Empty)` synthesizes.

* [#7912](https://github.com/leanprover/lean4/pull/7912) adds `List.Perm.take/drop`, and `Array.Perm.extract`,
  restricting permutations to sublist / subarrays when they are constant
  elsewhere.

* [#7913](https://github.com/leanprover/lean4/pull/7913) adds some missing `List/Array/Vector lemmas` about
  `isSome_idxOf?`, `isSome_finIdxOf?`, `isSome_findFinIdx?,
  `isSome_findIdx?` and the corresponding `isNone` versions.

* [#7933](https://github.com/leanprover/lean4/pull/7933) adds lemmas about `Int.bmod` to achieve parity between
  `Int.bmod` and `Int.emod`/`Int.fmod`/`Int.tmod`. Furthermore, it adds
  missing lemmas for `emod`/`fmod`/`tmod` and performs cleanup on names
  and statements for all four operations, also with a view towards
  increasing consistency with the corresponding `Nat.mod` lemmas.

* [#7938](https://github.com/leanprover/lean4/pull/7938) adds lemmas about `List/Array/Vector.countP/count` interacting
  with `replace`. (Specializing to `_self` and `_ne` lemmas doesn't seem
  useful, as there will still be an `if` on the RHS.)

* [#7939](https://github.com/leanprover/lean4/pull/7939) adds `Array.count_erase` and specializations.

* [#7953](https://github.com/leanprover/lean4/pull/7953) generalizes some typeclass hypotheses in the `List.Perm` API
  (away from `DecidableEq`), and reproduces `List.Perm.mem_iff` for
  `Array`, and fixes a mistake in the statement of `Array.Perm.extract`.

* [#7971](https://github.com/leanprover/lean4/pull/7971) upstreams much of the material from `Mathlib/Data/Nat/Init.lean`
  and `Mathlib/Data/Nat/Basic.lean`.

* [#7983](https://github.com/leanprover/lean4/pull/7983) upstreams many of the results from `Mathlib/Data/Int/Init.lean`.

* [#7994](https://github.com/leanprover/lean4/pull/7994) reproduces the `Array.Perm` API for `Vector`. Both are still
  significantly less developed than the API for `List.Perm`.

* [#7999](https://github.com/leanprover/lean4/pull/7999) replaces `Array.Perm` and `Vector.Perm` with one-field
  structures. This avoids dot notation for `List` to work like e.g.
  `h.cons 3` where `h` is an `Array.Perm`.

* [#8000](https://github.com/leanprover/lean4/pull/8000) deprecates some `Int.ofNat_*` lemmas in favor of
  `Int.natCast_*`.

* [#8004](https://github.com/leanprover/lean4/pull/8004) adds extensional hash maps and hash sets under the names
  `Std.ExtDHashMap`, `Std.ExtHashMap` and `Std.ExtHashSet`. Extensional
  hash maps work like regular hash maps, except that they have
  extensionality lemmas which make them easier to use in proofs. This
  however makes it also impossible to regularly iterate over its entries.

* [#8030](https://github.com/leanprover/lean4/pull/8030) adds some missing lemmas about
  `List/Array/Vector.findIdx?/findFinIdx?/findSome?/idxOf?`.

* [#8044](https://github.com/leanprover/lean4/pull/8044) introduces the modules `Std.Data.DTreeMap.Raw`,
  `Std.Data.TreeMap.Raw` and `Std.Data.TreeSet.Raw` and imports them into
  `Std.Data`. All modules related to the raw tree maps are imported into
  these new modules so that they are now a transitive dependency of `Std`.

* [#8067](https://github.com/leanprover/lean4/pull/8067) fixes the behavior of `Substring.isNat` to disallow empty
  strings.

* [#8078](https://github.com/leanprover/lean4/pull/8078) is a follow up to #8055 and implements a `Selector` for async
  TCP in order to allow IO multiplexing using TCP sockets.

* [#8080](https://github.com/leanprover/lean4/pull/8080) fixes `Json.parse` to handle surrogate pairs correctly.

* [#8085](https://github.com/leanprover/lean4/pull/8085) moves the coercion `α → Option α` to the new file
  `Init.Data.Option.Coe`. This file may not be imported anywhere in `Init`
  or `Std`.

* [#8089](https://github.com/leanprover/lean4/pull/8089) adds optimized division functions for `Int` and `Nat` when the
  arguments are known to be divisible (such as when normalizing
  rationals). These are backed by the gmp functions `mpz_divexact` and
  `mpz_divexact_ui`. See also leanprover-community/batteries#1202.

* [#8136](https://github.com/leanprover/lean4/pull/8136) adds an initial set of `@[grind]` annotations for
  `List`/`Array`/`Vector`, enough to set up some regression tests using
  `grind` in proofs about `List`. More annotations to follow.

* [#8139](https://github.com/leanprover/lean4/pull/8139) is a follow up to #8055 and implements a `Selector` for async
  UDP in order to allow IO multiplexing using UDP sockets.

* [#8144](https://github.com/leanprover/lean4/pull/8144) changes the predicate for `Option.guard` to be `p : α → Bool`
  instead of `p : α → Prop`. This brings it in line with other comparable
  functions like `Option.filter`.

* [#8147](https://github.com/leanprover/lean4/pull/8147) adds `List.findRev?` and `List.findSomeRev?`, for parity with
  the existing Array API, and simp lemmas converting these into existing
  operations.

* [#8148](https://github.com/leanprover/lean4/pull/8148) generalises `List.eraseDups` to allow for an arbitrary
  comparison relation. Further, it proves `eraseDups_append : (as ++
  bs).eraseDups = as.eraseDups ++ (bs.removeAll as).eraseDups`.

* [#8150](https://github.com/leanprover/lean4/pull/8150) is a follow up to #8055 and implements a Selector for
  `Std.Channel` in order to allow
   multiplexing using channels.

* [#8154](https://github.com/leanprover/lean4/pull/8154) adds unconditional lemmas for
  `HashMap.getElem?_insertMany_list`, alongside the existing ones that
  have quite strong preconditions. Also for TreeMap (and
  dependent/extensional variants).

* [#8175](https://github.com/leanprover/lean4/pull/8175) adds simp/grind lemmas about `List`/`Array`/`Vector.contains`.
  In the presence of `LawfulBEq` these effectively already held, via
  simplifying `contains` to `mem`, but now these also fire without
  `LawfulBEq`.

* [#8184](https://github.com/leanprover/lean4/pull/8184) adds the `insertMany_append` lemma for all map variants.

## Compiler

* [#6063](https://github.com/leanprover/lean4/pull/6063) updates the version of LLVM and clang used by and shipped with
  Lean to 19.1.2

* [#7824](https://github.com/leanprover/lean4/pull/7824) fixes an issue where uses of 'noncomputable' definitions can get
  incorrectly compiled, while also removing the use of 'noncomputable'
  definitions altogether. Some uses of 'noncomputable' definitions (e.g.
  Classical.propDecidable) do not get compiled correctly by type erasure.
  Running the optimizer on the result can lead to them being optimized
  away, eluding the later IR-level check for uses of noncomputable
  definitions.

* [#7838](https://github.com/leanprover/lean4/pull/7838) adds support for mpz objects (i.e., big nums) to the
  `shareCommon` functions.

* [#7854](https://github.com/leanprover/lean4/pull/7854) introduces fundamental API to distribute module data across
  multiple files in preparation for the module system.

* [#7945](https://github.com/leanprover/lean4/pull/7945) fixes a potential race between `IO.getTaskState` and the task in
  question finishing, resulting in undefined behavior.

* [#7958](https://github.com/leanprover/lean4/pull/7958) ensures that after `main` is finished we still wait on dedicated
  tasks instead of exiting forcefully. If users wish to violently kill
  their dedicated tasks at the end of main instead they can run
  `IO.Process.exit` at the end of `main` instead.

* [#7990](https://github.com/leanprover/lean4/pull/7990) adopts lcAny in more cases of type erasure in the new code
  generator.

* [#7996](https://github.com/leanprover/lean4/pull/7996) disables CSE of local function declarations in the base phase of
  the new compiler. This was introducing sharing between lambdas to bind
  calls w/ `do` notation, which caused them to later no longer be inlined.

* [#8006](https://github.com/leanprover/lean4/pull/8006) changes the inlining heuristics of the new code generator to
  match the old one, which ensures that monadic folds get sufficiently
  inlined for their tail recursion to be exposed to the code generator.

* [#8007](https://github.com/leanprover/lean4/pull/8007) changes eager lambda lifting heuristics in the new compiler to
  match the old compiler, which ensures that inlining/specializing monadic
  code does not accidentally create mutual tail recursion that the code
  generator can't handle.

* [#8008](https://github.com/leanprover/lean4/pull/8008) changes specialization in the new code generator to consider
  callee params to be ground variables, which improves the specialization
  of polymorphic functions.

* [#8009](https://github.com/leanprover/lean4/pull/8009) restricts lifting outside of cases expressions on values of a
  Decidable type, since we can't correctly represent the dependency on the
  erased proposition in the later stages of the compiler.

* [#8010](https://github.com/leanprover/lean4/pull/8010) fixes caseOn expressions with an implemented_by to work
  correctly with hash consing, even when the elaborator produces terms
  that reconstruct the discriminant rather than just reusing a variable.

* [#8015](https://github.com/leanprover/lean4/pull/8015) fixes the IR elim_dead_branches pass to correctly handle join
  points with no params, which currently get considered unreachable. I was
  not able to find an easy repro of this with the old compiler, but it
  occurs when bootstrapping Lean with the new compiler.

* [#8017](https://github.com/leanprover/lean4/pull/8017) makes the IR elim_dead_branches pass correctly handle extern
  functions by considering them as having a top return value. This fix is
  required to bootstrap the Init/ directory with the new compiler.

* [#8023](https://github.com/leanprover/lean4/pull/8023) fixes the IR expand_reset_reuse pass to correctly handle
  duplicate projections from the same base/index. This does not occur (at
  least easily) with the old compiler, but it occurs when bootstrapping
  Lean with the new compiler.

* [#8124](https://github.com/leanprover/lean4/pull/8124) correctly handles escaping functions in the LCNF
  elimDeadBranches pass, by setting all params to top instead of
  potentially leaving them at their default bottom value.

* [#8125](https://github.com/leanprover/lean4/pull/8125) adds support for the `init` attribute to the new compiler.

* [#8127](https://github.com/leanprover/lean4/pull/8127) adds support for borrowed params in the new compiler, which
  requires adding support for .mdata expressions to LCNF type handling.

* [#8132](https://github.com/leanprover/lean4/pull/8132) adds support for lowering `casesOn` for builtin types in the new
  compiler.

* [#8156](https://github.com/leanprover/lean4/pull/8156) fixes a bug where the old compiler's lcnf conversion expr cache
  was not including all of the relevant information in the key, leading to
  terms inadvertently being erased. The `root` variable is used to
  determine whether lambda arguments to applications should get let
  bindings or not, which in turn affects later decisions about type
  erasure (erase_irrelevant assumes that any non-atomic argument is
  irrelevant).

* [#8236](https://github.com/leanprover/lean4/pull/8236) fixes an issue where the combination of `extern_lib` and
  `precompileModules` would lead to "symbol not found" errors.

## Pretty Printing

* [#7805](https://github.com/leanprover/lean4/pull/7805) modifies the pretty printing of raw natural number literals; now
  both `pp.explicit` and `pp.natLit` enable the `nat_lit` prefix. An
  effect of this is that the hover on such a literal in the Infoview has
  the `nat_lit` prefix.

* [#7812](https://github.com/leanprover/lean4/pull/7812) modifies the pretty printing of pi types. Now `∀` will be
  preferred over `→` for propositions if the domain is not a proposition.
  For example, `∀ (n : Nat), True` pretty prints as `∀ (n : Nat), True`
  rather than as `Nat → True`. There is also now an option `pp.foralls`
  (default true) that when false disables using `∀` at all, for
  pedagogical purposes. also adjusts instance implicit binder
  pretty printing — nondependent pi types won't show the instance binder
  name. Closes #1834.

* [#7813](https://github.com/leanprover/lean4/pull/7813) fixes an issue where `let n : Nat := sorry` in the Infoview
  pretty prints as ``n : ℕ := sorry `«Foo:17:17»``. This was caused by
  top-level expressions being pretty printed with the same rules as
  Infoview hovers. Closes #6715. Refactors `Lean.Widget.ppExprTagged`; now
  it takes a delaborator, and downstream users should configure their own
  pretty printer option overrides if necessary if they used the `explicit`
  argument (see `Lean.Widget.makePopup.ppExprForPopup` for an example).
  Breaking change: `ppExprTagged` does not set `pp.proofs` on the root
  expression.

* [#7840](https://github.com/leanprover/lean4/pull/7840) causes structure instance notation to be tagged with the
  constructor when `pp.tagAppFns` is true. This will make docgen will have
  `{` and `}` be links to the structure constructor.

* [#8022](https://github.com/leanprover/lean4/pull/8022) fixes a bug where pretty printing is done in a context with
  cleared local instances. These were cleared since the local context is
  updated during a name sanitization step, but preserving local instances
  is valid since the modification to the local context only affects user
  names.

## Documentation

* [#7947](https://github.com/leanprover/lean4/pull/7947) adds some docstrings to clarify the functions of
  `Lean.mkFreshId`, `Lean.Core.mkFreshUserName`,
  `Lean.Elab.Term.mkFreshBinderName`, and
  `Lean.Meta.mkFreshBinderNameForTactic`.

* [#8018](https://github.com/leanprover/lean4/pull/8018) adjusts the RArray docstring to the new reality from #8014.

## Server

* [#7610](https://github.com/leanprover/lean4/pull/7610) adjusts the `TryThis` widget to also work in widget messages
  rather than only as a panel widget. It also adds additional
  documentation explaining why this change was needed.

* [#7873](https://github.com/leanprover/lean4/pull/7873) fixes a number of bugs related to the handling of the source
  search path in the language server, where deleting files could cause
  several features to stop functioning and both untitled files and files
  that don't exist on disc could have conflicting module names.

* [#7882](https://github.com/leanprover/lean4/pull/7882) fixes a regression where elaboration of a previous document
  version is not cancelled on changes to the document.

* [#8242](https://github.com/leanprover/lean4/pull/8242) fixes the 'goals accomplished' diagnostics. They were
  accidentally broken in #7902.

## Lake

* [#7796](https://github.com/leanprover/lean4/pull/7796) moves Lean's shared library path before the workspace's in
  Lake's augmented environment (e.g., `lake env`).

* [#7809](https://github.com/leanprover/lean4/pull/7809) fixes the order of libraries when loading them via
  `--load-dynlib` or `--plugin` in `lean` and when linking them into a
  shared library or executable. A `Dynlib` now tracks its dependencies and
  they are topologically sorted before being passed to either linking or
  loading.

* [#7822](https://github.com/leanprover/lean4/pull/7822) changes Lake to use normalized absolute paths for its various
  files and directories.

* [#7860](https://github.com/leanprover/lean4/pull/7860) restores the use of builtins (e.g., initializer, elaborators,
  and macros) for DSL features and the use of the Lake plugin in the
  server.

* [#7906](https://github.com/leanprover/lean4/pull/7906) changes Lake build traces to track their mixed inputs. The
  tracked inputs are saved as part of the `.trace` file, which can
  significantly assist in debugging trace issues. In addition, this PR
  tweaks some existing Lake traces. Most significant, module olean traces
  no longer incorporate their module's source trace.

* [#7909](https://github.com/leanprover/lean4/pull/7909) adds Lake support for building modules given their source file
  path. This is made use of in both the CLI and the server.

* [#7963](https://github.com/leanprover/lean4/pull/7963) adds helper functions to convert between `Lake.EStateT` and
  `EStateM`.

* [#7967](https://github.com/leanprover/lean4/pull/7967) adds a `bootstrap` option to Lake which is used to identify the
  core Lean package. This enables Lake to use the current stage's include
  directory rather than the Lean toolchains when compiling Lean with Lean
  in core.

* [#7987](https://github.com/leanprover/lean4/pull/7987) fixes a bug in #7967 that broke external library linking.

* [#8026](https://github.com/leanprover/lean4/pull/8026) fixes bugs in #7809 and #7909 that were not caught partially
  because the `badImport` test had been disabled.

* [#8048](https://github.com/leanprover/lean4/pull/8048) moves the Lake DSL syntax into a dedicated module with minimal
  imports.

* [#8152](https://github.com/leanprover/lean4/pull/8152) fixes a regression where non-precompiled module builds would
  `--load-dynlib` package `extern_lib` targets.

* [#8183](https://github.com/leanprover/lean4/pull/8183) makes Lake tests much more verbose in output. It also fixes some
  bugs that had been missed due to disabled tests. Most significantly, the
  target specifier `@pkg` (e.g., in `lake build`) is now always
  interpreted as a package. It was previously ambiguously interpreted due
  to changes in #7909.

* [#8190](https://github.com/leanprover/lean4/pull/8190) adds documentation for native library options (e.g., `dynlibs`,
  `plugins`, `moreLinkObjs`, `moreLinkLibs`) and `needs` to the Lake
  README. It is also includes information about specifying targets on the
  Lake CLI and in Lean and TOML configuration files.

## Other

* [#7785](https://github.com/leanprover/lean4/pull/7785) adds further automation to the release process, taking care of
  tagging, and creating new `bump/v4.X.0` branches automatically, and
  fixing some bugs.

* [#7789](https://github.com/leanprover/lean4/pull/7789) fixes `lean` potentially changing or interpreting arguments
  after `--run`.

* [#8060](https://github.com/leanprover/lean4/pull/8060) fixes a bug in the Lean kernel. During reduction of `Nat.pow`,
  the kernel did not validate that the WHNF of the first argument is a
  `Nat` literal before interpreting it as an `mpz` number. adds
  the missing check.


````
