/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.23.0 (2025-09-15)" =>
%%%
tag := "release-v4.23.0"
file := "v4.23.0"
%%%

````markdown
For this release, 610 changes landed. In addition to the 95 feature additions and 139 fixes listed below there were 61 refactoring changes, 12 documentation improvements, 71 performance improvements, and 232 other changes.

## Highlights

Lean v4.23.0 release brings significant performance improvements, better error messages,
and a plethora of bug fixes, refinements, and consolidations in `grind`, the compiler, and other components of Lean.

In terms of user experience, noteworthy new features are:

- Improved 'Go to Definition' navigation ([#9040](https://github.com/leanprover/lean4/pull/9040))

  - Using 'Go to Definition' on a type class projection now extracts
    the specific instances that were involved and provides them as locations
    to jump to. For example, using 'Go to Definition' on the `toString` of
    `toString 0` yields results for `ToString.toString` and `ToString Nat`.
  - Using 'Go to Definition' on a macro that produces syntax with type
    class projections now also extracts the specific instances that were
    involved and provides them as locations to jump to. For example, using
    'Go to Definition' on the `+` of `1 + 1` yields results for
    `HAdd.hAdd`, `HAdd α α α` and `Add Nat`.
  - Using 'Go to Declaration' now provides all the results of 'Go to
    Definition' in addition to the elaborator and the parser that were
    involved. For example, using 'Go to Declaration' on the `+` of `1 + 1`
    yields results for `HAdd.hAdd`, `HAdd α α α`, `Add Nat`,
    `` macro_rules | `($x + $y) => ... `` and `infixl:65 " + " => HAdd.hAdd`.
  - Using 'Go to Type Definition' on a value with a type that contains
    multiple constants now provides 'Go to Definition' results for each
    constant. For example, using 'Go to Type Definition' on `x` for `x : Array Nat`
    yields results for `Array` and `Nat`.

- Interactive code-action hints for errors:

  - for "invalid named argument" error, suggest valid argument names ([#9315](https://github.com/leanprover/lean4/pull/9315))

  - for "invalid case name" error, suggest valid case names ([#9316](https://github.com/leanprover/lean4/pull/9316))

  - for "fields missing" error in structure instances, suggest to insert all the missing fields ([#9317](https://github.com/leanprover/lean4/pull/9317))

  You can try all of these in the [Lean playground](https://live.lean-lang.org/#codez=PQWghAUAxABAEgSwHYBcDOMBmB7ATjZANwEMAbBAExiWIFsBTK43AcwFcHUNkYAHYlCnq4kaCCGAQIyCmwDGKBIXowAKjADuAC2H0IMGAB8YtANYBGGAAoAHjACeMAF4wAXDABC2bKQCUU+hs6XlIVKxQ3NV83AF59EwE5LRgIjQQULXjjADozSytHVxiU3DZ6aKsNWJKyipcirDI0cpgYgD5rfylQSFhELiw8GDliZuo6ejEJAKDaELCAI0ivH2j3ADkBaoX7eJHmjAW90ZUkbCRAhDQhVFa2+IM0UwRebvBoeGR0QfxaK7RkCwYNdSgo2LgVMhrsQkHIVJgEPRSBQppIICD5ChwSoAMqaHQQ+IIpEUSwbARExHIgBMkQAavQFENNhFicjzDNgqFIniivEAN4AXwgQA).

### Breaking Changes

- [#9800](https://github.com/leanprover/lean4/pull/9800) improves the delta deriving handler, giving it the ability to
  process definitions with binders, as well as the ability to recursively
  unfold definitions. **Breaking change**: the
  derived instance's name uses the `instance` command's name generator,
  and the new instance is added to the current namespace.

- [#9040](https://github.com/leanprover/lean4/pull/9040) improves the 'Go to Definition' UX.
  **Breaking change**: `InfoTree.hoverableInfoAt?` has been generalized to
  `InfoTree.hoverableInfoAtM?` and now takes a general `filter` argument
  instead of several boolean flags, as was the case before.

- [#9594](https://github.com/leanprover/lean4/pull/9594) optimizes `Lean.Name.toString`, giving a 10% instruction
  benefit.

  Crucially this is a **breaking change** as the old `Lean.Name.toString`
  method used to support a method for identifying tokens. This method is
  now available as `Lean.Name.toStringWithToken` in order to allow for
  specialization of the (highly common) `toString` code path which sets
  this function to just return `false`.

- [#9729](https://github.com/leanprover/lean4/pull/9729) introduces a canonical way to endow a type with an order
  structure. **Breaking changes:**

  - The requirements of the `lt_of_le_of_lt`/`le_trans` lemmas for
    `Vector`, `List` and `Array` are simplified. They now require an
    `IsLinearOrder` instance. The new requirements are logically equivalent
    to the old ones, but the `IsLinearOrder` instance is not automatically
    inferred from the smaller type classes.
  - Hypotheses of type `Std.Total (¬ · < · : α → α → Prop)` are replaced
    with the equivalent class `Std.Asymm (· < · : α → α → Prop)`. Breakage
    should be limited because there is now an instance that derives the
    latter from the former.
  - In `Init.Data.List.MinMax`, multiple theorem signatures are modified,
    replacing explicit parameters for antisymmetry, totality, `min_ex_or`
    etc. with corresponding instance parameters.

## Language

* [#6732](https://github.com/leanprover/lean4/pull/6732) adds support for the `clear` tactic in conversion mode.

* [#8666](https://github.com/leanprover/lean4/pull/8666) adjusts the experimental module system to not import the IR of
  non-`meta` declarations. It does this by replacing such IR with opaque
  foreign declarations on export and adjusting the new compiler
  accordingly.

* [#8842](https://github.com/leanprover/lean4/pull/8842) fixes the bug that `collectAxioms` didn't collect axioms
  referenced by other axioms. One of the results of this bug is that
  axioms collected from a theorem proved by `native_decide` may not
  include `Lean.trustCompiler`.

* [#9015](https://github.com/leanprover/lean4/pull/9015) makes `isDefEq` detect more stuck definitional equalities
  involving smart unfoldings. Specifically, if `t =?= defn ?m` and `defn`
  matches on its argument, then this equality is stuck on `?m`. Prior to
  this change, we would not see this dependency and simply return `false`.

* [#9084](https://github.com/leanprover/lean4/pull/9084) adds `binrel%` macros for `!=` and `≠` notation defined in
  `Init.Core`. This allows the elaborator to insert coercions on both
  sides of the relation, instead of committing to the type on the left
  hand side.

* [#9090](https://github.com/leanprover/lean4/pull/9090) fixes a bug in `whnfCore` where it would fail to reduce
  applications of recursors/auxiliary defs.

* [#9097](https://github.com/leanprover/lean4/pull/9097) ensures that `mspec` uses the configured transparency setting
  and makes `mvcgen` use default transparency when calling `mspec`.

* [#9099](https://github.com/leanprover/lean4/pull/9099) improves the “expected type mismatch” error message by omitting
  the type's types when they are defeq, and putting them into separate
  lines when not.

* [#9103](https://github.com/leanprover/lean4/pull/9103) prevents truncation of `panic!` messages containing null bytes.

* [#9108](https://github.com/leanprover/lean4/pull/9108) fixes an issue that may have caused inline expressions in
  messages to be unnecessarily rendered on a separate line.

* [#9113](https://github.com/leanprover/lean4/pull/9113) improves the `grind` doc string and tries to make it more
  approachable to new user.

* [#9130](https://github.com/leanprover/lean4/pull/9130) fixes unexpected occurrences of the `Grind.offset` gadget in
  ground patterns. See new test

* [#9131](https://github.com/leanprover/lean4/pull/9131) adds a `usedLetOnly` parameter to `LocalContext.mkLambda` and
  `LocalContext.mkForall`, to parallel the `MetavarContext` versions.

* [#9133](https://github.com/leanprover/lean4/pull/9133) adds support for `a^(m+n)` in the `grind` normalizer.

* [#9143](https://github.com/leanprover/lean4/pull/9143) removes a rather ugly hack in the module system, exposing the
  bodies of theorems whose type mention `WellFounded`.

* [#9146](https://github.com/leanprover/lean4/pull/9146) adds "safe" polynomial operations to `grind ring`. The use the
  usual combinators: `withIncRecDepth` and `checkSystem`.

* [#9149](https://github.com/leanprover/lean4/pull/9149) generalizes the `a^(m+n)` grind normalizer to any semirings.
  Example:
  ```
  variable [Field R]

* [#9150](https://github.com/leanprover/lean4/pull/9150) adds a missing case in the `toPoly` function used in `grind`.

* [#9153](https://github.com/leanprover/lean4/pull/9153) improves the linarith `markVars`, and ensures it does not
  produce spurious issue messages.

* [#9168](https://github.com/leanprover/lean4/pull/9168) resolves a defeq diamond, which caused a problem in Mathlib:
  ```
  import Mathlib

* [#9172](https://github.com/leanprover/lean4/pull/9172) fixes a bug at `matchEqBwdPat`. The type may contain pattern
  variables.

* [#9173](https://github.com/leanprover/lean4/pull/9173) fixes an incompatibility in the experimental module system when
  trying to combine wellfounded recursion with public exposed definitions.

* [#9176](https://github.com/leanprover/lean4/pull/9176) makes `mvcgen` split ifs rather than applying specifications.
  Doing so fixes a bug reported by Rish.

* [#9182](https://github.com/leanprover/lean4/pull/9182) tries to improve the E-matching pattern inference for `grind`.
  That said, we still need better tools for annotating and maintaining
  `grind` annotations in libraries.

* [#9184](https://github.com/leanprover/lean4/pull/9184) fixes stealing of `⇓` syntax by the new notation for total
  postconditions by demoting it to non-builtin syntax and scoping it to
  `Std.Do`.

* [#9191](https://github.com/leanprover/lean4/pull/9191) lets the equation compiler unfold abstracted proofs again if
  they would otherwise hide recursive calls.

  This fixes #8939.

* [#9193](https://github.com/leanprover/lean4/pull/9193) fixes the unexpected kernel projection issue reported by issue
  #9187

* [#9194](https://github.com/leanprover/lean4/pull/9194) makes the logic and tactics of `Std.Do` universe polymorphic, at
  the cost of a few definitional properties arising from the switch from
  `Prop` to `ULift Prop` in the base case `SPred []`.

* [#9196](https://github.com/leanprover/lean4/pull/9196) implements `forall` normalization using a simproc instead of
  rewriting rules in `grind`. This is the first part of the PR; after
  updating stage0, we must remove the normalization theorems.

* [#9200](https://github.com/leanprover/lean4/pull/9200) implements `exists` normalization using a simproc instead of
  rewriting rules in `grind`. This is the first part of the PR; after
  updating stage0, we must remove the normalization theorems.

* [#9202](https://github.com/leanprover/lean4/pull/9202) extends the `Eq` simproc used in `grind`. It covers more cases
  now. It also adds 3 reducible declarations to the list of declarations
  to unfold.

* [#9214](https://github.com/leanprover/lean4/pull/9214) implements support for local and scoped `grind_pattern`
  commands.

* [#9225](https://github.com/leanprover/lean4/pull/9225) improves the `congr` tactic so that it can handle function
  applications with fewer arguments than the arity of the head function.
  This also fixes a bug where `congr` could not make progress with
  `Set`-valued functions in Mathlib, since `Set` was being unfolded and
  making such functions have an apparently higher arity.

* [#9228](https://github.com/leanprover/lean4/pull/9228) improves the startup time for `grind ring` by generating the
  required type classes on demand. This optimization is particularly
  relevant for files that make hundreds of calls to `grind`, such as
  `tests/lean/run/grind_bitvec2.lean`. For example, before this change,
  `grind` spent 6.87 seconds synthesizing type classes, compared to 3.92
  seconds after this PR.

* [#9241](https://github.com/leanprover/lean4/pull/9241) ensures that the type class instances used to implement the
  `ToInt` adapter (in `grind cutsat`) are generated on demand.

* [#9244](https://github.com/leanprover/lean4/pull/9244) improves the instance generation in the `grind linarith` module.

* [#9251](https://github.com/leanprover/lean4/pull/9251) demotes the builtin elaborators for `Std.Do.PostCond.total` and
  `Std.Do.Triple` into macros, following the DefEq improvements of #9015.

* [#9267](https://github.com/leanprover/lean4/pull/9267) optimizes support for `Decidable` instances in `grind`. Because
  `Decidable` is a subsingleton, the canonicalizer no longer wastes time
  normalizing such instances, a significant performance bottleneck in
  benchmarks like `grind_bitvec2.lean`. In addition, the
  congruence-closure module now handles `Decidable` instances, and can
  solve examples such as:
  ```lean
  example (p q : Prop) (h₁ : Decidable p) (h₂ : Decidable (p ∧ q)) : (p ↔ q) → h₁ ≍ h₂ := by
    grind
  ```

* [#9271](https://github.com/leanprover/lean4/pull/9271) improves the performance of the formula normalizer used in
  `grind`.

* [#9287](https://github.com/leanprover/lean4/pull/9287) rewords the "application type mismatch" error message so that
  the argument and its type precede the application expression.

* [#9293](https://github.com/leanprover/lean4/pull/9293) replaces the `reduceCtorEq` simproc used in `grind` by a much
  more efficient one. The default one use in `simp` is just overhead
  because the `grind` normalizer is already normalizing arithmetic.
  In a separate PR, we will push performance improvements to the default
  `reduceCtorEq`.

* [#9305](https://github.com/leanprover/lean4/pull/9305) uses the `mkCongrSimpForConst?` API in `simp` to reduce the
  number of times the same congruence lemma is generated. Before this PR,
  `grind` would spend `1.5`s creating congruence theorems during
  normalization in the `grind_bitvec2.lean` benchmark. It now spends
  `0.6`s. should make an even bigger difference after we merge
  #9300.

* [#9315](https://github.com/leanprover/lean4/pull/9315) adds improves the "invalid named argument" error message in
  function applications and match patterns by providing clickable hints
  with valid argument names. In so doing, it also fixes an issue where
  this error message would erroneously flag valid match-pattern argument
  names.

* [#9316](https://github.com/leanprover/lean4/pull/9316) adds clickable code-action hints to the "invalid case name"
  error message.

* [#9317](https://github.com/leanprover/lean4/pull/9317) adds to the "fields missing" error message for structure
  instance notation a code-action hint that inserts all missing fields.

* [#9324](https://github.com/leanprover/lean4/pull/9324) improves the functions for checking whether two terms are
  disequal in `grind`

* [#9325](https://github.com/leanprover/lean4/pull/9325) optimizes the Boolean disequality propagator used in `grind`.

* [#9326](https://github.com/leanprover/lean4/pull/9326) optimizes `propagateEqUp` used in `grind`.

* [#9340](https://github.com/leanprover/lean4/pull/9340) modifies the encoding from `Nat` to `Int` used in `grind
  cutsat`. It is simpler, more extensible, and similar to the generic
  `ToInt`. After update stage0, we will be able to delete the leftovers.

* [#9351](https://github.com/leanprover/lean4/pull/9351) optimizes the `grind` preprocessing steps by skipping steps when
  the term is already present in the hash-consing table.

* [#9358](https://github.com/leanprover/lean4/pull/9358) adds support for generating lattice-theoretic (co)induction
  proof principles for predicates defined via `mutual` blocks using
  `inductive_fixpoint`/`coinductive_fixpoint` constructs.

* [#9367](https://github.com/leanprover/lean4/pull/9367) implements a minor optimization to the `grind` preprocessor.

* [#9369](https://github.com/leanprover/lean4/pull/9369) optimizes the `grind` preprocessor by skipping unnecessary steps
  when possible.

* [#9371](https://github.com/leanprover/lean4/pull/9371) fixes an issue that caused some `deriving` handlers to fail when
  the name of the type being declared matched that of a declaration in an
  open namespace.

* [#9372](https://github.com/leanprover/lean4/pull/9372) fixes a performance issue that occurs when generating equation
  lemmas for functions that use match-expressions containing several
  literals. This issue was exposed by #9322 and arises from a combination
  of factors:

  1. Literal values are compiled into a chain of dependent if-then-else
  expressions.
  2. Dependent if-then-else expressions are significantly more expensive
  to simplify than regular ones.
  3. The `split` tactic selects a target, splits it, and then invokes
  `simp` on the resulting subgoals. Moreover, `simp` traverses the entire
  goal bottom-up and does not stop after reaching the target.

* [#9385](https://github.com/leanprover/lean4/pull/9385) replaces the `isDefEq` test in the `simpEq` simproc used in
  `grind`. It is too expensive.

* [#9386](https://github.com/leanprover/lean4/pull/9386) improves a confusing error message that occurred when attempting
  to project from a zero-field structure.

* [#9387](https://github.com/leanprover/lean4/pull/9387) adds a hint to the "invalid projection" message suggesting the
  correct nested projection for expressions of the form `t.n` where `t` is
  a tuple and `n > 2`.

* [#9395](https://github.com/leanprover/lean4/pull/9395) fixes a bug at `mkCongrSimpCore?`. It fixes the issue reported
  by @joehendrix at #9388.
  The fix is just commit: afc4ba617fe2ca5828e0e252558d893d7791d56b. The
  rest of the PR is just cleaning up the file.

* [#9398](https://github.com/leanprover/lean4/pull/9398) avoids the expensive `inferType` call in `simpArith`. It also
  cleans up some of the code and removes anti-patterns.

* [#9408](https://github.com/leanprover/lean4/pull/9408) implements a simple optimization: dependent implications are no
  longer treated as E-matching theorems in `grind`. In
  `grind_bitvec2.lean`, this change saves around 3 seconds, as many
  dependent implications are generated. Example:
  ```lean
   ∀ (h : i + 1 ≤ w), x.abs.getLsbD i = x.abs[i]
   ```

* [#9414](https://github.com/leanprover/lean4/pull/9414) increases the number of cases where `isArrowProposition` returns
  a result other than `.undef`. This function is used to implement the
  `isProof` predicate, which is invoked on every subterm visited by
  `simp`.

* [#9421](https://github.com/leanprover/lean4/pull/9421) fixes a bug that caused error explanations to "steal" the
  Infoview's container in the Lean web editor.

* [#9423](https://github.com/leanprover/lean4/pull/9423) updates the formatting of, and adds explanations for, "unknown
  identifier" errors as well as "failed to infer type" errors for binders
  and definitions.

* [#9424](https://github.com/leanprover/lean4/pull/9424) improves the error messages produced by the `split` tactic,
  including suggesting syntax fixes and related tactics with which it
  might be confused.

* [#9443](https://github.com/leanprover/lean4/pull/9443) makes cdot function expansion take hygiene information into
  account, fixing "parenthesis capturing" errors that can make erroneous
  cdots trigger cdot expansion in conjunction with macros. For example,
  given
  ```lean
  macro "baz% " t:term : term => `(1 + ($t))
  ```
  it used to be that `baz% ·` would expand to `1 + fun x => x`, but now
  the parentheses in `($t)` do not capture the cdot. We also fix an
  oversight where cdot function expansion ignored the fact that type
  ascriptions and tuples were supposed to delimit expansion, and also now
  the quotation prechecker ignores the identifier in `hygieneInfo`. (#9491
  added the hygiene information to the parenthesis and cdot syntaxes.)

* [#9447](https://github.com/leanprover/lean4/pull/9447) ensures that `mvcgen` not only tries to close stateful subgoals
  by assumption, but also pure Lean goals.

* [#9448](https://github.com/leanprover/lean4/pull/9448) addresses the lean crash (stack overflow) with nested induction
  and the generation of the `SizeOf` spec lemmas, reported at #9018.

* [#9451](https://github.com/leanprover/lean4/pull/9451) adds support in the `mintro` tactic for introducing `let`/`have`
  binders in stateful targets, akin to `intro`. This is useful when
  specifications introduce such let bindings.

* [#9454](https://github.com/leanprover/lean4/pull/9454) introduces tactic `mleave` that leaves the `SPred` proof mode by
  eta expanding through its abstractions and applying some mild
  simplifications. This is useful to apply automation such as `grind`
  afterwards.

* [#9464](https://github.com/leanprover/lean4/pull/9464) makes `PProdN.reduceProjs` also look for projection functions.
  Previously, all redexes were created by the functions in `PProdN`, which
  used primitive projections. But with `mkAdmProj` the projection
  functions creep in via the types of the `admissible_pprod_fst` theorem.
  So let's just reduce both of them.

* [#9472](https://github.com/leanprover/lean4/pull/9472) fixes another issue at the `congr_simp` theorems that was
  affecting Mathlib. Many thanks to Johan Commelin for creating the mwe.

* [#9476](https://github.com/leanprover/lean4/pull/9476) fixes the bridge between `Nat` and `Int` in `grind cutsat`.

* [#9479](https://github.com/leanprover/lean4/pull/9479) improves the `evalInt?` function, which is used to evaluate
  configuration parameters from the `ToInt` type class. also adds
  a new `evalNat?` function for handling the `IsCharP` type class, and
  introduces a configuration option:
  ```
  grind (exp := <num>)
  ```
  This option controls the maximum exponent size considered during
  expression evaluation. Previously, `evalInt?` used `whnf`, which could
  run out of stack space when reducing terms such as `2^1024`.

* [#9480](https://github.com/leanprover/lean4/pull/9480) adds a feature where `structure` constructors can override the
  inferred binder kinds of the type's parameters. In the following, the
  `(p)` binder on `toLp` causes `p` to be an explicit parameter to
  `WithLp.toLp`:
  ```lean
  structure WithLp (p : Nat) (V : Type) where toLp (p) ::
    ofLp : V
  ```
  This reflects the syntax of the feature added in #7742 for overriding
  binder kinds of structure projections. Similarly, only those parameters
  in the header of the `structure` may be updated; it is an error to try
  to update binder kinds of parameters included via `variable`.

* [#9481](https://github.com/leanprover/lean4/pull/9481) fixes a kernel type mismatch that occurs when using `grind` on
  goals containing non-standard `OfNat.ofNat` terms. For example, in issue
  #9477, the `0` in the theorem `range_lower` has the form:
  ```lean
  (@OfNat.ofNat
    (Std.PRange.Bound (Std.PRange.RangeShape.lower (Std.PRange.RangeShape.mk Std.PRange.BoundShape.closed Std.PRange.BoundShape.open)) Nat)
    (nat_lit 0)
    (instOfNatNat (nat_lit 0)))
  ```
  instead of the more standard form:
  ```lean
  (@OfNat.ofNat
    Nat
    (nat_lit 0)
    (instOfNatNat (nat_lit 0)))
  ```

* [#9487](https://github.com/leanprover/lean4/pull/9487) fixes an incorrect proof term constructed by `grind linarith`,
  as reported in #9485.

* [#9491](https://github.com/leanprover/lean4/pull/9491) adds hygiene info to paren/tuple/typeAscription syntaxes, which
  will be used to implement hygienic cdot function expansion in #9443.

* [#9496](https://github.com/leanprover/lean4/pull/9496) improves the error messages produced by the `set_option`
  command.

* [#9500](https://github.com/leanprover/lean4/pull/9500) adds a `HPow \a Int \a` field to `Lean.Grind.Field`, and
  sufficient axioms to connect it to the operations, so that in future we
  can reason about exponents in `grind`. To avoid collisions, we also move
  the `HPow \a Nat \a` field in `Semiring` from the extends clause to a
  field. Finally, we add some failing tests about normalizing exponents.

* [#9505](https://github.com/leanprover/lean4/pull/9505) removes vestigial syntax definitions in
  `Lean.Elab.Tactic.Do.VCGen` that when imported undefine the `mvcgen`
  tactic. Now it should be possible to import Mathlib and still use
  `mvcgen`.

* [#9506](https://github.com/leanprover/lean4/pull/9506) adds a few missing simp lemmas to `mleave`.

* [#9507](https://github.com/leanprover/lean4/pull/9507) makes `mvcgen` `mintro` let/have bindings.

* [#9509](https://github.com/leanprover/lean4/pull/9509) surfaces kernel diagnostics even in `example`.

* [#9512](https://github.com/leanprover/lean4/pull/9512) makes `mframe`, `mspec` and `mvcgen` respect hygiene.
  Inaccessible stateful hypotheses can now be named with a new tactic
  `mrename_i` that works analogously to `rename_i`.

* [#9516](https://github.com/leanprover/lean4/pull/9516) ensures that private declarations made inaccessible by the
  module system are noted in the relevant error messages

* [#9518](https://github.com/leanprover/lean4/pull/9518) ensures previous "is marked as private" messages are still
  triggered under the module system

* [#9520](https://github.com/leanprover/lean4/pull/9520) corrects the changes to `Lean.Grind.Field` made in #9500.

* [#9522](https://github.com/leanprover/lean4/pull/9522) uses `withAbstractAtoms` to prevent the kernel from accidentally
  reducing the atoms in the arith normlizer while typechecking. This PR
  also sets `implicitDefEqProofs := false` in the `grind` normalizer

* [#9532](https://github.com/leanprover/lean4/pull/9532) generalizes `Process.output` and `Process.run` with an optional
  `String` argument that can be piped to `stdin`.

* [#9551](https://github.com/leanprover/lean4/pull/9551) fixes the error position for the "dependent elimination failed"
  error for the `cases` tactic.

* [#9553](https://github.com/leanprover/lean4/pull/9553) fixes a bug introduced in #7830 where if the cursor is at the
  indicated position
  ```lean
  example (as bs : List Nat) : (as.append bs).length = as.length + bs.length := by
    induction as with
    | nil => -- cursor
    | cons b bs ih =>
  ```
  then the Infoview would show "no goals" rather than the `nil` goal. The
  PR also fixes a separate bug where placing the cursor on the next line
  after the `induction`/`cases` tactics like in
  ```lean
    induction as with
    | nil => sorry
    | cons b bs ih => sorry
    I -- < cursor
  ```
  would report the original goal in the goal list. Furthermore, there are
  numerous improvements to error recovery (including `allGoals`-type logic
  for pre-tactics) and the visible tactic states when there are errors.
  Adds `Tactic.throwOrLogErrorAt`/`Tactic.throwOrLogError` for throwing or
  logging errors depending on the recovery state.

* [#9571](https://github.com/leanprover/lean4/pull/9571) restores the feature where in `induction`/`cases` for `Nat`, the
  `zero` and `succ` labels are hoverable. This was added in #1660, but
  broken in #3629 and #3655 when custom eliminators were added. In
  general, if a custom eliminator `T.elim` for an inductive type `T` has
  an alternative `foo`, and `T.foo` is a constant, then the `foo` label
  will have `T.foo` hover information.

* [#9574](https://github.com/leanprover/lean4/pull/9574) adds the option `abstractProof` to control whether `grind`
  automatically creates an auxiliary theorem for the generated proof or
  not.

* [#9575](https://github.com/leanprover/lean4/pull/9575) optimizes the proof terms generated by `grind ring`. For
  example, before this PR, the kernel took 2.22 seconds (on a M4 Max) to
  type-check the proof in the benchmark `grind_ring_5.lean`; it now takes
  only 0.63 seconds.

* [#9578](https://github.com/leanprover/lean4/pull/9578) fixes an issue in `grind`'s disequality proof construction. The
  issue occurs when an equality is merged with the `False` equivalence
  class, but it is not the root of its congruence class, and its
  congruence root has not yet been merged into the `False` equivalence
  class yet.

* [#9579](https://github.com/leanprover/lean4/pull/9579) ensures `ite` and `dite` are to selected as E-matching patterns.
  They are bad patterns because the then/else branches are only
  internalized after `grind` decided whether the condition is
  `True`/`False`.

* [#9592](https://github.com/leanprover/lean4/pull/9592) updates the styling and wording of error messages produced in
  inductive type declarations and anonymous constructor notation,
  including hints for inferable constructor visibility updates.

* [#9595](https://github.com/leanprover/lean4/pull/9595) improves the error message displayed when writing an invalid
  projection on a free variable of function type.

* [#9606](https://github.com/leanprover/lean4/pull/9606) adds notes to the deprecation warning when the replacement
  constant has a different type, visibility, and/or namespace.

* [#9625](https://github.com/leanprover/lean4/pull/9625) improves trace messages around wf_preprocess.

* [#9628](https://github.com/leanprover/lean4/pull/9628) introduces a `mutual_induct` variant of the generated
  (co)induction proof principle for mutually defined (co)inductive
  predicates. Unlike the standard (co)induction principle (which projects
  conclusions separately for each predicate), `mutual_induct` produces a
  conjunction of all conclusions.

* [#9633](https://github.com/leanprover/lean4/pull/9633) updates various error messages produced by or associated with
  built-in tactics and adapts their formatting to current conventions.

* [#9634](https://github.com/leanprover/lean4/pull/9634) modifies dot identifier notation so that `(.a : T)` resolves
  `T.a` with respect to the root namespace, like for generalized field
  notation. This lets the notation refer to private names, follow aliases,
  and also use open namespaces. The LSP completions are improved to follow
  how dot ident notation is resolved, but it doesn't yet take into account
  aliases or open namespaces.

* [#9637](https://github.com/leanprover/lean4/pull/9637) improves the readability of the "maximum universe level offset
  exceeded" error message.

* [#9646](https://github.com/leanprover/lean4/pull/9646) uses a more simple approach to proving the unfolding theorem for
  a function defined by well-founded recursion. Instead of looping a bunch
  of tactics, it uses simp in single-pass mode to (try to) exactly undo
  the changes done in `WF.Fix`, using a dedicated theorem that pushes the
  extra argument in for each matcher (or `casesOn`).

* [#9649](https://github.com/leanprover/lean4/pull/9649) fixes an issue where a macro unfolding to multiple commands
  would not be accepted inside `mutual`

* [#9653](https://github.com/leanprover/lean4/pull/9653) adds error explanations for two common errors caused by large
  elimination from `Prop`. To support this functionality, "nested" named
  errors thrown by sub-tactics are now able to display their error code
  and explanation.

* [#9666](https://github.com/leanprover/lean4/pull/9666) addresses an outstanding feature in the module system to
  automatically mark `let rec` and `where` helper declarations as private
  unless they are defined in a public context such as under `@[expose]`.

* [#9670](https://github.com/leanprover/lean4/pull/9670) add constructors `.intCast k` and `.natCast k` to
  `CommRing.Expr`. We need them because terms such as `Nat.cast (R := α)
  1` and `(1 : α)` are not definitionally equal. This is pervaise in
  Mathlib for the numerals `0` and `1`.

* [#9671](https://github.com/leanprover/lean4/pull/9671) fixes support for `SMul.smul` in `grind ring`. `SMul.smul`
  applications are now normalized. Example:
  ```lean
  example (x : BitVec 2) : x - 2 • x + x = 0 := by
    grind
  ```

* [#9675](https://github.com/leanprover/lean4/pull/9675) adds support for `Fin.val` in `grind cutsat`. Examples:
  ```lean
  example (a b : Fin 2) (n : Nat) : n = 1 → ↑(a + b) ≠ n → a ≠ 0 → b = 0 → False := by
    grind

* [#9676](https://github.com/leanprover/lean4/pull/9676) adds normalizers for nonstandard arithmetic instances. The types
  `Nat` and `Int` have built-in support in `grind`, which uses the
  standard instances for these types and assumes they are the ones in use.
  However, users may define their own alternative instances that are
  definitionally equal to the standard ones. normalizes such
  instances using simprocs. This situation actually occurs in Mathlib.
  Example:

  ```lean
  class Distrib (R : Type _) extends Mul R where

* [#9679](https://github.com/leanprover/lean4/pull/9679) produces a warning for redundant `grind` arguments.

* [#9682](https://github.com/leanprover/lean4/pull/9682) fixes a regression introduced by an optimization in the
  `unfoldReducible` step used by the `grind` normalizer. It also ensures
  that projection functions are not reduced, as they are folded in a later
  step.

* [#9686](https://github.com/leanprover/lean4/pull/9686) applies `clear` to implementation detail local declarations
  during the `grind` preprocessing steps.

* [#9699](https://github.com/leanprover/lean4/pull/9699) adds propagation rules for functions that take singleton types.
  This feature is useful for discharging verification conditions produced
  by `mvcgen`. For example:

  ```lean
  example (h : (fun (_ : Unit) => x + 1) = (fun _ => 1 + y)) : x = y := by
    grind
  ```

* [#9700](https://github.com/leanprover/lean4/pull/9700) fixes assertion violations when `checkInvariants` is enabled in
  `grind`

* [#9701](https://github.com/leanprover/lean4/pull/9701) switches to a non-verloading local `Std.Do.Triple` notation in
  SpecLemmas.lean to work around a stage2 build failure.

* [#9702](https://github.com/leanprover/lean4/pull/9702) fixes an issue in the `match` elaborator where pattern variables
  like `__x` would not have the kind `implDetail` in the local context.
  Now `kindOfBinderName` is `LocalDeclKind.ofBinderName`.

* [#9704](https://github.com/leanprover/lean4/pull/9704) optimizes the proof terms produced by `grind cutsat`. Additional
  performance improvements will be merged later.

* [#9706](https://github.com/leanprover/lean4/pull/9706) combines `Poly.combine_k` and `Poly.mul_k` steps used in the
  `grind cutsat` proof terms.

* [#9710](https://github.com/leanprover/lean4/pull/9710) improves some of the proof terms produced by `grind ring` and
  `grind cutsat`.

* [#9714](https://github.com/leanprover/lean4/pull/9714) adds a version of `CommRing.Expr.toPoly` optimized for kernel
  reduction. We use this function not only to implement `grind ring`, but
  also to interface the ring module with `grind cutsat`.

* [#9716](https://github.com/leanprover/lean4/pull/9716) moves the validation of cross-package `import all` to Lake and
  the syntax validation of import keywords (`public`, `meta`, and `all`)
  to the two import parsers.

* [#9728](https://github.com/leanprover/lean4/pull/9728) fixes #9724

* [#9735](https://github.com/leanprover/lean4/pull/9735) extends the propagation rule implemented in #9699 to constant
  functions.

* [#9736](https://github.com/leanprover/lean4/pull/9736) implements the option `mvcgen +jp` to employ a slightly lossy VC
  encoding for join points that prevents exponential VC blowup incurred by
  naïve splitting on control flow.

* [#9754](https://github.com/leanprover/lean4/pull/9754) makes `mleave` apply `at *` and improves its simp set in order to
  discharge some more trivialities (#9581).

* [#9755](https://github.com/leanprover/lean4/pull/9755) implements a `mrevert ∀n` tactic that "eta-reduces" the stateful
  goal and is adjoint to `mintro ∀x1 ... ∀xn`.

* [#9767](https://github.com/leanprover/lean4/pull/9767) fixes equality congruence proof terms constructed by `grind`.

* [#9772](https://github.com/leanprover/lean4/pull/9772) fixes a bug in the projection over constructor propagator used
  in `grind`. It may construct type-incorrect terms when an equivalence
  class contains heterogeneous equalities.

* [#9776](https://github.com/leanprover/lean4/pull/9776) combines the simplification and unfold-reducible-constants steps
  in `grind` to ensure that no potential normalization steps are missed.

* [#9780](https://github.com/leanprover/lean4/pull/9780) extends the test suite for `grind` working category theory, to
  help debug outstanding problems in Mathlib.

* [#9781](https://github.com/leanprover/lean4/pull/9781) ensures that `mvcgen` is hygienic. The goals it generates should
  now introduce all locals inaccessibly.

* [#9785](https://github.com/leanprover/lean4/pull/9785) splits out an implementation detail of
  MVarId.getMVarDependencies into a top-level function. Aesop was relying
  on the function defined in the where clause, which is no longer possible
  after #9759.

* [#9798](https://github.com/leanprover/lean4/pull/9798) introduces `Lean.realizeValue`, a new metaprogramming API for
  parallelism-aware caching of `MetaM` computations

* [#9800](https://github.com/leanprover/lean4/pull/9800) improves the delta deriving handler, giving it the ability to
  process definitions with binders, as well as the ability to recursively
  unfold definitions. Furthermore, delta deriving now tries all explicit
  non-out-param arguments to a class, and it can handle "mixin" instance
  arguments. The `deriving` syntax has been changed to accept general
  terms, which makes it possible to derive specific instances with for
  example `deriving OfNat _ 1` or `deriving Module R`. The class is
  allowed to be a pi type, to add additional hypotheses; here is a Mathlib
  example:
  ```lean
  def Sym (α : Type*) (n : ℕ) :=
    { s : Multiset α // Multiset.card s = n }
  deriving [DecidableEq α] → DecidableEq _
  ```
  This underscore stands for where `Sym α n` may be inserted, which is
  necessary when `→` is used. The `deriving instance` command can refer to
  scoped variables when delta deriving as well. Breaking change: the
  derived instance's name uses the `instance` command's name generator,
  and the new instance is added to the current namespace.

* [#9804](https://github.com/leanprover/lean4/pull/9804) allows trailing comma in the argument list of `simp?`, `dsimp?`,
  `simpa`, etc... Previously, it was only allowed in the non `?` variants
  of `simp`, `dsimp`, `simp_all`.

* [#9807](https://github.com/leanprover/lean4/pull/9807) adds `Std.List.Zipper.pref` to the simp set of `mleave`.

* [#9809](https://github.com/leanprover/lean4/pull/9809) adds a script for analyzing `grind` E-matching annotations. The
  script is useful for detecting matching loops. We plan to add
  user-facing commands for running the script in the future.

* [#9813](https://github.com/leanprover/lean4/pull/9813) fixes an unexpected bound variable panic in `unfoldReducible`
  used in `grind`.

* [#9814](https://github.com/leanprover/lean4/pull/9814) skips the `normalizeLevels` preprocessing step in `grind` when
  it is not needed.

* [#9818](https://github.com/leanprover/lean4/pull/9818) fixes a bug where the `DecidableEq` deriving handler did not
  take universe levels into account for enumerations (inductive types
  whose constructors all have no fields). Closes #9541.

* [#9819](https://github.com/leanprover/lean4/pull/9819) makes the `unsafe t` term create an auxiliary opaque
  declaration, rather than an auxiliary definition with opaque
  reducibility hints.

* [#9831](https://github.com/leanprover/lean4/pull/9831) adds a delaborator for `Std.Range` notation.

* [#9832](https://github.com/leanprover/lean4/pull/9832) adds simp lemmas `SPred.entails_<n>` to replace
  `SPred.entails_cons` which was dysfunctional as a simp lemma due to
  #8074.

* [#9833](https://github.com/leanprover/lean4/pull/9833) works around a DefEq bug in `mspec` involving delayed
  assignments.

* [#9834](https://github.com/leanprover/lean4/pull/9834) fixes a bug in `mvcgen` triggered by excess state arguments to
  the `wp` application, a situation which arises when working with
  `StateT` primitives.

* [#9841](https://github.com/leanprover/lean4/pull/9841) migrates the ⌜p⌝ notation for embedding pure `p : Prop` into
  `SPred σs` to expand into a simple, first-order expression `SPred.pure p`
  that can be supported by E-matching in `grind`.

* [#9843](https://github.com/leanprover/lean4/pull/9843) makes `mvcgen` produce deterministic case labels for the
  generated VCs. Invariants will be named `inv<n>` and every other VC will
  be named `vc<n>.*`, where the `*` part serves as a loose indication of
  provenance.

* [#9852](https://github.com/leanprover/lean4/pull/9852) removes the `inShareCommon` quick filter used in `grind`
  preprocessing steps. `shareCommon` is no longer used only for fully
  preprocessed terms.

* [#9853](https://github.com/leanprover/lean4/pull/9853) adds `Nat` and `Int` numeral normalizers in `grind`.

* [#9857](https://github.com/leanprover/lean4/pull/9857) ensures `grind` can E-match patterns containing universe
  polymorphic ground sub-patterns. For example, given
  ```
  set_option pp.universes true in
  attribute [grind?] Id.run_pure
  ```
  the pattern
  ```
  Id.run_pure.{u_1}: [@Id.run.{u_1} #1 (@pure.{u_1, u_1} `[Id.{u_1}] `[Applicative.toPure.{u_1, u_1}] _ #0)]
  ```
  contains two nested universe polymorphic ground patterns
  - `Id.{u_1}`
  - `Applicative.toPure.{u_1, u_1}`

* [#9860](https://github.com/leanprover/lean4/pull/9860) fixes E-matching theorem activation in `grind`.

* [#9865](https://github.com/leanprover/lean4/pull/9865) adds improved support for proof-by-reflection to the kernel type
  checker. It addresses the performance issue exposed by #9854. With this
  PR, whenever the kernel type-checks an argument of the form `eagerReduce
  _`, it enters "eager-reduction" mode. In this mode, the kernel is more
  eager to reduce terms. The new `eagerReduce _` hint is often used to
  wrap `Eq.refl true`. The new hint should not negatively impact any
  existing Lean package.

* [#9867](https://github.com/leanprover/lean4/pull/9867) fixes a nondeterministic behavior in `grind ring`.

* [#9880](https://github.com/leanprover/lean4/pull/9880) ensures a local forall is activated at most once per pattern in
  `grind`.

* [#9883](https://github.com/leanprover/lean4/pull/9883) refines the warning message for redundant `grind` arguments. It
  is not based on the actual inferred pattern instead provided kind.

* [#9885](https://github.com/leanprover/lean4/pull/9885) is initially motivated by noticing `Lean.Grind.Preorder.toLE`
  appearing in long Mathlib type class searches; this change will prevent
  these searches. These changes are also helpful preparation for
  potentially dropping the custom `Lean.Grind.*` type classes, and unifying
  with the new type classes introduced in #9729.
````

````markdown
## Library

* [#7450](https://github.com/leanprover/lean4/pull/7450) implements `Nat.dfold`, a dependent analogue of `Nat.fold`.

* [#9096](https://github.com/leanprover/lean4/pull/9096) removes some unnecessary `Decidable*` instance arguments by
  using lemmas in the `Classical` namespace instead of the `Decidable`
  namespace.

* [#9121](https://github.com/leanprover/lean4/pull/9121) allows `grind` to case on the universe variants of `Prod`.

* [#9129](https://github.com/leanprover/lean4/pull/9129) fixes simp lemmas about boolean equalities to say `(!x) = y`
  instead of `(!decide (x = y)) = true`

* [#9135](https://github.com/leanprover/lean4/pull/9135) allows the result type of `forIn`, `foldM` and `fold` on pure
  iterators (`Iter`) to be in a different universe than the iterators.

* [#9142](https://github.com/leanprover/lean4/pull/9142) changes `Fin.reverseInduction` from using well-founded recursion
  to using `let rec`, which makes it have better definitional equality.
  Co-authored by @digama0. See the test below:

  ```lean
  namespace Fin

* [#9145](https://github.com/leanprover/lean4/pull/9145) fixes two typos.

* [#9176](https://github.com/leanprover/lean4/pull/9176) makes `mvcgen` split ifs rather than applying specifications.
  Doing so fixes a bug reported by Rish.

* [#9194](https://github.com/leanprover/lean4/pull/9194) makes the logic and tactics of `Std.Do` universe polymorphic, at
  the cost of a few definitional properties arising from the switch from
  `Prop` to `ULift Prop` in the base case `SPred []`.

* [#9249](https://github.com/leanprover/lean4/pull/9249) adds theorem `BitVec.clzAuxRec_eq_clzAuxRec_of_getLsbD_false` as
  a more general statement than `BitVec.clzAuxRec_eq_clzAuxRec_of_le`,
  replacing the latter in the bitblaster too.

* [#9260](https://github.com/leanprover/lean4/pull/9260) removes uses of `Lean.RBMap` in Lean itself.

* [#9263](https://github.com/leanprover/lean4/pull/9263) fixes `toISO8601String` to produce a string that conforms to the
  ISO 8601 format specification. The previous implementation separated the
  minutes and seconds fragments with a `.` instead of a `:` and included
  timezone offsets without the hour and minute fragments separated by a
  `:`.

* [#9285](https://github.com/leanprover/lean4/pull/9285) removes the unnecessary requirement of `BEq α` for
  `Array.any_push`, `Array.any_push'`, `Array.all_push`, `Array.all_push'`
  as well as `Vector.any_push` and `Vector.all_push`.

* [#9301](https://github.com/leanprover/lean4/pull/9301) adds a `simp` and a `grind` annotation on `Zipper`-related
  theorems to improve reasoning about `Std.Do` invariants.

* [#9391](https://github.com/leanprover/lean4/pull/9391) replaces the proof of the simplification lemma `Nat.zero_mod`
  with
  `rfl` since it is, by design, a definitional equality. This solves an
  issue
  whereby the lemma could not be used by the simplifier when in 'dsimp'
  mode.

* [#9441](https://github.com/leanprover/lean4/pull/9441) fixes the behavior of `String.prev`, aligning the runtime
  implementation with the reference implementation. In particular, the
  following statements hold now:
  - `(s.prev p).byteIdx` is at least `p.byteIdx - 4` and at most
  `p.byteIdx - 1`
  - `s.prev 0 = 0`
  - `s.prev` is monotone

* [#9449](https://github.com/leanprover/lean4/pull/9449) fix the behavior of `String.next` on the scalar boundary (`2 ^
  63 - 1` on 64-bit platforms).

* [#9451](https://github.com/leanprover/lean4/pull/9451) adds support in the `mintro` tactic for introducing `let`/`have`
  binders in stateful targets, akin to `intro`. This is useful when
  specifications introduce such let bindings.

* [#9454](https://github.com/leanprover/lean4/pull/9454) introduces tactic `mleave` that leaves the `SPred` proof mode by
  eta expanding through its abstractions and applying some mild
  simplifications. This is useful to apply automation such as `grind`
  afterwards.

* [#9504](https://github.com/leanprover/lean4/pull/9504) adds a few more `*.by_wp` "adequacy theorems" that allows to
  prove facts about programs in `ReaderM` and `ExceptM` using the `Std.Do`
  framework.

* [#9528](https://github.com/leanprover/lean4/pull/9528) adds `List.zipWithM` and `Array.zipWithM`.

* [#9529](https://github.com/leanprover/lean4/pull/9529) upstreams some helper instances for `NameSet` from Batteries.

* [#9538](https://github.com/leanprover/lean4/pull/9538) adds two lemmas related to `Iter.toArray`.

* [#9577](https://github.com/leanprover/lean4/pull/9577) adds lemmas about `UIntX.toBitVec` and `UIntX.ofBitVec` and `^`.

* [#9586](https://github.com/leanprover/lean4/pull/9586) adds componentwise algebraic operations on `Vector α n`, and
  relevant instances.

* [#9594](https://github.com/leanprover/lean4/pull/9594) optimizes `Lean.Name.toString`, giving a 10% instruction
  benefit.

* [#9609](https://github.com/leanprover/lean4/pull/9609) adds `@[grind =]` to `Prod.lex_def`. Note that `omega` has
  special handling for `Prod.Lex`, and this is needed for `grind`'s cutsat
  module to achieve parity.

* [#9616](https://github.com/leanprover/lean4/pull/9616) introduces checks to make sure that the IO functions produce
  errors when inputs contain NUL bytes (instead of ignoring everything
  after the first NUL byte).

* [#9620](https://github.com/leanprover/lean4/pull/9620) adds the separate directions of
  `List.pairwise_iff_forall_sublist` as named lemmas.

* [#9621](https://github.com/leanprover/lean4/pull/9621) renames `Xor` to `XorOp`, to match `AndOp`, etc.

* [#9622](https://github.com/leanprover/lean4/pull/9622) adds a missing lemma about `List.sum`, and a grind annotation.

* [#9701](https://github.com/leanprover/lean4/pull/9701) switches to a non-verloading local `Std.Do.Triple` notation in
  SpecLemmas.lean to work around a stage2 build failure.

* [#9721](https://github.com/leanprover/lean4/pull/9721) tags more `SInt` and `UInt` lemmas with `int_toBitVec` so
  `bv_decide`
  can handle casts between them and negation.

* [#9729](https://github.com/leanprover/lean4/pull/9729) introduces a canonical way to endow a type with an order
  structure. The basic operations (`LE`, `LT`, `Min`, `Max`, and in later
  PRs `BEq`, `Ord`, ...) and any higher-level property (a preorder, a
  partial order, a linear order etc.) are then put in relation to `LE` as
  necessary. The PR provides `IsLinearOrder` instances for many core types
  and updates the signatures of some lemmas.

* [#9732](https://github.com/leanprover/lean4/pull/9732) re-implements `IO.waitAny` using Lean instead of C++. This is to
  reduce the size and
  complexity of `task_manager` in order to ease future refactorings.

* [#9736](https://github.com/leanprover/lean4/pull/9736) implements the option `mvcgen +jp` to employ a slightly lossy VC
  encoding for join points that prevents exponential VC blowup incurred by
  naïve splitting on control flow.

* [#9739](https://github.com/leanprover/lean4/pull/9739) removes the `instance` attribute from `lexOrd` that was
  accidentally applied in `Std.Classes.Ord.Basic`.

* [#9757](https://github.com/leanprover/lean4/pull/9757) adds `grind` annotations for key `Std.Do.SPred` lemmas.

* [#9782](https://github.com/leanprover/lean4/pull/9782) corrects the `Inhabited` instance of `StdGen` to use a valid
  initial state for the pseudorandom number generator. Previously, the
  `default` generator had the property that `Prod.snd (stdNext default) =
  default`, so it would produce only constant sequences.

* [#9787](https://github.com/leanprover/lean4/pull/9787) adds a simp lemma `PostCond.const_apply`.

* [#9792](https://github.com/leanprover/lean4/pull/9792) adds `@[expose]` to two definitions with `where` clauses that
  Batteries proves theorems about.

* [#9799](https://github.com/leanprover/lean4/pull/9799) fixes the #9410 issue.

* [#9805](https://github.com/leanprover/lean4/pull/9805) improves the API for invariants and postconditions and as such
  introduces a few breaking changes to the existing pre-release API around
  `Std.Do`. It also adds Markus Himmel's `pairsSumToZero` example as a
  test case.

* [#9832](https://github.com/leanprover/lean4/pull/9832) adds simp lemmas `SPred.entails_<n>` to replace
  `SPred.entails_cons` which was dysfunctional as a simp lemma due to
  #8074.

* [#9841](https://github.com/leanprover/lean4/pull/9841) migrates the ⌜p⌝ notation for embedding pure `p : Prop` into
  `SPred σs` to expand into a simple, first-order expression `SPred.pure p`
  that can be supported by E-matching in `grind`.

* [#9848](https://github.com/leanprover/lean4/pull/9848) adds `@[spec]` lemmas for `forIn` and `forIn'` at `Std.PRange`.

* [#9850](https://github.com/leanprover/lean4/pull/9850) adds a delaborator for `Std.PRange` notation.

## Compiler

* [#8691](https://github.com/leanprover/lean4/pull/8691) ensures that the state is reverted when compilation using the
  new compiler fails. This is especially important for noncomputable
  sections where the compiler might generate half-compiled functions which
  may then be erroneously used while compiling other functions.

* [#9134](https://github.com/leanprover/lean4/pull/9134) changes ToIR to call `lowerEnumToScalarType?` with
  `ConstructorVal.induct` rather than the name of the constructor itself.
  This was an oversight in some refactoring of code in the new compiler
  before landing it. It should not affect runtime of compiled code (due to
  the extra tagging/untagging being optimized by LLVM), but it does make
  IR for the interpreter slightly more efficient.

* [#9144](https://github.com/leanprover/lean4/pull/9144) adds support for representing more inductive as enums,
  summarized up as extending support to those that fail to be enums
  because of parameters or irrelevant fields. While this is nice to have,
  it is actually motivated by correctness of a future desired
  optimization. The existing type representation is unsound if we
  implement `object`/`tobject` distinction between values guaranteed to be
  an object pointer and those that may also be a tagged scalar. In
  particular, types like the ones added in this PR's tests would have all
  of their constructors encoded via tagged values, but under the natural
  extension of the existing rules of type representation they would be
  considered `object` rather than `tobject`.

* [#9154](https://github.com/leanprover/lean4/pull/9154) tightens the IR typing rules around applications of closures.
  When re-reading some code, I realized that the code in `mkPartialApp`
  has a clear typo—`.object` and `type` should be swapped. However, it
  doesn't matter, because later IR passes smooth out the mismatch here. It
  makes more sense to be strict up-front and require applications of
  closures to always return an `.object`.

* [#9159](https://github.com/leanprover/lean4/pull/9159) enforces the non-inlining of _override impls in the base phase
  of LCNF compilation. The current situation allows for constructor/cases
  mismatches to be exposed to the simplifier, which triggers an assertion
  failure. The reason this didn't show up sooner for Expr is that Expr has
  a custom extern implementation of its computed field getter.

* [#9177](https://github.com/leanprover/lean4/pull/9177) makes the `pullInstances` pass avoid pulling any instance
  expressions containing erased propositions, because we don't correctly
  represent the dependencies that remain after erasure.

* [#9198](https://github.com/leanprover/lean4/pull/9198) changes the compiler's specialization analysis to consider
  higher-order params that are rebundled in a way that only changes their
  `Prop` arguments to be fixed. This means that they get specialized with
  a mere `@[specialize]`, rather than the compiler having to opt-in to
  more aggressive parameter-specific specialization.

* [#9207](https://github.com/leanprover/lean4/pull/9207) makes the offending declaration clickable in the error message
  produced when something should be marked `noncomputable`.

* [#9209](https://github.com/leanprover/lean4/pull/9209) changes the `getLiteral` helper function of `elimDeadBranches`
  to correctly handle inductives with constructors. This function is not
  used as often as it could be, which makes this issue rare to hit outside
  of targeted test cases.

* [#9218](https://github.com/leanprover/lean4/pull/9218) makes the LCNF `elimDeadBranches` pass handle unsafe decls a bit
  more carefully. Now the result of an unsafe decl will only become ⊤ if
  there is value flow from a recursive call.

* [#9221](https://github.com/leanprover/lean4/pull/9221) removes code that has the false assumption that LCNF local vars
  can occur in types. There are other comments in `ElimDead.lean`
  asserting that this is not possible, so this must have been a change
  early in the development of the new compiler.

* [#9224](https://github.com/leanprover/lean4/pull/9224) changes the `toMono` pass to consider the type of an application
  and erase all arguments corresponding to erased params. This enables a
  lightweight form of relevance analysis by changing the mono type of a
  decl. I would have liked to unify this with the behavior for
  constructors, but my attempt to give constructors the same behavior in
  #9222 (which was in preparation for this PR) had a minor performance
  regression that is really incidental to the change. Still, I decided to
  hold off on it for the time being. In the future, we can hopefully
  extend this to constructors, extern decls, etc.

* [#9266](https://github.com/leanprover/lean4/pull/9266) adds support for `.mdata` in LCNF mono types (and then drops it
  at the IR type level instead). This better matches the behavior of
  extern decls in the C++ code of the old compiler, which is still being
  used to create extern decls at the moment and will soon be replaced.

* [#9268](https://github.com/leanprover/lean4/pull/9268) moves the implementation of `lean_add_extern`/`addExtern` from
  C++ into Lean. I believe is the last C++ helper function from the
  library/compiler directory being relied upon by the new compiler. I put
  it into its own file and duplicated some code because this function
  needs to execute in CoreM, whereas the other IR functions live in their
  own monad stack. After the C++ compiler is removed, we can move the IR
  functions into CoreM.

* [#9275](https://github.com/leanprover/lean4/pull/9275) removes the old compiler written in C++.

* [#9279](https://github.com/leanprover/lean4/pull/9279) fixes the `compiler.extract_closed` option after migrating it to
  Lean (and adds a test so it would be caught in the future).

* [#9310](https://github.com/leanprover/lean4/pull/9310) fixes IR constructor argument lowering to correctly handle an
  irrelevant argument being passed for a relevant parameter in all cases.
  This happened because constructor argument lowering (incompletely)
  reimplemented general LCNF-to-IR argument lowering, and the fix is to
  just adopt the generic helper functions. This is probably due to an
  incomplete refactoring when the new compiler was still on a branch.

* [#9336](https://github.com/leanprover/lean4/pull/9336) changes the implementation of `trace.Compiler.result` to use the
  decls as they are provided rather than looking them up in the LCNF mono
  environment extension, which was seemingly done to save the trouble of
  re-normalizing fvar IDs before printing the decl. This means that the
  `._closed` decls created by the `extractClosed` pass will now be
  included in the output, which was definitely confusing before if you
  didn't know what was happening.

* [#9344](https://github.com/leanprover/lean4/pull/9344) correctly populates the `xType` field of the `IR.FnBody.case`
  constructor. It turns out that there is no obvious consequence for this
  being incorrect, because it is conservatively recomputed by the `Boxing`
  pass.

* [#9393](https://github.com/leanprover/lean4/pull/9393) fixes an unsafe trick where a sentinel for a hash table of Exprs
  (keyed by pointer) is created by constructing a value whose runtime
  representation can never be a valid Expr. The value chosen for this
  purpose was Unit.unit, which violates the inference that Expr has no
  scalar constructors. Instead, we change this to a freshly allocated Unit
  × Unit value.

* [#9411](https://github.com/leanprover/lean4/pull/9411) adds support for compilation of `casesOn` for subsingletons. We
  rely on the elaborator's type checking to restrict this to inductives in
  `Prop` that can actually eliminate into `Type n`. This does not yet
  cover other recursors of these types (or of inductives not in `Prop` for
  that matter).

* [#9703](https://github.com/leanprover/lean4/pull/9703) changes the LCNF `elimDeadBranches` pass so that it considers
  all non-`Nat` literal types to be `⊤`. It turns out that fixing this to
  correctly handle all of these types with the current abstract value
  representation is surprisingly nontrivial, and it's better to just land
  the fix first.

* [#9720](https://github.com/leanprover/lean4/pull/9720) removes an error which implicitly assumes that the sort of type
  dependency between erased types present in the test being added can not
  occur. It would be difficult to refine the error using only the
  information present in LCNF types, and it is of very little ongoing
  value (I don't recall it ever finding an actual problem), so it makes
  more sense to delete it.

* [#9827](https://github.com/leanprover/lean4/pull/9827) changes the lowering of `Quot.lcInv` (the compiler-internal form
  of `Quot.lift`) in `toMono` to support overapplication.

* [#9847](https://github.com/leanprover/lean4/pull/9847) adds a check for reursive decls in this bespoke inlining path,
  which fixes a regression from the old compiler.

* [#9864](https://github.com/leanprover/lean4/pull/9864) adds new variants of `Array.getInternal` and
  `Array.get!Internal` that return their argument borrowed, i.e. without a
  reference count increment. These are intended for use by the compiler in
  cases where it can determine that the array will continue to hold a
  valid reference to the element for the returned value's lifetime.

## Pretty Printing

* [#8391](https://github.com/leanprover/lean4/pull/8391) adds an unexpander for `Vector.mk` that unexpands `Vector.mk
  #[...] _` to `#v[...]`.
  ```lean
  -- previously:
  #check #v[1, 2, 3] -- { toArray := #[1, 2, 3], size_toArray := ⋯ } : Vector Nat 3
  -- now:
  #check #v[1, 2, 3] -- #v[1, 2, 3] : Vector Nat 3
  ```

* [#9475](https://github.com/leanprover/lean4/pull/9475) fixes the way some syntaxes are pretty printed due to missing
  whitespace advice.

* [#9494](https://github.com/leanprover/lean4/pull/9494) fixes an issue that caused some error messages to attempt to
  display hovers for nonexistent identifiers.

* [#9555](https://github.com/leanprover/lean4/pull/9555) allows hints in message data to specify custom preview spans
  that extend beyond the edit region specified by the code action.

* [#9778](https://github.com/leanprover/lean4/pull/9778) modifies the pretty printing of anonymous metavariables to use
  the index rather than the internal name. This leads to smaller numerical
  suffixes in `?m.123` since the indices are numbered within a given
  metavariable context rather than across an entire file, hence each
  command gets its own numbering. This does not yet affect pretty printing
  of universe level metavariables.

## Documentation

* [#9093](https://github.com/leanprover/lean4/pull/9093) adds a missing docstring for `ToFormat.toFormat`.

* [#9152](https://github.com/leanprover/lean4/pull/9152) fixes an obsolete docstring for `registerDerivingHandler`

* [#9593](https://github.com/leanprover/lean4/pull/9593) simplifies the docstring for `propext` significantly.

## Server

* [#9040](https://github.com/leanprover/lean4/pull/9040) improves the 'Go to Definition' UX, specifically:
  - Using 'Go to Definition' on a type class projection will now extract
  the specific instances that were involved and provide them as locations
  to jump to. For example, using 'Go to Definition' on the `toString` of
  `toString 0` will yield results for `ToString.toString` and `ToString
  Nat`.
  - Using 'Go to Definition' on a macro that produces syntax with type
  class projections will now also extract the specific instances that were
  involved and provide them as locations to jump to. For example, using
  'Go to Definition' on the `+` of `1 + 1` will yield results for
  `HAdd.hAdd`, `HAdd α α α` and `Add Nat`.
  - Using 'Go to Declaration' will now provide all the results of 'Go to
  Definition' in addition to the elaborator and the parser that were
  involved. For example, using 'Go to Declaration' on the `+` of `1 + 1`
  will yield results for `HAdd.hAdd`, `HAdd α α α`, `Add Nat`,
  ``macro_rules | `($x + $y) => ...`` and `infixl:65 " + " => HAdd.hAdd`.
  - Using 'Go to Type Definition' on a value with a type that contains
  multiple constants will now provide 'Go to Definition' results for each
  constant. For example, using 'Go to Type Definition' on `x` for `x :
  Array Nat` will yield results for `Array` and `Nat`.

* [#9163](https://github.com/leanprover/lean4/pull/9163) disables the use of the header produced by `lake setup-file` in
  the server for now. It will be re-enabled once Lake takes into account
  the header given by the server when processing workspace modules.
  Without that, `setup-file` header can produce odd behavior when the file
  on disk and in an editor disagree on whether the file participates in
  the module system.

* [#9563](https://github.com/leanprover/lean4/pull/9563) performs some micro optimizations on fuzzy matching for a `~20%`
  instructions win.

* [#9784](https://github.com/leanprover/lean4/pull/9784) ensures the editor progress bar better reflects the actual
  progress of parallel elaboration.

## Lake

* [#9053](https://github.com/leanprover/lean4/pull/9053) updates Lake to resolve the `.olean` files for transitive
  imports for Lean through the `modules` field of `lean --setup`. This
  enables means the Lean can now directly use the `.olean` files from the
  Lake cache without needed to locate them at a specific hierarchical
  path.

* [#9101](https://github.com/leanprover/lean4/pull/9101) fixes a bug introduce by #9081 where the source file was dropped
  from the module input trace and some entries were dropped from the
  module job log.

* [#9162](https://github.com/leanprover/lean4/pull/9162) changes the key Lake uses for the `,ir` artifact in the content
  hash data structure to `r`, maintaining the convention of single
  character key names.

* [#9165](https://github.com/leanprover/lean4/pull/9165) fixes two issues with Lake's process of creating static
  archives.

* [#9332](https://github.com/leanprover/lean4/pull/9332) changes the dependency cloning mechanism in lake so the log
  message that lake is cloning a
  dependency occurs before it is finished doing so (and instead before it
  starts). This has been a
  huge source of confusion for users that don't understand why lake seems
  to be just stuck for no
  reason when setting up a new project, the output now is:
  ```
  λ lake +lean4 new math math
  info: downloading mathlib `lean-toolchain` file
  info: math: no previous manifest, creating one from scratch
  info: leanprover-community/mathlib: cloning https://github.com/leanprover-community/mathlib4
  <hang>
  info: leanprover-community/mathlib: checking out revision 'cd11c28c6a0d514a41dd7be9a862a9c8815f8599'
  ```

* [#9434](https://github.com/leanprover/lean4/pull/9434) changes the Lake local cache infrastructure to restore
  executables and shared and static libraries from the cache. This means
  they keep their expected names, which some use cases still rely on.

* [#9435](https://github.com/leanprover/lean4/pull/9435) adds the `libPrefixOnWindows` package and library configuration
  option. When enabled, Lake will prefix static and shared libraries with
  `lib` on Windows (i.e., the same way it does on Unix).

* [#9436](https://github.com/leanprover/lean4/pull/9436) adds the number of jobs run to the final message Lake produces
  on a successfully run of `lake build`.

* [#9478](https://github.com/leanprover/lean4/pull/9478) adds proper Lake support for `meta import`. Module IR is now
  tracked in traces and in the pre-resolved modules Lake passes to `lean
  --setup`.

* [#9525](https://github.com/leanprover/lean4/pull/9525) fixes Lake's handling of a module system `import all`.
  Previously, Lake treated `import all` the same a non-module `import`,
  importing all private data in the transitive import tree. Lake now
  distinguishes the two, with `import all M` just importing the private
  data of `M`. The direct private imports of `M` are followed, but they
  are not promoted.

* [#9559](https://github.com/leanprover/lean4/pull/9559) changes `lake setup-file` to use the server-provided header for
  workspace modules.

* [#9604](https://github.com/leanprover/lean4/pull/9604) restricts Lake's production of thin archives to only the Windows
  core build (i.e., `bootstrap = true`). The unbundled `ar` usually used
  for core builds on macOS does not support `--thin`, so we avoid using it
  unless necessary.

* [#9677](https://github.com/leanprover/lean4/pull/9677) adds build times to each build step of the build monitor (under
  `-v` or in CI) and delays exiting on a `--no-build` until after the
  build monitor finishes. Thus, a `--no-build` failure will now report
  which targets blocked Lake by needing a rebuild.

* [#9697](https://github.com/leanprover/lean4/pull/9697) fixes the handling in `lake lean` and `lake setup-file` of a
  library source file with multiple dots (e.g., `src/Foo.Bar.lean`).

* [#9698](https://github.com/leanprover/lean4/pull/9698) adjusts the formatting type classes for `lake query` to no
  longer require both a text and JSON form and instead work with any
  combination of the two. The classes have also been renamed. In addition,
  the query formatting of a text module header has been improved to only
  produce valid headers.

## Other

* [#9106](https://github.com/leanprover/lean4/pull/9106) fixes `undefined symbol: lean::mpz::divexact(lean::mpz const&,
  lean::mpz const&)` when building without `LEAN_USE_GMP`

* [#9114](https://github.com/leanprover/lean4/pull/9114) further improves release automation, automatically incorporating
  material from `nightly-testing` and `bump/v4.X.0` branches in the bump
  PRs to downstream repositories.

* [#9659](https://github.com/leanprover/lean4/pull/9659) fixes compatibility of the `trace.profiler.output` option with
  newer versions of Firefox Profiler

````
