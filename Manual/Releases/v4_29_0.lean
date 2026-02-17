/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.29.0-rc1 (2026-02-17)" =>
%%%
tag := "release-v4.29.0"
file := "v4.29.0"
%%%

For this release, 303 changes landed. In addition to the 81 feature additions and 71 fixes listed below there were 18 refactoring changes, 15 documentation improvements, 22 performance improvements, 20 improvements to the test suite and 74 other changes.

# Language

* [#11963](https://github.com/leanprover/lean4/pull/11963) activates `getElem?_pos` more aggressively, triggered by `c[i]`.

* [#12028](https://github.com/leanprover/lean4/pull/12028) gives a simpler semantics to `noncomputable`, improving
  predictability as well as preparing codegen to be moved into a separate
  build step without breaking immediate generation of error messages.

* [#12110](https://github.com/leanprover/lean4/pull/12110) fixes a SIGFPE crash on `x86_64` when evaluating `(ISize.minValue
  / -1 : ISize)`, filling an omission from #11624.

* [#12159](https://github.com/leanprover/lean4/pull/12159) makes Std.Do's `post` macro universe polymorphic by expanding to
  `PUnit.unit` instead of `()`.

* [#12160](https://github.com/leanprover/lean4/pull/12160) removes calls to `check` that we expect to pass under normal
  circumstances. This may be re-added later guarded by a `debug` option.

* [#12164](https://github.com/leanprover/lean4/pull/12164) uses the `.inj` theorem in the proof of one direction of the
  `.injEq` theorem.

* [#12179](https://github.com/leanprover/lean4/pull/12179) ensures `isDefEq` does not increase the transparency mode to
  `.default` when checking whether implicit arguments are definitionally
  equal. The previous behavior was creating scalability problems in
  Mathlib. That said, this is a very disruptive change. The previous
  behavior can be restored using the command
  ```
  set_option backward.isDefEq.respectTransparency false
  ```

* [#12184](https://github.com/leanprover/lean4/pull/12184) ensures that the `mspec` tactic does not assign synthetic opaque
  MVars occurring in the goal, just like the `apply` tactic.

* [#12190](https://github.com/leanprover/lean4/pull/12190) adds the `introSubstEq` MetaM tactic, as an optimization over
  `intro h; subst h` that avoids introducing `h : a = b` if it can be
  avoided,
  which is the case when `b` can be reverted without reverting anything
  else. Speeds up the generation of `injEq` theorem.

* [#12217](https://github.com/leanprover/lean4/pull/12217) implements RFC #12216: native computation (`native_decide`,
  `bv_decide`) is represented in the logic as one axiom per computation,
  asserting the equality that was obtained from the native computation.
  `#print axiom` will no longer show `Lean.trustCompiler`, but rather the
  auto-generated names of these axioms (with, for example,
  `._native.bv_decide.` in the name). See the RFC for more information.

* [#12219](https://github.com/leanprover/lean4/pull/12219) fixes a unification issue that appeared in
  `Lean.Meta.MkIffOfInductiveProp` machinery that was upstreamed from
  Mathlib. Inside of `toInductive`, wrong free variables were passed,
  which made it impossible to perform a unification in certain cases.

* [#12236](https://github.com/leanprover/lean4/pull/12236) adds `orElse` combinator to simprocs of `Sym.Simp`.

* [#12243](https://github.com/leanprover/lean4/pull/12243) fixes #12240, where `deriving Ord` failed with `Unknown
  identifier a✝`.

* [#12247](https://github.com/leanprover/lean4/pull/12247) adds the new transparency setting `@[instance_reducible]`. We
  used to check whether a declaration had `instance` reducibility by using
  the `isInstance` predicate. However, this was not a robust solution
  because:

  - We have scoped instances, and `isInstance` returns `true` only if the
  scope is active.

* [#12263](https://github.com/leanprover/lean4/pull/12263) implements the second part of #12247.

* [#12269](https://github.com/leanprover/lean4/pull/12269) refines upon #12106, by setting the `isRecursive` env extension
  after adding the declaration, but before processing attributes like
  `macro_inline` that want to look at the flag. Fixes #12268.

* [#12283](https://github.com/leanprover/lean4/pull/12283) introduces `cbv_opaque` attribute that allows one to mark
  definitions not to be unfolded by the `cbv` tactic.

* [#12285](https://github.com/leanprover/lean4/pull/12285) implements a cache for the positions of class universe level
  parameters that only appear in output parameter types.

* [#12286](https://github.com/leanprover/lean4/pull/12286) ensures the type resolution cache properly caches results for
  type classe containing output parameters.

* [#12324](https://github.com/leanprover/lean4/pull/12324) adds a default `Inhabited` instance to `Theorem` type.

* [#12329](https://github.com/leanprover/lean4/pull/12329) adds the option `doc.verso.module`. If set, it controls whether
  module docstrings use Verso syntax. If not set, it defaults to the value
  of the `doc.verso` option.

* [#12338](https://github.com/leanprover/lean4/pull/12338) implements preparatory work for #12179. It implements a new
  feature in `isDefEq` to ensure it does not increase the transparency
  level to `.default` when checking definitionally equality of implicit
  arguments. This transparency level bump was introduced in Lean 3, but it
  is not a performance issue and is affecting Mathlib. adds the
  new feature, but it is disabled by default.

* [#12339](https://github.com/leanprover/lean4/pull/12339) fixes a diamond problem in delta deriving where
  instance-implicit class parameters in the derived instance type were
  using instances synthesized for the underlying type, not the alias type.

* [#12340](https://github.com/leanprover/lean4/pull/12340) implements better support for unfolding class fields marked as
  `reducible`. For example, we want to mark fields that are types such as
  ```
  MonadControlT.stM : Type u -> Type u
  ```
  The motivation is similar to our heuristic that type definitions should
  be abbreviations.
  Now, suppose we want to unfold `stM m (ExceptT ε m) α` using the
  `.reducible` transparency setting, we want the result to be `stM m m
  (MonadControl.stM m (ExceptT ε m) α)` instead of
  `(instMonadControlTOfMonadControl m m (ExceptT ε m)).1 α`. The latter
  would defeat the intent of marking the field as reducible, since the
  instance `instMonadControlTOfMonadControl` is `[instance_reducible]` and
  the resulting term would be stuck when using `.reducible` transparency
  mode.

* [#12353](https://github.com/leanprover/lean4/pull/12353) ressurects the dead trace class `Elab.resume` by redirecting the
  non-existant `Elab.resuming` to it.

* [#12355](https://github.com/leanprover/lean4/pull/12355) adds `isBoolTrueExpr` and `isBoolFalseExpr` functions to `SymM`

* [#12391](https://github.com/leanprover/lean4/pull/12391) makes `simpCond` public. It is needed to avoid code duplication
  in #12361

* [#12395](https://github.com/leanprover/lean4/pull/12395) adds `mvcgen` support for specifications in the local context.
  Example:

  ```
  import Std.Tactic.Do

  open Std.Do

  set_option mvcgen.warning false

  def foo (x : Id Nat → Id Nat) : Id Nat := do
    let r₁ ← x (pure 42)
    let r₂ ← x (pure 26)
    pure (r₁ + r₂)

  theorem foo_spec
      (x : Id Nat → Id Nat)
      (x_spec : ∀ (k : Id Nat) (_ : ⦃⌜True⌝⦄ k ⦃⇓r => ⌜r % 2 = 0⌝⦄), ⦃⌜True⌝⦄ x k ⦃⇓r => ⌜r % 2 = 0⌝⦄) :
      ⦃⌜True⌝⦄ foo x ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
    mvcgen [foo, x_spec] <;> grind

  def bar (k : Id Nat) : Id Nat := do
    let r ← k
    if r > 30 then return 12 else return r

  example : ⦃⌜True⌝⦄ foo bar ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
    mvcgen [foo_spec, bar]
  ```

* [#12407](https://github.com/leanprover/lean4/pull/12407) is similar to #12403.

* [#12416](https://github.com/leanprover/lean4/pull/12416) makes `Sym.Simp.toBetaApp` public. This is necessary for the
  refactor of the main `cbv` simproc in #12417.

* [#12425](https://github.com/leanprover/lean4/pull/12425) fixes a bug in `mvcgen` caused by incomplete `match` splitting.

* [#12427](https://github.com/leanprover/lean4/pull/12427) makes `mvcgen` suggest to use `-trivial` when doing so avoids a
  recursion depth error.

* [#12429](https://github.com/leanprover/lean4/pull/12429) sets the `irreducible` attribute before generating the equations
  for recursive definitions. This prevents these equations to be marked as
  `defeq`, which could lead to `simp` generation proofs that do not type
  check at default transparency.

* [#12460](https://github.com/leanprover/lean4/pull/12460) fixes an `AppBuilder` exception in the `cbv` tactic when
  simplifying projections whose projection function is dependent (closes
  #12457).

* [#12507](https://github.com/leanprover/lean4/pull/12507) fixes #12495 where equational theorem generation fails for
  structurally recursive definitions using a Box-like wrapper around
  nested inductives.

# Library

* [#11811](https://github.com/leanprover/lean4/pull/11811) proves that membership is preserved by eraseDups: an element
  exists in the deduplicated list iff it was in the original.

* [#11832](https://github.com/leanprover/lean4/pull/11832) uses an `Array` instead of a `List` to store the clauses in
  `Std.CNF`. This reduces the memory footprint and pressure on the
  allocator, leading to noticeable performance changes with gigantic CNFs.

* [#11936](https://github.com/leanprover/lean4/pull/11936) provides `Array` operations analogous to `List.min(?)` and
  `List.max(?)`.

* [#11938](https://github.com/leanprover/lean4/pull/11938) introduces projected minima and maxima, also known as
  "argmin/argmax", for lists under the names `List.minOn` and
  `List.maxOn`. It also introduces `List.minIdxOn` and `List.maxIdxOn`,
  which return the index of the minimal or maximal element. Moreover,
  there are variants with `?` suffix that return an `Option`. The change
  further introduces new instances for opposite orders, such as
  `LE.opposite`, `IsLinearOrder.opposite` etc. The change also adds the
  missing `Std.lt_irrefl` lemma.

* [#11943](https://github.com/leanprover/lean4/pull/11943) introduces the theorem
  `BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend` theorem, proving
  `x.sshiftRight n` is equivalent to first sign-extending `x`, extracting
  the appropriate least significant bits, and then setting the width back
  to `w`.

* [#11994](https://github.com/leanprover/lean4/pull/11994) provides more lemmas about sums of lists/arrays/vectors,
  especially sums of `Nat` or `Int` lists/arrays/vectors.

* [#12017](https://github.com/leanprover/lean4/pull/12017) makes several small improvements to the list/array/vector API:
  * It fixes typos in `Init.Core`.
  * It adds `List.isSome_min_iff` and `List.isSome_max_iff`.
  * It adds `grind` and `simp` annotations to various previously
  unannotated lemmas.
  * It adds lemmas for characterizing `∃ x ∈ xs, P x` using indices as `∃
  (i : Nat), ∃ hi, P (xs[i])`, and similar universally quantified lemmas:
  `exists_mem_iff_exists_getElem` and `forall_mem_iff_forall_getElem`.
  * It adds `Vector.toList_zip`.
  * It adds `map_ofFn` and `ofFn_getElem` for lists/arrays/vectors.

* [#12019](https://github.com/leanprover/lean4/pull/12019) provides the `Nat`/`Int` lemmas `x ≤ y * z ↔ (x + z - 1) / z ≤
  y`, `x ≤ y * z ↔ (x + y - 1) / y ≤ z` and `x / z + y / z ≤ (x + y) / z`.

* [#12108](https://github.com/leanprover/lean4/pull/12108) adds `prefix_map_iff_of_injective` and
  `suffix_map_iff_of_injective` lemmas to Init.Data.List.Nat.Sublist.

* [#12161](https://github.com/leanprover/lean4/pull/12161) adds `Option.of_wp_eq` and `Except.of_wp_eq`, similar to the
  existing `Except.of_wp`. `Except.of_wp` is deprecated because applying
  it requires prior generalization, at which point it is more convenient
  to use `Except.of_wp_eq`.

* [#12162](https://github.com/leanprover/lean4/pull/12162) adds the function `Std.Iter.first?` and proves the specification
  lemma `Std.Iter.first?_eq_match_step` if the iterator is productive.

* [#12170](https://github.com/leanprover/lean4/pull/12170) adjusts the grind annotations for List.take/drop, and adds two
  theorems.

* [#12181](https://github.com/leanprover/lean4/pull/12181) adds two missing order instances for `Int`.

* [#12193](https://github.com/leanprover/lean4/pull/12193) adds `DecidableEq` instances for `Sigma` and `PSigma`.

* [#12204](https://github.com/leanprover/lean4/pull/12204) adds theorems showing the consistency between `find?` and the
  various index-finding functions. The theorems establish bidirectional
  relationships between finding elements and finding their indices.

* [#12212](https://github.com/leanprover/lean4/pull/12212) adds the function `Std.Iter.isEmpty` and proves the
  specification lemmas `Std.Iter.isEmpty_eq_match_step` and
  `Std.Iter.isEmpty_toList` if the iterator is productive.

* [#12220](https://github.com/leanprover/lean4/pull/12220) fixes a bug on Windows with `IO.Process.spawn` where setting an
  environment variable to the empty string would not set the environment
  variable on the subprocess.

* [#12234](https://github.com/leanprover/lean4/pull/12234) introduces an `Iter.step_eq` lemma that fully unfolds an
  `Iter.step` call, bypassing layers of unfolding.

* [#12249](https://github.com/leanprover/lean4/pull/12249) adds some lemmas about the interaction of `sum`, `min` and `max`
  about arrays that already exist for lists.

* [#12250](https://github.com/leanprover/lean4/pull/12250) introduces the defining equality `Triple.iff` and uses that in
  proofs instead of relying on definitional equality. It also introduces
  `Triple.iff_conseq` that is useful for backward reasoning and introduces
  verification conditions. Similarly, `Triple.entails_wp_*` theorems are
  introduced for backward reasoning where the target is an stateful
  entailment rather than a triple.

* [#12258](https://github.com/leanprover/lean4/pull/12258) adds theorems that directly state that div and mod form an
  injective pair: if `a / n = b / n` and `a % n = b % n` then `a = b`.
  These complement existing div/mod lemmas and are useful for extension
  arguments.

* [#12277](https://github.com/leanprover/lean4/pull/12277) adds `IO.FS.Metadata.numLinks`, which contains the number of
  hard links to a file.

* [#12281](https://github.com/leanprover/lean4/pull/12281) changes the definition of `Squash` to use `Quotient` by
  upstreaming
  [`true_equivalence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html#true_equivalence)
  (now `equivalence_true`) and
  [`trueSetoid`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html#trueSetoid)
  (now `Setoid.trivial`). The new definition is def-eq to the old one, but
  ensures that `Squash` can be used whenever a `Quotient` argument is
  expected without having to explicitly provide the setoid.

* [#12282](https://github.com/leanprover/lean4/pull/12282) fixes a platform inconsistency in `IO.FS.removeFile` where it
  could not delete read-only files on Windows.

* [#12290](https://github.com/leanprover/lean4/pull/12290) moves the `PredTrans.apply` structure field into a separate
  `def`. Doing so improves kernel reduction speed because the kernel is
  less likely to unfold definitions compared to structure field
  projections. This causes minor shifts in `simp` normal forms.

* [#12301](https://github.com/leanprover/lean4/pull/12301) introduces the functions `(String|Slice).posGE` and
  `(String|Slice).posGT` will full verification and deprecates
  `Slice.findNextPos` in favor of `Slice.posGT`.

* [#12305](https://github.com/leanprover/lean4/pull/12305) adds various uninteresting lemmas about basic types, extracted
  from the KMP verification.

* [#12311](https://github.com/leanprover/lean4/pull/12311) exposes the chain and `is_sup` definitions such that other modules
  can declare custom CCPO instances.

* [#12312](https://github.com/leanprover/lean4/pull/12312) reverses the relationship between the `ForwardPattern` and
  `ToForwardSearcher` classes.

* [#12318](https://github.com/leanprover/lean4/pull/12318) avoids undefined behavior in `String.Slice.hash` on unaligned
  substrings.
  This could produce a SIGILL on some Arm platforms.

* [#12322](https://github.com/leanprover/lean4/pull/12322) adds `String.Slice.Subslice`, which is an unbundled version of
  `String.Slice`.

* [#12333](https://github.com/leanprover/lean4/pull/12333) adds the basic typeclasses that will be used in the verification
  of our string searching infrastructure.

* [#12341](https://github.com/leanprover/lean4/pull/12341) adds a few unification hints that we will need after
  `backward.isDefEq.respectTransparency` is `true` by default.

* [#12346](https://github.com/leanprover/lean4/pull/12346) shows `s == t ↔ s.copy = t.copy` for `s t : String.Slice` and
  establishes the right-hand side as the simp normal form.

* [#12349](https://github.com/leanprover/lean4/pull/12349) builds on #12333 and proves that `Char` and `Char -> Bool`
  patterns are lawful.

* [#12352](https://github.com/leanprover/lean4/pull/12352) improves the slice API with lemmas for `drop`/`take` operations
  on `Subarray` and more lemmas about `Std.Slice.fold`, `Std.Slice.foldM`
  and `Std.Slice.forIn`. It also changes the `simp` and `grind`
  annotations for `Slice`-related lemmas. Lemmas converting between slices
  of different shapes are no longer `simp`/`grind`-annotated because they
  often complicated lemmas and hindered automation.

* [#12358](https://github.com/leanprover/lean4/pull/12358) improves the `simp` and `grind` rule framework for
  `PredTrans.apply` and also renames the respective lemmas according to
  convention.

* [#12359](https://github.com/leanprover/lean4/pull/12359) deprecates `extract_eq_drop_take` in favor of the more correct
  name `extract_eq_take_drop`, so that we'll be able to use the old name
  for a lemma `xs.extract start stop = (xs.take stop).drop start`. Until
  the deprecation deadline has passed, this new lemma will be called
  `extract_eq_drop_take'`.

* [#12360](https://github.com/leanprover/lean4/pull/12360) provides a `LawfulForwardPatternModel` instance for string
  patterns, i.e., it proves correctness of the `dropPrefix?` and
  `startsWith` functions for string patterns.

* [#12363](https://github.com/leanprover/lean4/pull/12363) introduces iterators for vectors via `Vector.iter` and
  `Vector.iterM`, together with the usual lemmas.

* [#12371](https://github.com/leanprover/lean4/pull/12371) adds lemmas for simplifying situations involving `Bool` and
  `ite`/`dite`.

* [#12412](https://github.com/leanprover/lean4/pull/12412) introduces `Rat.abs` and adds missing lemmas about `Int` and
  `Rat`.

* [#12419](https://github.com/leanprover/lean4/pull/12419) adds `LawfulOrderOrd` instances for `Nat`, `Int`, and all
  fixed-width integer types (`Int8`, `Int16`, `Int32`, `Int64`, `ISize`,
  `UInt8`, `UInt16`, `UInt32`, `UInt64`, `USize`). These instances
  establish that the `Ord` instances for these types are compatible with
  their `LE` instances. Additionally, this PR adds a few missing lemmas
  and `grind` patterns.

* [#12424](https://github.com/leanprover/lean4/pull/12424) gives a proof of `LawfulToForwardSearcherModel` for `Slice`
  patterns, which amounts to proving that our implementation of KMP is
  correct.

* [#12426](https://github.com/leanprover/lean4/pull/12426) adds the lemma `Acc.inv_of_transGen`, a generalization of
  `Acc.inv`. While `Acc.inv` shows that `Acc r x` implies `Acc r y` given
  that `r y x`, the new lemma shows that this also holds if `y` is only
  *transitively* related to `x`.

* [#12432](https://github.com/leanprover/lean4/pull/12432) adds the lemmas `isSome_find?` and `isSome_findSome?` to the API
  of lists, arrays and vectors.

* [#12437](https://github.com/leanprover/lean4/pull/12437) verifies the `String.Slice.splitToSubslice` function by relating
  it to a model implementation `Model.split` based on a
  `ForwardPatternModel`.

* [#12438](https://github.com/leanprover/lean4/pull/12438) provides (1) lemmas showing that lists obtained from ranges have
  no duplicates and (2) lemmas about `forIn` and `foldl` on slices.

* [#12442](https://github.com/leanprover/lean4/pull/12442) derives `DecidableEq` instances for the types of ranges such as
  `a...b` (in this case, `Std.Rco`).

* [#12449](https://github.com/leanprover/lean4/pull/12449) marks `String.toString_eq_singleton` as a `simp` lemma.

* [#12450](https://github.com/leanprover/lean4/pull/12450) moves the `String.Slice`/`String` iterators out into their own
  file, in preparation for verification.

* [#12456](https://github.com/leanprover/lean4/pull/12456) verifies all of the `String` iterators except for the bytes
  iterator by relating them to `String.toList`.

* [#12504](https://github.com/leanprover/lean4/pull/12504) makes the `Rat.abs_*` lemmas (`abs_zero`, `abs_nonneg`,
  `abs_of_nonneg`, `abs_of_nonpos`, `abs_neg`, `abs_sub_comm`,
  `abs_eq_zero_iff`, `abs_pos_iff`) protected, so they don't shadow the
  general `abs_*` lemmas when the `Rat` namespace is opened in downstream
  projects.

# Tactics

* [#11744](https://github.com/leanprover/lean4/pull/11744) fixes a bug where `lia` was incorrectly solving goals involving
  ordered types like `Rat` that it shouldn't handle. The `lia` tactic is
  intended for linear integer arithmetic only.

* [#12152](https://github.com/leanprover/lean4/pull/12152) adds `simpArrowTelescope`, a simproc that simplifies telescopes
  of non-dependent arrows (p₁ → p₂ → ... → q) while avoiding quadratic
  proof growth.

* [#12153](https://github.com/leanprover/lean4/pull/12153) improves the `simpArrowTelescope` simproc that simplifies
  non-dependent arrow telescopes: `p₁ → p₂ → ... → q`.

* [#12154](https://github.com/leanprover/lean4/pull/12154) adds `simpTelescope`, a simproc that simplifies telescope
  binders (`have`-expression values and arrow hypotheses) but not the
  final body. This is useful for simplifying targets before introducing
  hypotheses.

* [#12168](https://github.com/leanprover/lean4/pull/12168) adds support for eta-reduction in `SymM`.

* [#12172](https://github.com/leanprover/lean4/pull/12172) fixes how we determine whether a function parameter is an
  instance.
  Previously, we relied on binder annotations (e.g., `[Ring A]` vs `{_ :
  Ring A}`)
  to make this determination. This is unreliable because users
  legitimately use
  `{..}` binders for class types when the instance is already available
  from
  context. For example:
  ```
  structure OrdSet (α : Type) [Hashable α] [BEq α] where
    ...

  def OrdSet.insert {_ : Hashable α} {_ : BEq α} (s : OrdSet α) (a : α) : OrdSet α :=
    ...
  ```

  Here, `Hashable` and `BEq` are classes, but the `{..}` binder is intentional, the
  instances come from `OrdSet`'s parameters, so type class resolution is unnecessary.

  The fix checks the parameter's *type* using `isClass?` rather than its syntax, and
  caches this information in `FunInfo`. This affects several subsystems:
  discrimination trees, congruence lemma generation, and the `grind` canonicalizer.

* [#12176](https://github.com/leanprover/lean4/pull/12176) fixes a bug where delayed E-match theorem instances could cause
  uniqueId collisions in the instance tracking map.

* [#12195](https://github.com/leanprover/lean4/pull/12195) ensures `dsimp` does not "simplify" instances by default. The
  old behavior can be retrieved by using
  ```
  set_option backward.dsimp.instances true
  ```
  Applying `dsimp` to instances creates non-standard instances, and this
  creates all sorts of problems in Mathlib.
  This modification is similar to
  ```
  set_option backward.dsimp.proofs true
  ```

* [#12205](https://github.com/leanprover/lean4/pull/12205) adds `mkBackwardRuleFromExpr` to create backward rules from
  expressions, complementing the existing `mkBackwardRuleFromDecl` which
  only works with declaration names.

* [#12224](https://github.com/leanprover/lean4/pull/12224) fixes a bug where `grind?` suggestions would not include
  parameters using local variable dot notation (e.g.,
  `cs.getD_rightInvSeq` where `cs` is a local variable). These parameters
  were incorrectly filtered out because the code assumed all ident params
  resolve to global declarations. In fact, local variable dot notation
  produces anchors that need the original term to be loaded during replay,
  so they must be preserved in the suggestion.

* [#12244](https://github.com/leanprover/lean4/pull/12244) ensures `simp` does not "simplify" instances by default. The old
  behavior can be retrieved by using `simp +instances`. is similar
  to #12195, but for `dsimp`.
  The backward compatibility flag for `dsimp` also deactivates this new
  feature.

* [#12259](https://github.com/leanprover/lean4/pull/12259) ensures we cache the result of `unfold_definition` definition in
  the kernel type checker. We used to cache this information in a thread
  local storage, but it was deleted during the Lean 3 to Lean 4
  transition.

* [#12260](https://github.com/leanprover/lean4/pull/12260) fixes a bug in the function `instantiateRangeS'` in the `Sym`
  framework.

* [#12279](https://github.com/leanprover/lean4/pull/12279) adds an experimental `cbv` tactic that can be invoked from
  `conv` mode. The tactic is not suitable for production use and an
  appropriate warning is displayed.

* [#12280](https://github.com/leanprover/lean4/pull/12280) adds a benchmark based on Xavier Leroy's compiler verification
  course to test call-by-value tactic.

* [#12287](https://github.com/leanprover/lean4/pull/12287) fixes an issue where `attribute [local simp]` was incorrectly
  rejected on a theorem from a private import

* [#12296](https://github.com/leanprover/lean4/pull/12296) adds `cbv_eval` attribute that allows to evaluate functions in
  `cbv` tactic using pre-registered theorems.

* [#12319](https://github.com/leanprover/lean4/pull/12319) leverages the fact that expressions are type correct in `grind`
  and the conclusion of extensionality theorems is of the form `?a = ?b`.

* [#12345](https://github.com/leanprover/lean4/pull/12345) adds two benchmarks (sieve of Eratosthenes, removing duplicates
  from the list) and one test (a function with sublinear complexity
  defined via well-founded recursion evaluated on large naturals with up
  to `60` digits).

* [#12361](https://github.com/leanprover/lean4/pull/12361) develops custom simprocs for dealing with `ite`/`dite`
  expressions in `cbv` tactics, based on equivalent simprocs from
  `Sym.simp`, with the difference that if the condition is not reduced to
  `True`/`False`, we make use of the decidable instance and calculate to
  what the condition reduces to.

* [#12370](https://github.com/leanprover/lean4/pull/12370) fixes a proof construction bug in `Sym.simp`.

* [#12399](https://github.com/leanprover/lean4/pull/12399) adds a custom simproc to handle `Decidable.rec`, where we force
  the rewrite in the argument of the `Decidable` type, that normally is
  not rewritten due to being a subsingleton.

* [#12406](https://github.com/leanprover/lean4/pull/12406) implements two changes to LRAT checking in `bv_decide`:
  1. The LRAT trimmer previously used to drop delete instructions as we
  did not act upon them in a meaningful way (as explained in 2). Now it
  figures out the earliest point after which a clause may be deleted in
  the trimmed LRAT proof and inserts a deletion there.
  2. The LRAT checker takes in an `Array IntAction` and explodes it into
  an `Array DefaultClauseAction` before passing it into the checking loop.
  `DefaultClauseAction` has a much larger memory footprint compared to
  `IntAction`. Thus materializing the entire proof as
  `DefaultClauseAction` upfront consumes a lot of memory. In the adapted
  LRAT checker we take in an `Array IntAction` and only ever convert the
  step we are currently working on to a `DefaultClauseAction`. In
  combination with the fact that we now insert deletion instructions this
  can drastically reduce memory consumption.

* [#12408](https://github.com/leanprover/lean4/pull/12408) adds a user facing `cbv` tactic that can be used outside of the
  `conv` mode.

* [#12411](https://github.com/leanprover/lean4/pull/12411) adds a finishing `decide_cbv` tactic, which applies
  `of_decide_eq_true` and then tries to discharge the remaining goal using
  `cbv`.

* [#12415](https://github.com/leanprover/lean4/pull/12415) improves the support for eta expanded terms in `grind` patterns.

* [#12417](https://github.com/leanprover/lean4/pull/12417) refactors the main loop of the `cbv` tactic. Rather than using
  multiple simprocs, a central pre simproc is introduced. Moreover, let
  expressions are no longer immediately zeta-reduced due to performance on
  one of the benchmarks (`leroy.lean`).

* [#12423](https://github.com/leanprover/lean4/pull/12423) adds the attribute `@[univ_out_params]` for specifying which
  universe levels should be treated as output parameters. By default, any
  universe level that does not occur in any input parameter is considered
  an output parameter.

* [#12467](https://github.com/leanprover/lean4/pull/12467) adds a benchmark for `cbv` tactic for evaluating
  `Decidable.decide` for a `Decidable` instance for a problem of checking
  if a number is not a prime power.

* [#12473](https://github.com/leanprover/lean4/pull/12473) fixes an assertion violation in `grind` reported at #12246 This
  assertion fails when in examples containing heterogenous equalities with
  elements of different types (e.g., `Fin n` and `Fin m`) attached to the
  same theory solver.

* [#12474](https://github.com/leanprover/lean4/pull/12474) fixes a panic in `grind` where `sreifyCore?` could encounter
  power subterms not yet internalized in the E-graph during nested
  propagation. The ring reifier (`reifyCore?`) already had a defensive
  `alreadyInternalized` check before creating variables, but the semiring
  reifier (`sreifyCore?`) was missing this guard. When `propagatePower`
  decomposed `a ^ (b₁ + b₂)` into `a^b₁ * a^b₂` and the resulting terms
  triggered further propagation, the semiring reifier could be called on
  subterms not yet in the E-graph, causing `markTerm` to fail.

* [#12475](https://github.com/leanprover/lean4/pull/12475) fixes `grind` failing when hypotheses contain metavariables
  (e.g., after `refine`). The root cause was that `abstractMVars` in
  `withProtectedMCtx` only abstracted metavariables in the target, not in
  hypotheses, creating a disconnect in grind's e-graph.

* [#12476](https://github.com/leanprover/lean4/pull/12476) fixes #12245 where `grind` works on `Fin n` but fails on `Fin (n
  + 1)`.

* [#12477](https://github.com/leanprover/lean4/pull/12477) fixes an internal `grind` error where `mkEqProof` is invoked
  with terms of different types. When equivalence classes contain
  heterogeneous equalities (e.g., `0 : Fin 3` and `0 : Fin 2` merged via
  `HEq`), `closeGoalWithValuesEq` would call `mkEqProof` on terms with
  incompatible types, triggering an internal error.

* [#12480](https://github.com/leanprover/lean4/pull/12480) skips the relabeling step during AIG to CNF conversion, reducing
  memory pressure.

* [#12483](https://github.com/leanprover/lean4/pull/12483) adds support for higher-order Miller patterns in `grind`'s
  e-matching engine.

* [#12486](https://github.com/leanprover/lean4/pull/12486) caches `isDefEqI` results in `Sym`. During symbolic computation
  (e.g., VC generators), we find the same instances over and over again.

# Compiler

* [#12052](https://github.com/leanprover/lean4/pull/12052) avoids a potential deadlock on shutdown of a Lean program when
  the number of pooled threads has temporarily been pushed above the
  limit.

* [#12060](https://github.com/leanprover/lean4/pull/12060) strips unneeded symbol names from libleanshared.so on Linux. It
  appears that on other platforms the symbols names we are interested in
  here are already removed by the linker.

* [#12082](https://github.com/leanprover/lean4/pull/12082) makes the compiler produce C code that statically initializes
  close terms when possible. This change reduces startup time as the terms
  are directly stored in the binary instead of getting computed at
  startup.

* [#12117](https://github.com/leanprover/lean4/pull/12117) upgrades Lean's internal toolchain to use C++20 as a preparatory
  step for #12044.

* [#12214](https://github.com/leanprover/lean4/pull/12214) introduces a phase separation to the LCNF IR. This is a
  preparation for the merge of
  the old `Lean.Compiler.IR` and the new `Lean.Compiler.LCNF` framework.

* [#12239](https://github.com/leanprover/lean4/pull/12239) reverts a lot of the changes done in #8308. We practically
  encountered situations such as:
  ```
  fun y (z) :=
    let x := inst
    mkInst x z
  f y
  ```
  Where the instance puller turns it into:
  ```
  let x := inst
  fun y (z) :=
    mkInst x z
  f y
  ```
  The current heuristic now discovers `x` being in scope at the call site
  of `f` and being used under a binder in `y` and thus blocks pulling in
  `x` to the specialization, abstracting over an instance.

* [#12272](https://github.com/leanprover/lean4/pull/12272) shifts the conversion from LCNF mono to lambda pure into the
  LCNF impure phase. This is preparatory work for the upcoming refactor of
  IR into LCNF impure.

* [#12284](https://github.com/leanprover/lean4/pull/12284) changes the handling of over-applied cases expressions in
  `ToLCNF` to avoid generating function declarations that are called
  immediately. For example, `ToLCNF` previously produced this:
  ```
  set_option trace.Compiler.init true
  /--
  trace: [Compiler.init] size: 4
      def test x y : Bool :=
        fun _y.1 _y.2 : Bool :=
          cases x : Bool
          | PUnit.unit =>
            fun _f.3 a : Bool :=
              return a;
            let _x.4 := _f.3 _y.2;
            return _x.4;
        let _x.5 := _y.1 y;
        return _x.5
  -/
  #guard_msgs in
  def test (x : Unit) (y : Bool) : Bool :=
    x.casesOn (fun a => a) y
  ```
  which is now simplified to
  ```
  set_option trace.Compiler.init true
  /--
  trace: [Compiler.init] size: 3
      def test x y : Bool :=
        cases x : Bool
        | PUnit.unit =>
          let a := y;
          return a
  -/
  #guard_msgs in
  def test (x : Unit) (y : Bool) : Bool :=
    x.casesOn (fun a => a) y
  ```
  This is especially relevant for #8309 because there `dite` is defined as
  an over-applied `Bool.casesOn`.

* [#12294](https://github.com/leanprover/lean4/pull/12294) ports the `push_proj` pass from IR to LCNF. Notably it cannot
  delete it from IR yet as the pass is still used later on.

* [#12315](https://github.com/leanprover/lean4/pull/12315) migrates the IR ResetReuse pass to LCNF.

* [#12344](https://github.com/leanprover/lean4/pull/12344) changes the semantics of `inline` annotations in the compiler.
  The behavior of the original `@[inline]` attribute remains the same but
  the function `inline` now comes with a restriction that it can only use
  declarations that are local to the current module. This comes as a
  preparation to pulling the compiler out into a separate process.

* [#12356](https://github.com/leanprover/lean4/pull/12356) moves the IR `elim_dead_vars` pass to LCNF. It cannot delete the
  pass yet as it is still used
  in later IR passes.

* [#12384](https://github.com/leanprover/lean4/pull/12384) ports the IR SimpCase pass to LCNF.

* [#12387](https://github.com/leanprover/lean4/pull/12387) fixes an issue in LCNF simp where it would attempt to act on
  type incorrect `cases`
  statements and look for a branch, otherwise panic. This issue did not
  yet manifest in production as
  various other invariants upheld by LCNF simp help mask it but will start
  to become an issue with the
  upcoming changes.

* [#12413](https://github.com/leanprover/lean4/pull/12413) ports the IR borrow pass to LCNF.

* [#12434](https://github.com/leanprover/lean4/pull/12434) removes the uses of `shared_timed_mutex` that were introduced
  because we were stuck on C++14
  with the `shared_mutex` available from C++17 and above.

* [#12446](https://github.com/leanprover/lean4/pull/12446) adds a simplification rule for `Task.get (Task.pure x) = x` into
  the LCNF simplifier. This
  ensures that we avoid touching the runtime for a `Task` that instantly
  gets destructed anyways.

* [#12458](https://github.com/leanprover/lean4/pull/12458) ports the IR pass for box/unbox insertion to LCNF.

* [#12465](https://github.com/leanprover/lean4/pull/12465) changes the boxed type of `uint64` from `tobject` to `object` to
  allow for more precise reference counting.

* [#12466](https://github.com/leanprover/lean4/pull/12466) handles zero-sized reads on handles correctly by returning an
  empty array before the syscall
  is even attempted.

* [#12472](https://github.com/leanprover/lean4/pull/12472) inlines `mix_hash` from C++ which provides general speedups for
  hash functions.

# Documentation

* [#12157](https://github.com/leanprover/lean4/pull/12157) updates #12137 with a link to the Lean reference manual.

* [#12174](https://github.com/leanprover/lean4/pull/12174) fixes a typo in `ExtractLetsConfig.merge` doc comment.

* [#12253](https://github.com/leanprover/lean4/pull/12253) adds a "Stabilizing output" section to the `#guard_msgs`
  docstring, explaining how to use `pp.mvars.anonymous` and `pp.mvars`
  options to stabilize output containing autogenerated metavariable names
  like `?m.47`.

* [#12271](https://github.com/leanprover/lean4/pull/12271) adds and updates docstrings for syntax (and one for ranges).

* [#12439](https://github.com/leanprover/lean4/pull/12439) improves docstrings for `cbv` and `decide_cbv` tactics

* [#12487](https://github.com/leanprover/lean4/pull/12487) expands the docstring for `@[univ_out_params]` to explain:

  - How universe output parameters affect the typeclass resolution cache
  (they are erased from cache keys, so queries differing only in output
  universes share entries)
  - When a universe parameter should be considered an output (determined
  by inputs) vs. not (part of the question being asked)

# Server

* [#12197](https://github.com/leanprover/lean4/pull/12197) fixes a bug in `System.Uri.fileUriToPath?` where it wouldn't use
  the default Windows path separator in the path it produces.

* [#12332](https://github.com/leanprover/lean4/pull/12332) fixes an issue on new NeoVim versions that would cause the
  language server to display an error when using certain code actions.

# Lake

* [#12113](https://github.com/leanprover/lean4/pull/12113) changes the alters the file format of outputs stored in the
  local Lake cache to include an identifier indicating the service (if
  any) the output came from. This will be used to enable lazily
  downloading artifacts on-demand during builds.

* [#12178](https://github.com/leanprover/lean4/pull/12178) scopes the `simp` attribute on `FamilyOut.fam_eq` to the `Lake`
  namespace. The lemma has a very permissive discrimination tree key
  (`_`), so when `Lake.Util.Family` is transitively imported into
  downstream projects, it causes `simp` to attempt this lemma on every
  goal, leading to timeouts.

* [#12203](https://github.com/leanprover/lean4/pull/12203) changes the way artifacts are transferred from the local Lake
  cache to a local build path. Now, Lake will first attempt to hard link
  the local build path to artifact in the cache. If this fails (e.g.,
  because the cache is on a different file system or drive), it will
  fallback to pre-existing approach of copying the artifact. Lake also now
  marks cache artifacts as read-only to avoid corrupting the cache by
  writing to a hard linked artifact.

* [#12261](https://github.com/leanprover/lean4/pull/12261) fixes a bug in Lake where the facet names printed in unknown
  facet errors would contain the internal facet kind.

* [#12300](https://github.com/leanprover/lean4/pull/12300) makes disabling the artifact cache (e.g., via
  `LAKE_ARTIFACT_CACHE=false` or `enableArtifactCache = false`) now stop
  Lake from fetching from the cache (whereas it previously only stopped
  writing to it).

* [#12377](https://github.com/leanprover/lean4/pull/12377) adds identifying information about a module available to `lean`
  (e.g., its name and package identifier) to the module's dependency
  trace. This ensures modules with different identification have different
  input hashes even if their source files and imports are identical.

* [#12444](https://github.com/leanprover/lean4/pull/12444) adds the Lake CLI command `lake cache clean`, which deletes the
  Lake cache directory.

* [#12461](https://github.com/leanprover/lean4/pull/12461) adds support for manually re-releasing nightlies when a build
  issue or critical fix requires it. When a `workflow_dispatch` triggers
  the nightly release job and a `nightly-YYYY-MM-DD` tag already exists,
  the CI now creates `nightly-YYYY-MM-DD-rev1` (then `-rev2`, etc.)
  instead of silently skipping.

# Other

* [#12351](https://github.com/leanprover/lean4/pull/12351) extends the `@[csimp]` attribute to be correctly tracked by
  `lake shake`

* [#12375](https://github.com/leanprover/lean4/pull/12375) extends shake with tracking of attribute names passed to
  `simp`/`grind`.

* [#12463](https://github.com/leanprover/lean4/pull/12463) fixes two issues discovered during the first test of the revised
  nightly release workflow
  (https://github.com/leanprover/lean4/pull/12461):

  **1. Date logic:** The `workflow_dispatch` path used `date -u +%F`
  (current UTC date) to find the base nightly to revise. If the most
  recent nightly was from yesterday (e.g. `nightly-2026-02-12`) but UTC
  has rolled over to Feb 13, the code would look for `nightly-2026-02-13`,
  not find it, and create a fresh nightly instead of a revision. Now finds
  the latest `nightly-*` tag via `sort -rV` and creates a revision of
  that.
