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

#doc (Manual) "Lean 4.28.0 (2026-02-17)" =>
%%%
tag := "release-v4.28.0"
file := "v4.28.0"
%%%

For this release, 309 changes landed. In addition to the 94 feature additions and 65 fixes listed below there were 19 refactoring changes, 8 documentation improvements, 34 performance improvements, 12 improvements to the test suite and 77 other changes.

# Highlights

The Lean v4.28 release contains module system fixes, performance
improvements, notably in `bv_decide`, and continued expansion of
`grind` annotations across the standard library. The main new features
are presented below.

## Symbolic Simulation Framework

New lightweight symbolic simulation framework integrates with `grind`
and enables the implementation of verification condition generators
and symbolic execution engines.
[#12143](https://github.com/leanprover/lean4/pull/12143) defines the
core API of this framework.

For design notes and implementation details, see:

- [#11788](https://github.com/leanprover/lean4/pull/11788) — intro and
  overview
- [#11825](https://github.com/leanprover/lean4/pull/11825) — efficient
  pattern matching and unification
- [#11837](https://github.com/leanprover/lean4/pull/11837) — goal
  transformation via backward chaining
- [#11860](https://github.com/leanprover/lean4/pull/11860) —
  congruence analysis for efficient subterm rewriting
- [#11884](https://github.com/leanprover/lean4/pull/11884) —
  discrimination tree for fast pattern retrieval
- [#11909](https://github.com/leanprover/lean4/pull/11909) — monad
  hierarchy for symbolic computation
- [#11898](https://github.com/leanprover/lean4/pull/11898),
  [#11967](https://github.com/leanprover/lean4/pull/11967),
  [#11974](https://github.com/leanprover/lean4/pull/11974) —
  optimizations

## User-Defined Grind Attributes

[#11765](https://github.com/leanprover/lean4/pull/11765) implements
user-defined `grind` attributes. They are useful for users that want
to implement tactics using the `grind` infrastructure (e.g.,
`progress*` in Aeneas). New `grind` attributes are declared using the
command

```lean
register_grind_attr my_grind
```

The command is similar to `register_simp_attr`. Recall that similar to
`register_simp_attr`, the new attribute cannot be used in the same
file it is declared.

```
opaque f : Nat → Nat
opaque g : Nat → Nat

@[my_grind] theorem fax : f (f x) = f x := sorry

example theorem fax2 : f (f (f x)) = f x := by
  fail_if_success grind
  grind [my_grind]
```

[#11770](https://github.com/leanprover/lean4/pull/11770) implements
support for user-defined attributes at `grind_pattern`. After
declaring a `grind` attribute with `register_grind_attr my_grind`, one
can write:

```
opaque f : Nat → Nat
opaque g : Nat → Nat
axiom fg : g (f x) = x

grind_pattern [my_grind] fg => g (f x)
```

## Configurable Normalization and Preprocessing in Grind

[#11776](https://github.com/leanprover/lean4/pull/11776) adds the
attributes `[grind norm]` and `[grind unfold]` for controlling the
`grind` normalizer and preprocessor.

The `norm` modifier instructs `grind` to use a theorem as a
normalization rule. That is, the theorem is applied during the
preprocessing step. This feature is meant for advanced users who
understand how the preprocessor and `grind`'s search procedure
interact with each other. New users can still benefit from this
feature by restricting its use to theorems that completely eliminate a
symbol from the goal. Example:

```
theorem max_def : max n m = if n ≤ m then m else n
```

The `unfold` modifier instructs `grind` to unfold the given definition
during the preprocessing step. Example:

```lean
@[grind unfold] def h (x : Nat) := 2 * x
example : 6 ∣ 3*h x := by grind
```

See the PR description for the complete discussion.

## Local Definitions in Grind and Simp

[#11946](https://github.com/leanprover/lean4/pull/11946) adds a
`+locals` configuration option to the `grind` tactic that
automatically adds all definitions from the current file as e-match
theorems. This provides a convenient alternative to manually adding
`[local grind]` attributes to each definition. In the form
`grind? +locals`, it is also helpful for discovering which local
declarations it may be useful to add `[local grind]` attributes to.

[#11947](https://github.com/leanprover/lean4/pull/11947) adds a
`+locals` configuration option to the `simp`, `simp_all`, and `dsimp`
tactics.

## Solver Mode in `bv_decide`

[#11847](https://github.com/leanprover/lean4/pull/11847) adds a new
`solverMode` field to `bv_decide`'s configuration, allowing users to
configure the SAT solver for different kinds of workloads. Solver mode
can be set to:

- `proof`, to improve proof search;
- `counterexample`, to improve counterexample search;
- `default`, where there are no additional SAT solver flags.

## Parallel Tactic Combinator

[#11949](https://github.com/leanprover/lean4/pull/11949) adds a new
`first_par` tactic combinator that runs multiple tactics in parallel
and returns the first successful result (cancelling the others).

The `try?` tactic's `atomicSuggestions` step now uses `first_par` to
try three grind variants in parallel:

- `grind? +suggestions`  ̵ uses library suggestion engine
- `grind? +locals`  ̵ unfolds local definitions from current file
- `grind? +locals +suggestions`  ̵ combines both

## Dependency Management Tools

- [#11726](https://github.com/leanprover/lean4/pull/11726) upstreams
  dependency-management commands from Mathlib:
    - `#import_path Foo` prints the transitive import chain that
      brings `Foo` into scope
    - `assert_not_exists Foo` errors if declaration `Foo` exists (for
      dependency management)
    - `assert_not_imported Module` warns if `Module` is transitively
      imported
    - `#check_assertions` verifies all pending assertions are
      eventually satisfied

- [#11921](https://github.com/leanprover/lean4/pull/11921) adds
  `lake shake` as a built-in Lake command, moving the shake
  functionality from `script/Shake.lean` into the Lake CLI.

## External Checker

[#11887](https://github.com/leanprover/lean4/pull/11887) makes the
external checker lean4checker available as the existing `leanchecker`
binary already known to elan, allowing for out-of-the-box access to
it.

Project repository: https://github.com/leanprover/lean4checker

## Library Highlights

### Ranges

- [#11438](https://github.com/leanprover/lean4/pull/11438) renames the
  namespace `Std.Range` to `Std.Legacy.Range`. Instead of using
  `Std.Range` and `[a:b]` notation, the new range type `Std.Rco` and
  its corresponding `a...b` notation should be used.

### Iterators

- [#11446](https://github.com/leanprover/lean4/pull/11446) moves many
  constants of the iterator API from `Std.Iterators` to the `Std`
  namespace in order to make them more convenient to use. These
  constants include, but are not limited to, `Iter`, `IterM` and
  `IteratorLoop`. This is a *breaking change*. If something breaks,
  try adding `open Std` in order to make these constants available
  again. If some constants in the `Std.Iterators` namespace cannot be
  found, they can be found directly in `Std` now.

- [#11789](https://github.com/leanprover/lean4/pull/11789) makes the
  `FinitenessRelation` structure, which is helpful when proving the
  finiteness of iterators, part of the public API.

### Bitvectors

- [#11257](https://github.com/leanprover/lean4/pull/11257) adds the
  definition of `BitVec.cpop`, aka popcount.

- [#11767](https://github.com/leanprover/lean4/pull/11767) introduces
  two induction principles for bitvectors, based on the concat and
  cons operations.

### Async Framework

- [#11499](https://github.com/leanprover/lean4/pull/11499) adds the
  `Context` type for cancellation with context propagation. It works
  by storing a tree of forks of the main context, providing a way to
  control cancellation.

# Language

* [#11553](https://github.com/leanprover/lean4/pull/11553) makes `simpH`, used in the match equation generator, produce a
  proof term. This is in preparation for a bigger refactoring in #11512.

* [#11666](https://github.com/leanprover/lean4/pull/11666) makes sure that when a matcher is compiled using a sparse cases,
  that equation generation also uses sparse cases to split.
  This fixes #11665.

* [#11669](https://github.com/leanprover/lean4/pull/11669) makes sure that proofs about `ctorIdx` passed to `grind` pass
  the `debug.grind` checks, despite reducing a `semireducible` definition.

* [#11670](https://github.com/leanprover/lean4/pull/11670) fixes the `grind` support for `Nat.ctorIdx`. Nat constructors
  appear in `grind` as offsets or literals, and not as a node marked
  `.constr`, so handle that case as well.

* [#11673](https://github.com/leanprover/lean4/pull/11673) fixes an issue where a `by` in the public scope could create an
  auxiliary theorem for the proof whose type does not match the expected
  type in the public scope.

* [#11698](https://github.com/leanprover/lean4/pull/11698) makes `mvcgen` early return after simplifying discriminants,
  avoiding a rewrite on an ill-formed `match`.

* [#11714](https://github.com/leanprover/lean4/pull/11714) gives a focused error message when a user tries to name an
  example, and tweaks error messages for attempts to define multiple
  opaque names at once.

* [#11718](https://github.com/leanprover/lean4/pull/11718) adds a test for issue #11655, which it seems was fixed by #11695

* [#11721](https://github.com/leanprover/lean4/pull/11721) improves the performance of the functions for generating
  congruence lemmas, used by `simp`
  and a few other components.

* [#11726](https://github.com/leanprover/lean4/pull/11726) upstreams dependency-management commands from Mathlib:

  - `#import_path Foo` prints the transitive import chain that brings
  `Foo` into scope
  - `assert_not_exists Foo` errors if declaration `Foo` exists (for
  dependency management)
  - `assert_not_imported Module` warns if `Module` is transitively
  imported
  - `#check_assertions` verifies all pending assertions are eventually
  satisfied

* [#11731](https://github.com/leanprover/lean4/pull/11731) makes the cache in expr_eq_fn use mimalloc for a small
  performance win across the board.

* [#11748](https://github.com/leanprover/lean4/pull/11748) fixes an edge case where some tactics did not allow access to
  private declarations inside private proofs under the module system

* [#11756](https://github.com/leanprover/lean4/pull/11756) fixes an issue where `grind` fails when trying to unfold a
  definition by pattern matching imported by `import all` (or from a
  non-`module`).

* [#11780](https://github.com/leanprover/lean4/pull/11780) ensures that pretty-printing of unification hints inserts a
  space after |- resp. ⊢.

* [#11871](https://github.com/leanprover/lean4/pull/11871) makes `mvcgen with tac` fail if `tac` fails on one of the VCs,
  just as `induction ... with tac` fails if `tac` fails on one of the
  goals. The old behavior can be recovered by writing `mvcgen with try
  tac` instead.

* [#11875](https://github.com/leanprover/lean4/pull/11875) adds the directory `Meta/DiscrTree` and reorganizes the code
  into different files. Motivation: we are going to have new functions for
  retrieving simplification theorems for the new structural simplifier.

* [#11882](https://github.com/leanprover/lean4/pull/11882) adds a guard to `TagDeclarationExtension.tag` to check if the
  declaration name is anonymous and return early if so. This prevents a
  panic that could occur when modifiers like `meta` or `noncomputable` are
  used in combination with syntax errors.

* [#11896](https://github.com/leanprover/lean4/pull/11896) fixes a panic that occurred when a theorem had a docstring on an
  auxiliary definition within a `where` clause.

* [#11908](https://github.com/leanprover/lean4/pull/11908) adds two features to the message testing commands:
  a new `#guard_panic` command that succeeds if the nested command produces
  a panic message (useful for testing commands expected to panic), and a
  `substring := true` option for `#guard_msgs` that checks if the docstring
  appears as a substring of the output rather than requiring an exact match.

* [#11919](https://github.com/leanprover/lean4/pull/11919) improves the error message when `initialize` (or `opaque`) fails
  to find an `Inhabited` or `Nonempty` instance.

* [#11926](https://github.com/leanprover/lean4/pull/11926) adds an `unsafe` modifier to an existing helper function user
  `unsafeEIO`, and also leaves the function private.

* [#11933](https://github.com/leanprover/lean4/pull/11933) adds utility functions for managing the message log during
  tactic
  evaluation, and refactors existing code to use them.

* [#11940](https://github.com/leanprover/lean4/pull/11940) fixes module system visibiltity issues when trying to declare a
  public inductive inside a mutual block.

* [#11991](https://github.com/leanprover/lean4/pull/11991) fixes `declare_syntax_cat` declaring a local category leading to
  import errors when used in `module` without `public section`.

* [#12026](https://github.com/leanprover/lean4/pull/12026) fixes an issue where attributes like `@[irreducible]` would not
  be allowed under the module system unless combined with `@[exposed]`,
  but the former may be helpful without the latter to ensure downstream
  non-`module`s are also affected.

* [#12045](https://github.com/leanprover/lean4/pull/12045) disables the `import all` check across package boundaries. Now
  any module can `import all` any other module.

* [#12048](https://github.com/leanprover/lean4/pull/12048) fixes a bug where `mvcgen` loses VCs, resulting in unassigned
  metavariables. It is fixed by making all emitted VCs synthetic opaque.

* [#12122](https://github.com/leanprover/lean4/pull/12122) adds support for Verso docstrings in `where` clauses.

* [#12148](https://github.com/leanprover/lean4/pull/12148) reverts #12000, which introduced a regression where `simp`
  incorrectly rejects valid rewrites for perm lemmas.

# Library

* [#11257](https://github.com/leanprover/lean4/pull/11257) adds the definition of `BitVec.cpop`, which relies on the more
  general `BitVec.cpopNatRec`, and build some theory around it. The name
  `cpop` aligns with the [RISCV ISA
  nomenclature](https://msyksphinz-self.github.io/riscv-isadoc/#_cpop).

* [#11438](https://github.com/leanprover/lean4/pull/11438) renames the namespace `Std.Range` to `Std.Legacy.Range`. Instead
  of using `Std.Range` and `[a:b]` notation, the new range type `Std.Rco`
  and its corresponding `a...b` notation should be used. There are also
  other ranges with open/closed/infinite boundary shapes in
  `Std.Data.Range.Polymorphic` and the new range notation also works for
  `Int`, `Int8`, `UInt8`, `Fin` etc.

* [#11446](https://github.com/leanprover/lean4/pull/11446) moves many constants of the iterator API from `Std.Iterators` to
  the `Std` namespace in order to make them more convenient to use. These
  constants include, but are not limited to, `Iter`, `IterM` and
  `IteratorLoop`. This is a breaking change. If something breaks, try
  adding `open Std` in order to make these constants available again. If
  some constants in the `Std.Iterators` namespace cannot be found, they
  can be found directly in `Std` now.

* [#11499](https://github.com/leanprover/lean4/pull/11499) adds the `Context` type for cancellation with context
  propagation. It works by storing a tree of forks of the main context,
  providing a way to control cancellation.

* [#11532](https://github.com/leanprover/lean4/pull/11532) adds the new operation `MonadAttach.attach` that attaches a
  proof that a postcondition holds to the return value of a monadic
  operation. Most non-CPS monads in the standard library support this
  operation in a nontrivial way. The PR also changes the `filterMapM`,
  `mapM` and `flatMapM` combinators so that they attach postconditions to
  the user-provided monadic functions passed to them. This makes it
  possible to prove termination for some of these for which it wasn't
  possible before. Additionally, the PR adds many missing lemmas about
  `filterMap(M)` and `map(M)` that were needed in the course of this PR.

* [#11693](https://github.com/leanprover/lean4/pull/11693) makes it possible to verify loops over iterators. It provides
  MPL spec lemmas about `for` loops over pure iterators. It also provides
  spec lemmas that rewrite loops over `mapM`, `filterMapM` or `filterM`
  iterator combinators into loops over their base iterator.

* [#11705](https://github.com/leanprover/lean4/pull/11705) provides many lemmas about `Int` ranges, in analogy to those
  about `Nat` ranges. A few necessary basic `Int` lemmas are added. The PR
  also removes `simp` annotations on `Rcc.toList_eq_toList_rco`,
  `Nat.toList_rcc_eq_toList_rco` and consorts.

* [#11706](https://github.com/leanprover/lean4/pull/11706) removes the `IteratorCollect` type class and hereby simplifies
  the iterator API. Its limited advantages did not justify the complexity
  cost.

* [#11710](https://github.com/leanprover/lean4/pull/11710) extends the get-elem tactic for ranges so that it supports
  subarrays. Example:
  ```
  example {a : Array Nat} (h : a.size = 28) : Id Unit := do
    let mut x := 0
    for h : i in *...(3 : Nat) do
      x := a[1...4][i]
  ```

* [#11716](https://github.com/leanprover/lean4/pull/11716) adds more MPL spec lemmas for all combinations of `for` loops,
  `fold(M)` and the `filter(M)/filterMap(M)/map(M)` iterator combinators.
  These kinds of loops over these combinators (e.g. `it.mapM`) are first
  transformed into loops over their base iterators (`it`), and if the base
  iterator is of type `Iter _` or `IterM Id _`, then another spec lemma
  exists for proving Hoare triples about it using an invariant and the
  underlying list (`it.toList`). The PR also fixes a bug that MPL always
  assigns the default priority to spec lemmas if `Std.Tactic.Do.Syntax` is
  not imported and a bug that low-priority lemmas are preferred about
  high-priority ones.

* [#11724](https://github.com/leanprover/lean4/pull/11724) adds more `event_loop_lock`s to fix race conditions.

* [#11728](https://github.com/leanprover/lean4/pull/11728) introduces some additional lemmas around `BitVec.extractLsb'`
  and `BitVec.extractLsb`.

* [#11760](https://github.com/leanprover/lean4/pull/11760) allows `grind` to use `List.eq_nil_of_length_eq_zero` (and
  `Array.eq_empty_of_size_eq_zero`), but only when it has already proved
  the length is zero.

* [#11761](https://github.com/leanprover/lean4/pull/11761) adds some `grind_pattern` `guard` conditions to potentially
  expensive theorems.

* [#11762](https://github.com/leanprover/lean4/pull/11762) moves the grind pattern from `Sublist.eq_of_length` to the
  slightly more general `Sublist.eq_of_length_le`, and adds a grind
  pattern guard so it only activates if we have a proof of the hypothesis.

* [#11767](https://github.com/leanprover/lean4/pull/11767) introduces two induction principles for bitvectors, based on the
  concat and cons operations. We show how this principle can be useful to
  reason about bitvectors by refactoring two population count lemmas
  (`cpopNatRec_zero_le` and `toNat_cpop_append`) and introducing a new
  lemma (`toNat_cpop_not`).
  To use the induction principle we also move `cpopNatRec_cons_of_le` and
  `cpopNatRec_cons_of_lt` earlier in the popcount section (they are the
  building blocks enabling us to take advantage of the new induction
  principle).

* [#11772](https://github.com/leanprover/lean4/pull/11772) fixes a bug in the optimized and unsafe implementation of
  `Array.foldlM`.

* [#11774](https://github.com/leanprover/lean4/pull/11774) fixes a mismatch between the behavior of `foldlM` and
  `foldlMUnsafe` in the three array
  types. This mismatch is only exposed when manually specifying a `stop`
  value greater than the size
  of the array and only exploitable through `native_decide`.

* [#11779](https://github.com/leanprover/lean4/pull/11779) fixes an oversight in the initial #11772 PR.

* [#11784](https://github.com/leanprover/lean4/pull/11784) just adds an optional start position argument to
  `PersistentArray.forM`

* [#11789](https://github.com/leanprover/lean4/pull/11789) makes the `FinitenessRelation` structure, which is helpful when
  proving the finiteness of iterators, part of the public API. Previously,
  it was marked internal and experimental.

* [#11794](https://github.com/leanprover/lean4/pull/11794) implements the function `getMaxFVar?` for implementing `SymM`
  primitives.

* [#11834](https://github.com/leanprover/lean4/pull/11834) adds `num?` parameter to `mkPatternFromTheorem` to control how
  many leading quantifiers are stripped when creating a pattern. This
  enables matching theorems where only some quantifiers should be
  converted to pattern variables.

* [#11848](https://github.com/leanprover/lean4/pull/11848) fixes a bug at `Name.beq` reported by
  gasstationcodemanager@gmail.com

* [#11852](https://github.com/leanprover/lean4/pull/11852) changes the definition of the iterator combinators `takeWhileM`
  and `dropWhileM` so that they use `MonadAttach`. This is only relevant
  in rare cases, but makes it sometimes possible to prove such combinators
  finite when the finiteness depends on properties of the monadic
  predicate.

* [#11901](https://github.com/leanprover/lean4/pull/11901) adds `gcd_left_comm` lemmas for both `Nat` and `Int`:

  - `Nat.gcd_left_comm`: `gcd m (gcd n k) = gcd n (gcd m k)`
  - `Int.gcd_left_comm`: `gcd a (gcd b c) = gcd b (gcd a c)`

* [#11905](https://github.com/leanprover/lean4/pull/11905) provides a `Decidable` instance for `Nat.isPowerOfTwo` based on
  the formula `(n ≠ 0) ∧ (n &&& (n - 1)) = 0`.

* [#11907](https://github.com/leanprover/lean4/pull/11907) implements `PersistentHashMap.findKeyD` and
  `PersistentHashSet.findD`. The motivation is avoid two memory
  allocations (`Prod.mk` and `Option.some`) when the collections contains
  the key.

* [#11945](https://github.com/leanprover/lean4/pull/11945) changes the runtime implementation of the `Decidable (xs = #[])`
  and `Decidable (#[] = xs)` instances to use `Array.isEmpty`. Previously,
  `decide (xs = #[])` would first convert `xs` into a list and then
  compare it against `List.nil`.

* [#11979](https://github.com/leanprover/lean4/pull/11979) adds `suggest_for` annotations such that `Int*.toNatClamp` is
  suggested for `Int*.toNat`.

* [#11989](https://github.com/leanprover/lean4/pull/11989) removes a leftover `example` from
  `src/Std/Tactic/BVDecide/Bitblast/BVExpr/Circuit/Lemmas/Operations/Clz.lean`.

* [#11993](https://github.com/leanprover/lean4/pull/11993) adds `grind` annotations to the lemmas about `Subarray` and
  `ListSlice`.

* [#12058](https://github.com/leanprover/lean4/pull/12058) implements iteration over ranges for `Fin` and `Char`.

* [#12139](https://github.com/leanprover/lean4/pull/12139) adds `«term_⁻¹»` to the `recommended_spelling` for `inv`,
  matching
  the pattern used by all other operators which include both the function
  and the syntax in their spelling lists.

# Tactics

* [#11664](https://github.com/leanprover/lean4/pull/11664) adds support for `Nat.cast` in `grind linarith`. It now uses
  `Grind.OrderedRing.natCast_nonneg`. Example:
  ```
  open Lean Grind Std
  attribute [instance] Semiring.natCast

  variable [Lean.Grind.CommRing R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

  example (a : Nat) : 0 ≤ (a : R) := by grind
  example (a b : Nat) : 0 ≤ (a : R) + (b : R) := by grind
  ```

* [#11677](https://github.com/leanprover/lean4/pull/11677) adds basic support for equality propagation in `grind linarith`
  for the `IntModule` case. This covers only the basic case. See note in
  the code.
  We remark this feature is irrelevant for `CommRing` since `grind ring`
  already has much better support for equality propagation.

* [#11678](https://github.com/leanprover/lean4/pull/11678) fixes a bug in `registerNonlinearOccsAt` used to implement
  `grind lia`. This issue was originally reported at:
  https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Weirdness.20with.20cutsat/near/562099515

* [#11691](https://github.com/leanprover/lean4/pull/11691) fixes `grind` to support dot notation on declarations in the
  lemma list.

* [#11700](https://github.com/leanprover/lean4/pull/11700) adds a link to the `grind` docstring. The link directs users to
  the section describing `grind` in the reference manual.

* [#11712](https://github.com/leanprover/lean4/pull/11712) avoids invoking TC synthesis and other inference mechanisms in
  the simprocs of `bv_decide`. This can give significant speedups on
  problems that pressure these simprocs.

* [#11717](https://github.com/leanprover/lean4/pull/11717) improves the performance of `bv_decide`'s rewriter on large
  problems.

* [#11736](https://github.com/leanprover/lean4/pull/11736) fixes an issue where `exact?` would not suggest private
  declarations defined in the current module.

* [#11739](https://github.com/leanprover/lean4/pull/11739) turns even more commonly used `bv_decide` theorems that require
  unification into fast simprocs
  using syntactic equality. This pushes the overall performance across
  sage/app7 to <= 1min10s for
  every problem.

* [#11749](https://github.com/leanprover/lean4/pull/11749) fixes a bug in the function `selectNextSplit?` used in `grind`.
  It was incorrectly computing the generation of each candidate.

* [#11758](https://github.com/leanprover/lean4/pull/11758) improves support for nonstandard `Int`/`Nat` instances in
  `grind` and `simp +arith`.

* [#11765](https://github.com/leanprover/lean4/pull/11765) implements user-defined `grind` attributes. They are useful for
  users that want to implement tactics using the `grind` infrastructure
  (e.g., `progress*` in Aeneas). New `grind` attributes are declared using
  the command
  ```
  register_grind_attr my_grind
  ```
  The command is similar to `register_simp_attr`. Recall that similar to
  `register_simp_attr`, the new attribute cannot be used in the same file
  it is declared.
  ```
  opaque f : Nat → Nat
  opaque g : Nat → Nat

  @[my_grind] theorem fax : f (f x) = f x := sorry

  example theorem fax2 : f (f (f x)) = f x := by
    fail_if_success grind
    grind [my_grind]
  ```

* [#11769](https://github.com/leanprover/lean4/pull/11769) uses the new support for user-defined `grind` attributes to
  implement the default `[grind]` attribute.

* [#11770](https://github.com/leanprover/lean4/pull/11770) implements support for user-defined attributes at
  `grind_pattern`. After declaring a `grind` attribute with
  `register_grind_attr my_grind`, one can write:
  ```
  grind_pattern [my_grind] fg => g (f x)
  ```

* [#11776](https://github.com/leanprover/lean4/pull/11776) adds the attributes `[grind norm]` and `[grind unfold]` for
  controlling the `grind` normalizer/preprocessor.

* [#11785](https://github.com/leanprover/lean4/pull/11785) disables closed term extraction in the reflection terms used by
  `bv_decide`. These terms do
  not profit at all from closed term extraction but can in practice cause
  thousands of new closed term
  declarations which in turn slows down the compiler.

* [#11787](https://github.com/leanprover/lean4/pull/11787) adds support for incrementally processing local declarations in
  `grind`. Instead of processing all hypotheses at once during goal
  initialization, `grind` now tracks which local declarations have been
  processed via `Goal.nextDeclIdx` and provides APIs to process new
  hypotheses incrementally.
  This feature will be used by the new `SymM` monad for efficient symbolic
  simulation.

* [#11788](https://github.com/leanprover/lean4/pull/11788) introduces `SymM`, a new monad for implementing symbolic
  simulators (e.g., verification condition generators) in Lean. The monad
  addresses performance issues found in symbolic simulators built on top
  of user-facing tactics like `apply` and `intros`.

* [#11792](https://github.com/leanprover/lean4/pull/11792) adds `isDebugEnabled` for checking whether `grind.debug` is set
  to `true` when `grind` was initialized.

* [#11793](https://github.com/leanprover/lean4/pull/11793) adds functions for creating maximally shared terms from
  maximally shared terms. It is more efficient than creating an expression
  and then invoking `shareCommon`. We are going to use these functions for
  implementing the symbolic simulation primitives.

* [#11797](https://github.com/leanprover/lean4/pull/11797) simplifies `AlphaShareCommon.State` by separating the persistent
  and transient parts of the state.

* [#11800](https://github.com/leanprover/lean4/pull/11800) adds the function `Sym.replaceS`, which is similar to
  `replace_fn` available in the kernel but assumes the input is maximally
  shared and ensures the output is also maximally shared. The PR also
  generalizes the `AlphaShareBuilder` API.

* [#11802](https://github.com/leanprover/lean4/pull/11802) adds the function `Sym.instantiateS` and its variants, which are
  similar to `Expr.instantiate` but assumes the input is maximally shared
  and ensures the output is also maximally shared.

* [#11803](https://github.com/leanprover/lean4/pull/11803) implements `intro` (and its variants) for `SymM`. These versions
  do not use reduction or infer types, and ensure expressions are
  maximally shared.

* [#11806](https://github.com/leanprover/lean4/pull/11806) refactors the `Goal` type used in `grind`. The new
  representation allows multiple goals with different metavariables to
  share the same `GoalState`. This is useful for automation such as
  symbolic simulator, where applying theorems create multiple goals that
  inherit the same E-graph, congruence closure and solvers state, and
  other accumulated facts.

* [#11810](https://github.com/leanprover/lean4/pull/11810) adds a new transparency mode `.none` in which no definitions are
  unfolded.

* [#11813](https://github.com/leanprover/lean4/pull/11813) introduces a fast pattern matching and unification module for
  the symbolic simulation framework (`Sym`). The design prioritizes
  performance by using a two-phase approach:

  *Phase 1 (Syntactic Matching)*
  - Patterns use de Bruijn indices for expression variables and renamed
  level params (`_uvar.0`, `_uvar.1`, ...) for universe variables
  - Matching is purely structural after reducible definitions are unfolded
  during preprocessing
  - Universe levels treat `max` and `imax` as uninterpreted functions (no
  AC reasoning)
  - Binders and term metavariables are deferred to Phase 2

  *Phase 2 (Pending Constraints)*
  - Handles binders (Miller patterns) and metavariable unification
  - Converts remaining de Bruijn variables to metavariables
  - Falls back to `isDefEq` when necessary

* [#11814](https://github.com/leanprover/lean4/pull/11814) implements `instantiateRevBetaS`, which is similar to
  `instantiateRevS` but beta-reduces nested applications whose function
  becomes a lambda after substitution.

* [#11815](https://github.com/leanprover/lean4/pull/11815) optimizes pattern matching by skipping proof and instance
  arguments during Phase 1 (syntactic matching).

* [#11819](https://github.com/leanprover/lean4/pull/11819) adds some basic infrastructure for a structural (and cheaper)
  `isDefEq` predicate for pattern matching and unification in `Sym`.

* [#11820](https://github.com/leanprover/lean4/pull/11820) adds optimized `abstractFVars` and `abstractFVarsRange` for
  converting free variables to de Bruijn indices during pattern
  matching/unification.

* [#11824](https://github.com/leanprover/lean4/pull/11824) implements `isDefEqS`, a lightweight structural definitional
  equality for the symbolic simulation framework. Unlike the full
  `isDefEq`, it avoids expensive operations while still supporting Miller
  pattern unification.

* [#11825](https://github.com/leanprover/lean4/pull/11825) completes the new pattern matching and unification procedures
  for the symbolic simulation framework using a two-phase approach.

* [#11833](https://github.com/leanprover/lean4/pull/11833) fixes a few typos, adds missing docstrings, and adds a (simple)
  missing optimization.

* [#11837](https://github.com/leanprover/lean4/pull/11837) adds `BackwardRule` for efficient goal transformation via
  backward chaining in `SymM`.

* [#11847](https://github.com/leanprover/lean4/pull/11847) adds a new `solverMode` field to `bv_decide`'s configuration,
  allowing users to configure
  the SAT solver for different kinds of workloads.

* [#11849](https://github.com/leanprover/lean4/pull/11849) fixes missing zetaDelta support at the pattern
  matching/unification procedure in the new Sym framework.

* [#11850](https://github.com/leanprover/lean4/pull/11850) fixes a bug in the new pattern matching procedure for the Sym
  framework. It was not correctly handling assigned metavariables during
  pattern matching.

* [#11851](https://github.com/leanprover/lean4/pull/11851) fixes `Sym/Intro.lean` support for `have`-declarations.

* [#11856](https://github.com/leanprover/lean4/pull/11856) adds the basic infrastructure for the structural simplifier used
  by the symbolic simulation (`Sym`) framework.

* [#11857](https://github.com/leanprover/lean4/pull/11857) adds an incremental variant of `shareCommon` for expressions
  constructed from already-shared subterms. We use this when an expression
  `e` was produced by a Lean API (e.g., `inferType`, `mkApp4`) that does
  not preserve maximal sharing, but the inputs to that API were already
  maximally shared. Unlike `shareCommon`, this function does not use a
  local `Std.HashMap ExprPtr Expr` to track visited nodes. This is more
  efficient when the number of new (unshared) nodes is small, which is the
  common case when wrapping API calls that build a few constructor nodes
  around shared inputs.

* [#11858](https://github.com/leanprover/lean4/pull/11858) changes `bv_decide`'s heuristic for what kinds of structures to
  split on to also allow
  splitting on structures where the fields have dependently typed widths.
  For example:
  ```
  structure Byte (w : Nat) where
    /-- A two's complement integer value of width `w`. -/
    val : BitVec w
    /-- A per-bit poison mask of width `w`. -/
    poison : BitVec w
  ```
  This is to allow handling situations such as `(x : Byte 8)` where the
  width becomes concrete after
  splitting is done.

* [#11860](https://github.com/leanprover/lean4/pull/11860) adds `CongrInfo` analysis for function applications in the
  symbolic simulator framework. `CongrInfo` determines how to build
  congruence proofs for rewriting subterms efficiently, categorizing
  functions into:

  - `none`: no arguments can be rewritten (e.g., proofs)
  - `fixedPrefix`: common case where implicit/instance arguments form a
  fixed prefix and explicit arguments can be rewritten (e.g., `HAdd.hAdd`,
  `Eq`)
  - `interlaced`: rewritable and non-rewritable arguments alternate (e.g.,
  `HEq`)
  - `congrTheorem`: uses auto-generated congruence theorems for functions
  with dependent proof arguments (e.g., `Array.eraseIdx`)

* [#11866](https://github.com/leanprover/lean4/pull/11866) implements the core simplification loop for the `Sym` framework,
  with efficient congruence-based argument rewriting.

* [#11868](https://github.com/leanprover/lean4/pull/11868) implements `Sym.Simp.Theorem.rewrite?` for rewriting terms using
  equational theorems in `Sym`.

* [#11869](https://github.com/leanprover/lean4/pull/11869) adds configuration flag `Meta.Context.cacheInferType`. You can
  use it to disable the `inferType` cache at `MetaM`. We use this flag to
  implement `SymM` because it has its own cache based on pointer equality.

* [#11878](https://github.com/leanprover/lean4/pull/11878) documents assumptions made by the symbolic simulation framework
  regarding structural matching and definitional equality.

* [#11880](https://github.com/leanprover/lean4/pull/11880) adds a `with_unfolding_none` tactic that sets the transparency
  mode to `.none`, in which no definitions are unfolded. This complements
  the existing `with_unfolding_all` tactic and provides tactic-level
  access to the `TransparencyMode.none` added in
  https://github.com/leanprover/lean4/pull/11810.

* [#11881](https://github.com/leanprover/lean4/pull/11881) fixes an issue where `grind` failed to prove `f ≠ 0` from `f * r
  ≠ 0` when using `Lean.Grind.CommSemiring`, but succeeded with
  `Lean.Grind.Semiring`.

* [#11884](https://github.com/leanprover/lean4/pull/11884) adds discrimination tree support for the symbolic simulation
  framework.
  The new `DiscrTree.lean` module converts `Pattern` values into
  discrimination
  tree keys, treating proof/instance arguments and pattern variables as
  wildcards
  (`Key.star`). Motivation: efficient pattern retrieval during rewriting.

* [#11886](https://github.com/leanprover/lean4/pull/11886) adds `getMatch` and `getMatchWithExtra` for retrieving patterns
  from
  discrimination trees in the symbolic simulation framework.
  The PR also adds uses `DiscrTree` to implement indexing in `Sym.simp`.

* [#11888](https://github.com/leanprover/lean4/pull/11888) refactors `Sym.simp` to make it more general and customizable.
  It also moves the code
  to its own subdirectory `Meta/Sym/Simp`.

* [#11889](https://github.com/leanprover/lean4/pull/11889) improves the discrimination tree retrieval performance used by
  `Sym.simp`.

* [#11890](https://github.com/leanprover/lean4/pull/11890) ensures that `Sym.simp` checks thresholds for maximum recursion
  depth and maximum number of steps. It also invokes `checkSystem`.
  Additionally, this PR simplifies the main loop. Assigned metavariables
  and `zetaDelta` reduction are now handled by installing `pre`/`post`
  methods.

* [#11892](https://github.com/leanprover/lean4/pull/11892) optimizes the construction on congruence proofs in `simp`.
  It uses some of the ideas used in `Sym.simp`.

* [#11898](https://github.com/leanprover/lean4/pull/11898) adds support for simplifying lambda expressions in `Sym.simp`.
  It is much more efficient than standard simp for very large lambda
  expressions with many binders. The key idea is to generate a custom
  function extensionality theorem for the type of the lambda being
  simplified.

* [#11900](https://github.com/leanprover/lean4/pull/11900) adds a `done` flag to the result returned by `Simproc`s in
  `Sym.simp`.

* [#11906](https://github.com/leanprover/lean4/pull/11906) tries to minimize the number of expressions created at
  `AlphaShareCommon`.

* [#11909](https://github.com/leanprover/lean4/pull/11909) reorganizes the monad hierarchy for symbolic computation in
  Lean.

* [#11911](https://github.com/leanprover/lean4/pull/11911) minimizes the number of expression allocations performed by
  `replaceS` and `instantiateRevBetaS`.

* [#11914](https://github.com/leanprover/lean4/pull/11914) factors out the `have`-telescope support used in `simp`, and
  implements it using the `MonadSimp` interface. The goal is to
  use this nice infrastructure for both `Meta.simp` and `Sym.simp`.

* [#11918](https://github.com/leanprover/lean4/pull/11918) filters deprecated lemmas from `exact?` and `rw?` suggestions.

* [#11920](https://github.com/leanprover/lean4/pull/11920) implements support for simplifying `have` telescopes in
  `Sym.simp`.

* [#11923](https://github.com/leanprover/lean4/pull/11923) adds a new option to the function `simpHaveTelescope` in which
  the `have` telescope is simplified in two passes:

  * In the first pass, only the values and the body are simplified.
  * In the second pass, unused declarations are eliminated.

* [#11932](https://github.com/leanprover/lean4/pull/11932) eliminates super-linear kernel type checking overhead when
  simplifying lambda expressions. I improved the proof term produced by
  `mkFunext`. This function is used in `Sym.simp` when simplifying lambda
  expressions.

* [#11946](https://github.com/leanprover/lean4/pull/11946) adds a `+locals` configuration option to the `grind` tactic that
  automatically adds all definitions from the current file as e-match
  theorems. This provides a convenient alternative to manually adding
  `[local grind]` attributes to each definition. In the form `grind?
  +locals`, it is also helpful for discovering which local declarations it
  may be useful to add `[local grind]` attributes to.

* [#11947](https://github.com/leanprover/lean4/pull/11947) adds a `+locals` configuration option to the `simp`, `simp_all`,
  and `dsimp` tactics that automatically adds all definitions from the
  current file to unfold.

* [#11949](https://github.com/leanprover/lean4/pull/11949) adds a new `first_par` tactic combinator that runs multiple
  tactics in parallel and returns the first successful result (cancelling
  the others).

* [#11950](https://github.com/leanprover/lean4/pull/11950) implements `simpForall` and `simpArrow` in `Sym.simp`.

* [#11962](https://github.com/leanprover/lean4/pull/11962) fixes library suggestions to include private proof-valued
  structure fields.

* [#11967](https://github.com/leanprover/lean4/pull/11967) implements a new strategy for simplifying `have`-telescopes in
  `Sym.simp` that achieves linear kernel type-checking time instead of
  quadratic.

* [#11974](https://github.com/leanprover/lean4/pull/11974) optimizes congruence proof construction in `Sym.simp` by
  avoiding
  `inferType` calls on expressions that are less likely to be cached.
  Instead of
  inferring types of expressions like `@HAdd.hAdd Nat Nat Nat instAdd 5`,
  we infer
  the type of the function prefix `@HAdd.hAdd Nat Nat Nat instAdd` and
  traverse
  the forall telescope.

* [#11976](https://github.com/leanprover/lean4/pull/11976) adds missing type checking for pattern variables during pattern
  matching/unification to prevent incorrect matches.

* [#11985](https://github.com/leanprover/lean4/pull/11985) implements support for auto-generated congruence theorems in
  `Sym.simp`, enabling simplification of functions with complex argument
  dependencies such as proof arguments and `Decidable` instances.

* [#11999](https://github.com/leanprover/lean4/pull/11999) adds support for simplifying the arguments of over-applied and
  under-applied function application terms in `Sym.simp`, completing the
  implementation for all three congruence strategies (fixed prefix,
  interlaced, and congruence theorems).

* [#12006](https://github.com/leanprover/lean4/pull/12006) fixes the pretty-printing of the `extract_lets` tactic.
  Previously, the pretty-printer would expect a space after the
  `extract_lets` tactic, when it was followed by another tactic on the
  same line: for example,
  `extract_lets; exact foo`
  would be changed to
  `extract_lets ; exact foo`.

* [#12012](https://github.com/leanprover/lean4/pull/12012) implements support for rewrite on over-applied terms in
  `Sym.simp`. Example: rewriting `id f a` using `id_eq`.

* [#12031](https://github.com/leanprover/lean4/pull/12031) adds `Sym.Simp.evalGround`, a simplification procedure for
  evaluating ground terms of builtin numeric types. It is designed for
  `Sym.simp`.

* [#12032](https://github.com/leanprover/lean4/pull/12032) adds `Discharger`s to `Sym.simp`, and ensures the cached results
  are consistent.

* [#12033](https://github.com/leanprover/lean4/pull/12033) adds support for conditional rewriting rules to `Sym.simp`.

* [#12035](https://github.com/leanprover/lean4/pull/12035) adds `simpControl`, a simproc that handles control-flow
  expressions such as `if-then-else`. It simplifies conditions while
  avoiding unnecessary work on branches that won't be taken.

* [#12039](https://github.com/leanprover/lean4/pull/12039) implements `match`-expression simplification for `Sym.simp`.

* [#12040](https://github.com/leanprover/lean4/pull/12040) adds simprocs for simplifying `cond` and dependent
  `if-then-else` in `Sym.simp`.

* [#12053](https://github.com/leanprover/lean4/pull/12053) adds support for offset terms in `SymM`. This is essential for
  handling equational theorems for functions that pattern match on natural
  numbers in `Sym.simp`. Without this, it cannot handle simple examples
  such as `pw (a + 2)` where `pw` pattern matches on `n+1`.

* [#12077](https://github.com/leanprover/lean4/pull/12077) implements simprocs for `String` and `Char`. It also ensures
  reducible definitions are unfolded in `SymM`

* [#12096](https://github.com/leanprover/lean4/pull/12096) cleanups temporary metavariables generated when applying
  rewriting rules in `Sym.simp`.

* [#12099](https://github.com/leanprover/lean4/pull/12099) ensures `Sym.simpGoal` does not use `mkAppM`. It also increases
  the default number of maximum steps in `Sym.simp`.

* [#12100](https://github.com/leanprover/lean4/pull/12100) adds a comparison between `MetaM` and `SymM` for a benchmark was
  proposed during the Lean@Google Hackathon.

* [#12101](https://github.com/leanprover/lean4/pull/12101) improves the the `Sym.simp` APIs. It is now easier to reuse the
  simplifier cache between different simplification steps. We use the APIs
  to improve the benchmark at #12100.

* [#12134](https://github.com/leanprover/lean4/pull/12134) adds a new benchmark `shallow_add_sub_cancel.lean` that
  demonstrates symbolic simulation using a shallow embedding into monadic
  `do` notation, as opposed to the deep embedding approach in
  `add_sub_cancel.lean`.

* [#12143](https://github.com/leanprover/lean4/pull/12143) adds an API for building symbolic simulation engines and
  verification
  condition generators that leverage `grind`. The API wraps `Sym`
  operations to
  work with `grind`'s `Goal` type, enabling lightweight symbolic execution
  while
  carrying `grind` state for discharge steps.

* [#12145](https://github.com/leanprover/lean4/pull/12145) moves the pre-shared commonly used expressions from `GrindM` to
  `SymM`.

* [#12147](https://github.com/leanprover/lean4/pull/12147) adds a new API for helping users write focused rewrites.

# Compiler

* [#11479](https://github.com/leanprover/lean4/pull/11479) enables the specializer to also recursively specialize in some
  non trivial higher order situations.

* [#11729](https://github.com/leanprover/lean4/pull/11729) internalizes all arguments of Quot.lift during LCNF conversion,
  preventing panics in certain
  non trivial programs that use quotients.

* [#11874](https://github.com/leanprover/lean4/pull/11874) improves the performance of `getLine` by coalescing the locking
  of the underlying `FILE*`.

* [#11916](https://github.com/leanprover/lean4/pull/11916) adds a symbol to the runtime for marking `Array`
  non-linearities. This should allow users to
  spot them more easily in profiles or hunt them down using a debugger.

* [#11983](https://github.com/leanprover/lean4/pull/11983) fixes the `floatLetIn` pass to not move variables in case it
  could break linearity (owned variables being passed with RC 1). This
  mostly improves the situation in the parser which previously had many
  functions that were supposed to be linear in terms of `ParserState` but
  the compiler made them non-linear. For an example of how this affected
  parsers:
  ```
  def optionalFn (p : ParserFn) : ParserFn := fun c s =>
    let iniSz  := s.stackSize
    let iniPos := s.pos
    let s      := p c s
    let s      := if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else s
    s.mkNode nullKind iniSz
  ```
  previously moved the `let iniSz := ...` declaration into the `hasError`
  branch. However, this means that at the point of calling the inner
  parser (`p c s`), the original state `s` needs to have RC>1 because it
  is used later in the `hasError` branch, breaking linearity. This fix
  prevents such moves, keeping `iniSz` before the `p c s` call.

* [#12003](https://github.com/leanprover/lean4/pull/12003) splits up the SCC that the compiler manages into (potentially)
  multiple ones after
  performing lambda lifting. This aids both the closed term extractor and
  the elimDeadBranches pass as
  they are both negatively influenced when more declarations than required
  are within one SCC.

* [#12008](https://github.com/leanprover/lean4/pull/12008) ensures that the LCNF simplifier already constant folds decision
  procedures (`Decidable`
  operations) in the base phase.

* [#12010](https://github.com/leanprover/lean4/pull/12010) fixe a superliniear behavior in the closed subterm extractor.

* [#12123](https://github.com/leanprover/lean4/pull/12123) fixes an issue that may sporadically trigger ASAN to got into a
  deadlock when running a subprocess through the `IO.Process.spawn`
  framework.

# Documentation

* [#11737](https://github.com/leanprover/lean4/pull/11737) replaces `ffi.md` with links to the corresponding sections of
  the manual, so we don't have to keep two documents up to date.

* [#11912](https://github.com/leanprover/lean4/pull/11912) adds missing docstrings for parts of the iterator library, which
  removes warnings and empty content in the manual.

* [#12047](https://github.com/leanprover/lean4/pull/12047) makes the automatic first token detection in tactic docs much
  more robust, in addition to making it work in modules and other contexts
  where builtin tactics are not in the environment. It also adds the
  ability to override the tactic's first token as the user-visible name.

* [#12072](https://github.com/leanprover/lean4/pull/12072) enables tactic completion and docs for the `let rec` tactic,
  which required a stage0 update after #12047.

* [#12093](https://github.com/leanprover/lean4/pull/12093) makes the Verso module docstring API more like the Markdown
  module docstring API, enabling downstream consumers to use them the same
  way.

# Server

* [#11536](https://github.com/leanprover/lean4/pull/11536) corrects the JSON Schema at
  `src/lake/schemas/lakefile-toml-schema.json` to allow the table variant
  of the `require.git` field in `lakefile.toml` as specified in the
  [reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#Lake___Dependency-git).

* [#11630](https://github.com/leanprover/lean4/pull/11630) improves the performance of autocompletion and fuzzy matching by
  introducing an ASCII fast path into one of their core loops and making
  Char.toLower/toUpper more efficient.

* [#12000](https://github.com/leanprover/lean4/pull/12000) fixes an issue where go-to-definition would jump to the wrong
  location in presence of async theorems.

* [#12004](https://github.com/leanprover/lean4/pull/12004) allows 'Go to Definition' to look through reducible definition
  when looking for typeclass instance projections.

* [#12046](https://github.com/leanprover/lean4/pull/12046) fixes a bug where the unknown identifier code actions were
  broken in NeoVim due to the language server not properly setting the
  `data?` field for all code action items that it yields.

* [#12119](https://github.com/leanprover/lean4/pull/12119) fixes the call hierarchy for `where` declarations under the
  module system

# Lake

* [#11683](https://github.com/leanprover/lean4/pull/11683) fixes an inconsistency in the way Lake and Lean view the
  transitivity of a `meta import`. Lake now works as Lean expects and
  includes the meta segment of all transitive imports of a `meta import`
  in its transitive trace.

* [#11859](https://github.com/leanprover/lean4/pull/11859) removes the need to write `.ofNat` for numeric options in
  `lakefile.lean`. Note that `lake translate-config` incorrectly assumed
  this was already legal in earlier revisions.

* [#11921](https://github.com/leanprover/lean4/pull/11921) adds `lake shake` as a built-in Lake command, moving the shake
  functionality from `script/Shake.lean` into the Lake CLI.

* [#12034](https://github.com/leanprover/lean4/pull/12034) changes the default of `enableArtifactCache` to use the
  workspace's `enableArtifactCache` setting if the package is a dependency
  and `LAKE_ARTIFACT_CACHE` is not set. This means that dependencies of a
  project with `enableArtifactCache` set will also, by default, use Lake's
  local artifact cache.

* [#12037](https://github.com/leanprover/lean4/pull/12037) fixes two Lake cache issues: a bug where a failed upload would
  not produce an error and a mistake in the `--wfail` checks of the cache
  commands.

* [#12076](https://github.com/leanprover/lean4/pull/12076) adds additional debugging information to a run of `lake build
  --no-build` via a `.nobuild` trace file. When a build fails due to
  needing a rebuild, Lake emits the new expected trace next as `.nobuild`
  file next to the build's old `.trace`. The inputs recorded in these
  files can then be compared to debug what caused the mismatch.

* [#12086](https://github.com/leanprover/lean4/pull/12086) fixes a bug where a `lake build --no-build` would exit with code
  `3` if the optional job to fetch a GitHub or Reservoir release for a
  package failed (even if nothing else needed rebuilding).

* [#12105](https://github.com/leanprover/lean4/pull/12105) fixes the `lake query` output for targets which produce an
  `Array` or `List` of a value with a custom `QueryText` or `QueryJson`
  instance (e.g., `deps` and `transDeps`).

* [#12112](https://github.com/leanprover/lean4/pull/12112) revives the ability to specify modules in dependencies via the
  basic `+mod` target key.

# Other

* [#11727](https://github.com/leanprover/lean4/pull/11727) adds a Python script that helps find which commit introduced a
  behavior change in Lean. It supports multiple bisection modes and
  automatically downloads CI artifacts when available.

* [#11735](https://github.com/leanprover/lean4/pull/11735) adds a standalone script to download pre-built CI artifacts from
  GitHub Actions. This allows us to quickly switch commits without
  rebuilding.

* [#11887](https://github.com/leanprover/lean4/pull/11887) makes the external checker lean4checker available as the
  existing `leanchecker` binary already known to elan, allowing for
  out-of-the-box access to it.

* [#12121](https://github.com/leanprover/lean4/pull/12121) wraps info trees produced by the `lean` Verso docstring
  codeblock in a context info node.

# Ffi

* [#12098](https://github.com/leanprover/lean4/pull/12098) removes the requirement that libraries compiled against the lean
  headers must use `-fwrapv`.
