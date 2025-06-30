/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.21.0 (2025-06-30)" =>
%%%
tag := "release-v4.21.0"
file := "v4.21.0"
%%%

````markdown
For this release, 295 changes landed. In addition to the 100 feature additions and 83 fixes listed below there were 2 refactoring changes, 4 documentation improvements, 6 performance improvements, 2 improvements to the test suite and 98 other changes.

## Highlights

_'Unknown identifier' code actions_

* [#7665](https://github.com/leanprover/lean4/pull/7665) and [#8180](https://github.com/leanprover/lean4/pull/8180) add
  support for code actions that resolve 'unknown identifier' errors by either importing the missing declaration or by
  changing the identifier to one from the environment.

_New Language Features_

* [#8449](https://github.com/leanprover/lean4/pull/8449) and [#8516](https://github.com/leanprover/lean4/pull/8516)
  upstream and extend the Mathlib `clear_value` tactic. Given a
  local definition `x : T := v`, the tactic `clear_value x` replaces it
  with a hypothesis `x : T`, or throws an error if the goal does not
  depend on the value `v`. The syntax `clear_value (h : x = _)` creates a
  hypothesis `h : x = _` before clearing the value of `x`. Any expression definitionally equal to `x`
  can be used in place of the underscore.
  Furthermore, `clear_value *` clears all values that can be cleared, or throws an
  error if none can be cleared.

* [#8512](https://github.com/leanprover/lean4/pull/8512) adds a `value_of% ident` term that elaborates to the value of
  the local or global constant `ident`. This is useful for creating
  definition hypotheses:
  ```lean
  let x := ... complicated expression ...
  have hx : x = value_of% x := rfl
  ```

* [#8450](https://github.com/leanprover/lean4/pull/8450) adds a feature to the `subst` tactic so that when `x : X := v`
  is a local definition, `subst x` substitutes `v` for `x` in the goal and
  removes `x`. Previously the tactic would throw an error.

* [#8037](https://github.com/leanprover/lean4/pull/8037) introduces a `noConfusionType` construction that’s sub-quadratic
  in size, and reduces faster. The previous `noConfusion` construction with
  two nested `match` statements is quadratic in size and reduction behavior.
  Using some helper definitions, a linear size construction is possible.

* [#8104](https://github.com/leanprover/lean4/pull/8104) makes `fun_induction` and `fun_cases` (try to) unfold the
  function application of interest in the goal. The old behavior can be
  enabled with `set_option tactic.fun_induction.unfolding false`. For
  `fun_cases` this does not work yet when the function’s result type
  depends on one of the arguments, see issue [#8296](https://github.com/leanprover/lean4/issues/8296).

* [#8171](https://github.com/leanprover/lean4/pull/8171) omits cases from functional induction/cases principles that are
  implemented `by contradiction` (or, more generally, `False.elim`,
  `absurd` or `noConfusion). **Breaking change** in the sense that there are
  fewer goals to prove after using functional induction.

* [#8106](https://github.com/leanprover/lean4/pull/8106) adds a `register_linter_set` command for declaring linter sets.
  The `getLinterValue` function now checks if the present linter is
  contained in a set that has been enabled (using the `set_option` command
  or on the command line).

* [#8267](https://github.com/leanprover/lean4/pull/8267) makes `#guard_msgs` to treat `trace` messages separate from
  `info`, `warning` and `error`. It also introduces the ability to say
  `#guard_msgs (pass info)`, like `(drop info)` so far, and also adds
  `(check info)` as the explicit form of `(info)`, for completeness.

_Library Highlights_

* [#8358](https://github.com/leanprover/lean4/pull/8358) introduces a very minimal version of the new iterator library.
  It comes with list iterators and various consumers, namely `toArray`,
  `toList`, `toListRev`, `ForIn`, `fold`, `foldM` and `drain`. All
  consumers also come in a partial variant that can be used without any
  proofs. This limited version of the iterator library generates decent
  code, even with the old code generator.

* [#7352](https://github.com/leanprover/lean4/pull/7352) reworks the `simp` set around the `Id` monad, to not elide or
  unfold `pure` and `Id.run`

* [#8313](https://github.com/leanprover/lean4/pull/8313) changes the definition of `Vector` so it no longer extends
  `Array`. This prevents `Array` API from "leaking through".

_Other Highlights_

* Performance optimizations in `dsimp`:

  - [#6973](https://github.com/leanprover/lean4/pull/6973) stops `dsimp` from visiting proof terms, which should make
  `simp` and `dsimp` more efficient.

  - [#7428](https://github.com/leanprover/lean4/pull/7428) adds a `dsimp` cache to `simp`. Previously each `dsimp` call from
  `simp` started with a fresh cache. As a result, time spent in `simp` while
  compiling Mathlib is reduced by over 45%, giving an overall 8% speedup to
  Mathlib compilation.

* [#8221](https://github.com/leanprover/lean4/pull/8221) adjusts the experimental module system to not export the bodies
  of `def`s unless opted out by the new attribute `@[expose]` on the `def`
  or on a surrounding `section`.

* [#8559](https://github.com/leanprover/lean4/pull/8559) and [#8560](https://github.com/leanprover/lean4/pull/8560) fix an adversarial
  soundness attack described  in [#8554](https://github.com/leanprover/lean4/pull/8554). The
  attack exploits the fact that `assert!` no longer aborts execution, and
  that users can redirect error messages.

## Language

* [#6973](https://github.com/leanprover/lean4/pull/6973) stops `dsimp` from visiting proof terms, which should make
  `simp` and `dsimp` more efficient.

* [#7428](https://github.com/leanprover/lean4/pull/7428) adds a `dsimp` cache to `simp`. Previously each `dsimp` call from `simp` started with a fresh cache. As a result, time spent in `simp` while compiling Mathlib is reduced by over 45%, giving an overall 8% speedup to Mathlib compilation.

* [#7631](https://github.com/leanprover/lean4/pull/7631) fixes `Lean.Level.mkIMaxAux` (`mk_imax` in the kernel) such that
  `imax 1 u` reduces to `u`.

* [#7977](https://github.com/leanprover/lean4/pull/7977) adds basic support for eta-reduction to `grind`.

* [#8002](https://github.com/leanprover/lean4/pull/8002) fixes an issue where "go to definition" for variables
  generalized by the `induction` and `cases` tactic did not work. Closes
  #2873.

* [#8024](https://github.com/leanprover/lean4/pull/8024) adds the `--setup` option to the `lean` CLI. It takes a path to
  a JSON file containing information about a module's imports and
  configuration, superseding that in the module's own file header. This
  will be used by Lake to specify paths to module artifacts (e.g., oleans
  and ileans) separate from the `LEAN_PATH` schema.

* [#8037](https://github.com/leanprover/lean4/pull/8037) introduces a `noConfusionType` construction that’s sub-quadratic
  in size, and reduces faster.

* [#8104](https://github.com/leanprover/lean4/pull/8104) makes `fun_induction` and `fun_cases` (try to) unfold the
  function application of interest in the goal. The old behavior can be
  enabled with `set_option tactic.fun_induction.unfolding false`. For
  `fun_cases` this does not work yet when the function’s result type
  depends on one of the arguments, see issue #8296.

* [#8106](https://github.com/leanprover/lean4/pull/8106) adds a `register_linter_set` command for declaring linter sets.
  The `getLinterValue` function now checks if the present linter is
  contained in a set that has been enabled (using the `set_option` command
  or on the command line).

* [#8169](https://github.com/leanprover/lean4/pull/8169) makes the whitespace handling in the syntax of `omit` and
  `include` consistent with `variable`.

* [#8171](https://github.com/leanprover/lean4/pull/8171) omits cases from functional induction/cases principles that are
  implemented `by contradiction` (or, more generally, `False.elim`,
  `absurd` or `noConfusion). Breaking change in the sense that there are
  fewer goals to prove after using functional induction.

* [#8196](https://github.com/leanprover/lean4/pull/8196) improves the E-matching pattern inference procedure in `grind`.
  Consider the following theorem:
  ```lean
  @[grind →]
  theorem eq_empty_of_append_eq_empty {xs ys : Array α} (h : xs ++ ys = #[]) : xs = #[] ∧ ys = #[] :=
    append_eq_empty_iff.mp h
  ```
  Before this PR, `grind` inferred the following pattern:
  ```lean
  @HAppend.hAppend _ _ _ _ #2 #1
  ```
  Note that this pattern would match any `++` application, even if it had
  nothing to do with arrays. With this PR, the inferred pattern becomes:
  ```lean
  @HAppend.hAppend (Array #3) (Array _) (Array _) _ #2 #1
  ```
  With the new pattern, the theorem will not be considered by `grind` for
  goals that do not involve `Array`s.

* [#8198](https://github.com/leanprover/lean4/pull/8198) fixes an issue in the theory propagation used in `grind`. When
  two equivalence classes are merged, the core may need to push additional
  equalities or disequalities down to the satellite theory solvers (e.g.,
  `cutsat`, `comm ring`, etc). Some solvers (e.g. `cutsat`) assume that
  all of the core’s invariants hold before they receive those facts.
  Propagating immediately therefore risks violating a solver’s
  pre-conditions midway through the merge. To decouple the merge operation
  from propagation and to keep the core solver-agnostic, this PR adds the
  helper type `PendingTheoryPropagation`.

* [#8208](https://github.com/leanprover/lean4/pull/8208) reduces the need for defeq in frequently used bv_decide rewrite
  by turning them into simprocs that work on structural equality instead.
  As the intended meaning of these rewrites is to simply work with
  structural equality anyways this should not change the proving power of
  `bv_decide`'s rewriter but just make it faster on certain very large
  problems.

* [#8209](https://github.com/leanprover/lean4/pull/8209) fixes a nondeterminism issue in the `grind` tactic. It was a bug
  in the model-based theory combination module.

* [#8221](https://github.com/leanprover/lean4/pull/8221) adjusts the experimental module system to not export the bodies
  of `def`s unless opted out by the new attribute `@[expose]` on the `def`
  or on a surrounding `section`.

* [#8224](https://github.com/leanprover/lean4/pull/8224) adds diagnostic information for the commutative ring procedure
  in `grind`.

* [#8226](https://github.com/leanprover/lean4/pull/8226) fixes the `simplifyBasis` procedure in the commutative ring
  procedure in `grind`.

* [#8231](https://github.com/leanprover/lean4/pull/8231) changes the behaviour of `apply?` so that the `sorry` it uses to
  close the goal is non-synthetic. (Recall that correct use of synthetic
  sorries requires that the tactic also generates an error message, which
  we don't want to do in this situation.) This change defends against the problem reported in [#8212](https://github.com/leanprover/lean4/issues/8212).

* [#8232](https://github.com/leanprover/lean4/pull/8232) fixes elaboration of constants in the `rewrite` tactic.
  previously, `rw [eq_self]` would elaborate `eq_self` twice, and add it
  to the infotree twice. This would lead to the "Expected type" being
  delaborated with an unknown universe metavariable.

* [#8241](https://github.com/leanprover/lean4/pull/8241) changes the behavior of the `rename` tactic to skip over
  implementation detail hypotheses when finding a hypothesis to rename.

* [#8254](https://github.com/leanprover/lean4/pull/8254) fixes unintended inlining of `ToJson`, `FromJson`, and `Repr`
  instances, which was causing exponential compilation times in `deriving`
  clauses for large structures.

* [#8259](https://github.com/leanprover/lean4/pull/8259) clarifies the invalid field notation error when projected value
  type is a metavariable.

* [#8260](https://github.com/leanprover/lean4/pull/8260) clarifies the invalid dotted identifier notation error when the
  type is a sort.

* [#8261](https://github.com/leanprover/lean4/pull/8261) adjusts the error message when `apply` fails to unify. It is
  clearer about distinguishing the term being applied and the goal, as
  well as distinguishing the "conclusion" of the given term and the term
  itself.

* [#8262](https://github.com/leanprover/lean4/pull/8262) improves the type-as-hole error message. Type-as-hole error for
  theorem declarations should not admit the possibility of omitting the
  type entirely.

* [#8264](https://github.com/leanprover/lean4/pull/8264) rewords the `application type mismatch` error message by more
  specifically mentioning that the problem is with the final argument.
  This is useful when the same argument is passed to the function multiple
  times.

* [#8267](https://github.com/leanprover/lean4/pull/8267) makes `#guard_msgs` to treat `trace` messages separate from
  `info`, `warning` and `error`. It also introduce the ability to say
  `#guard_msgs (pass info`, like `(drop info)` so far, and also adds
  `(check info)` as the explicit form of `(info)`, for completeness.

* [#8270](https://github.com/leanprover/lean4/pull/8270) makes the enum pass of `bv_decide` handle enum types that are
  universe polymorphic.

* [#8271](https://github.com/leanprover/lean4/pull/8271) changes `addPPExplicitToExposeDiff` to show universe differences
  and to visit into projections, e.g.:
  ```
  error: tactic 'rfl' failed, the left-hand side
    (Test.mk (∀ (x : PUnit.{1}), True)).1
  is not definitionally equal to the right-hand side
    (Test.mk (∀ (x : PUnit.{2}), True)).1
  ```
  for
  ```lean
  inductive Test where
    | mk (x : Prop)

* [#8275](https://github.com/leanprover/lean4/pull/8275) ensures the congruence closure in `grind` and find non-dependent
  arrow congruences. That is, it can apply the `implies_congr` theorem.

* [#8276](https://github.com/leanprover/lean4/pull/8276) adds the instances `Grind.CommRing (Fin n)` and `Grind.IsCharP
  (Fin n) n`. New tests:
  ```lean
  example (x y z : Fin 13) :
      (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
    grind +ring

* [#8277](https://github.com/leanprover/lean4/pull/8277) improves the generation of `.induct_unfolding` by rewriting
  `match` statements more reliably, using the new “congruence equations”
  introduced in #8284. Fixes #8195.

* [#8280](https://github.com/leanprover/lean4/pull/8280) the support for arrows in the congruence closure procedure used
  in `grind`.

* [#8281](https://github.com/leanprover/lean4/pull/8281) improves the module used to prove auxiliary type cast equalities
  in `grind`.

* [#8284](https://github.com/leanprover/lean4/pull/8284) adds a new variant of equations for matchers, namely “congruence
  equations” that generalize the normal matcher equations. They have
  unrestricted left-hand-sides, extra equality assumptions relating the
  discriminiants with the patterns and thus prove heterogenous equalities.
  In that sense they combine congruence with rewriting. They can be used
  to rewrite matcher applications where, due to dependencies, `simp` would
  fail to rewrite the discriminants, and will be used when producing the
  unfolding induction theorems.

* [#8285](https://github.com/leanprover/lean4/pull/8285) fixes “declaration has free variables” errors when generating a
  splitter for a match statement with named patterns. Fixes #8274.

* [#8299](https://github.com/leanprover/lean4/pull/8299) implements a missing preprocessing step in `grind`: abstract
  metavariables in the goal

* [#8301](https://github.com/leanprover/lean4/pull/8301) unfolds functions in the unfolding induction principle properly
  when they use `bif` (a.k.a. `Bool.cond`).

* [#8302](https://github.com/leanprover/lean4/pull/8302) lets `cases` fail gracefully when the motive has an complex
  argument whose type is dependent type on the targets. While the
  `induction` tactic can handle this well, `cases` does not. This change
  at least gracefully degrades to not instantiating that motive parameter.
  See issue [#8296](https://github.com/leanprover/lean4/issues/8296) for more details on this issue.

* [#8303](https://github.com/leanprover/lean4/pull/8303) fixes missing occurrences of `foldProjs` in `grind`.

* [#8306](https://github.com/leanprover/lean4/pull/8306) makes it possible for `bv_decide` to tackle situations for its
  enum type preprocessing where the enums themselves are use in a
  dependently type context (for example inside of a `GetElem` body) and
  thus not trivially accessible to `simp` for rewriting. To do this we
  drop`GetElem` on `BitVec` as well as `dite` as early as possible in the
  pipeline.

* [#8321](https://github.com/leanprover/lean4/pull/8321) lets the termination argument inference consider negations of
  Nat comparisons. Fixes [#8257](https://github.com/leanprover/lean4/issues/8257).

* [#8323](https://github.com/leanprover/lean4/pull/8323) adds support for bv_decide to understand `BitVec.reverse` in
  bitblasting.

* [#8330](https://github.com/leanprover/lean4/pull/8330) improves support for structure extensionality in `grind`. It now
  uses eta expansion for structures instead of the extensionality theorems
  generated by `[ext]`. Examples:

  ```lean
  opaque f (a : Nat) : Nat × Bool

* [#8338](https://github.com/leanprover/lean4/pull/8338) improves the error messages displayed in `inductive`
  declarations when type parameters are invalid or absent.

* [#8341](https://github.com/leanprover/lean4/pull/8341) fixes the `propagateCtor` constraint propagator used in `grind`.

* [#8343](https://github.com/leanprover/lean4/pull/8343) splits `Lean.Grind.CommRing` into 4 typeclasses, for semirings
  and noncommutative rings. This does not yet change the behaviour of
  `grind`, which expects to find all 4 typeclasses. Later we will make
  some generalizations.

* [#8344](https://github.com/leanprover/lean4/pull/8344) fixes term normalization issues in `grind`, and the new option
  `grind +etaStruct`.

* [#8347](https://github.com/leanprover/lean4/pull/8347) adds draft typeclasses for `grind` to process facts about
  ordered modules. These interfaces will evolve as the implementation
  develops.

* [#8354](https://github.com/leanprover/lean4/pull/8354) makes sure that when generating the unfolding functional
  induction theorem, `mdata` does not get in the way.

* [#8356](https://github.com/leanprover/lean4/pull/8356) tries harder to clean internals of the argument packing of n-ary
  functions from the functional induction theorem, in particular the
  unfolding variant

* [#8359](https://github.com/leanprover/lean4/pull/8359) improves the functional cases principles, by making a more
  educated guess which function parameters should be targets and which
  should remain parameters (or be dropped). This simplifies the
  principles, and increases the chance that `fun_cases` can unfold the
  function call.

* [#8361](https://github.com/leanprover/lean4/pull/8361) fixes a bug in the `cases` tacic introduced in #3188 that arises
  when cases (not induction) is used with a non-atomic expression in using
  and the argument indexing gets confused.

* [#8363](https://github.com/leanprover/lean4/pull/8363) unifies various ways of naming auxiliary declarations in a
  conflict-free way and ensures the method is compatible with diverging
  branches of elaboration such as parallelism or Aesop-like
  backtracking+replaying search.

* [#8365](https://github.com/leanprover/lean4/pull/8365) fixes the transparency mode for ground patterns. This is
  important for implicit instances. Here is a mwe for an issue detected
  while testing `grind` in Mathlib.
  ```lean
  example (a : Nat) : max a a = a := by
    grind

* [#8368](https://github.com/leanprover/lean4/pull/8368) improves the error messages produced by invalid pattern-match
  alternatives and improves parity in error placement between
  pattern-matching tactics and elaborators.

* [#8369](https://github.com/leanprover/lean4/pull/8369) fixes a type error at `instantiateTheorem` function used in
  `grind`. It was failing to instantiate theorems such as
  ```lean
  theorem getElem_reverse {xs : Array α} {i : Nat} (hi : i < xs.reverse.size)
      : (xs.reverse)[i] = xs[xs.size - 1 - i]'(by simp at hi; omega)
  ```
  in examples such as
  ```lean
  example (xs : Array Nat) (w : xs.reverse = xs) (j : Nat) (hj : 0 ≤ j) (hj' : j < xs.size / 2)
      : xs[j] = xs[xs.size - 1 - j]
  ```
  generating the issue
  ```lean
    [issue] type error constructing proof for Array.getElem_reverse
        when assigning metavariable ?hi with
          ‹j < xs.toList.length›
        has type
          j < xs.toList.length : Prop
        but is expected to have type
          j < xs.reverse.size : Prop
  ```

* [#8375](https://github.com/leanprover/lean4/pull/8375) ensures that using `mapError` to expand an error message uses
  `addMessageContext` to include the current context, so that expressions
  are rendered correctly. Also adds a `preprendError` variant with a more
  convenient argument order for the common cases of
  prepending-and-indenting.

* [#8403](https://github.com/leanprover/lean4/pull/8403) adds missing monotonicity lemmas for universal quantifiers, that
  are used in defining (co)inductive predicates.

* [#8410](https://github.com/leanprover/lean4/pull/8410) fixes a case-splitting heuristic in `grind` and simplifies the
  proof for test `grind_palindrome2.lean`.

* [#8412](https://github.com/leanprover/lean4/pull/8412) fixes the `markNestedProofs` preprocessor used in `grind`. There
  was a missing case (e.g., `Expr.mdata`)

* [#8413](https://github.com/leanprover/lean4/pull/8413) implements normalization rules that pull universal quantifiers
  across disjunctions. This is a common normalization step performed by
  first-order theorem provers.

* [#8417](https://github.com/leanprover/lean4/pull/8417) introduces `Lean.Grind.Field`, proves that a `IsCharP 0` field
  satisfies `NoNatZeroDivisors`, and sets up some basic (currently
  failing) tests for `grind`.

* [#8426](https://github.com/leanprover/lean4/pull/8426) adds the attribute `[grind?]`. It is like `[grind]` but displays
  inferred E-matching patterns. It is a more convinient than writing.
  Thanks @kim-em for suggesting this feature.
  ```lean
  set_option trace.grind.ematch.pattern true
  ```
  also improves some tests, and adds helper function
  `ENode.isRoot`.

* [#8429](https://github.com/leanprover/lean4/pull/8429) adds `Lean.Grind.Ring.IsOrdered`, and cleans up the ring/module
  grind API. These typeclasses are at present unused, but will support
  future algorithmic improvements in `grind`.

* [#8437](https://github.com/leanprover/lean4/pull/8437) fixes `split` in the presence of metavariables in the target.

* [#8438](https://github.com/leanprover/lean4/pull/8438) ensures that `grind` diagnostics are obtained even when
  `maxHeartbeats` is reached.
  also removes some dead code.

* [#8440](https://github.com/leanprover/lean4/pull/8440) implements non-chronological backtracking for the `grind`
  tactic. This feature ensures that `grind` does not need to process
  irrelevant branches after performing a case-split that is not relevant.
  It is not just about performance, but also the size of the final proof
  term. The new test demonstrates this feature in practice.
  ```lean
  -- In the following test, the first 8 case-splits are irrelevant,
  -- and non-choronological backtracking is used to avoid searching
  -- (2^8 - 1) irrelevant branches
  /--
  trace:
  [grind.split] p8 ∨ q8, generation: 0
  [grind.split] p7 ∨ q7, generation: 0
  [grind.split] p6 ∨ q6, generation: 0
  [grind.split] p5 ∨ q5, generation: 0
  [grind.split] p4 ∨ q4, generation: 0
  [grind.split] p3 ∨ q3, generation: 0
  [grind.split] p2 ∨ q2, generation: 0
  [grind.split] p1 ∨ q1, generation: 0
  [grind.split] ¬p ∨ ¬q, generation: 0
  -/
  #guard_msgs (trace) in
  set_option trace.grind.split true in
  theorem ex
      : p ∨ q →
        ¬ p ∨ q →
        p ∨ ¬ q →
        ¬ p ∨ ¬ q →
        p1 ∨ q1 →
        p2 ∨ q2 →
        p3 ∨ q3 →
        p4 ∨ q4 →
        p5 ∨ q5 →
        p6 ∨ q6 →
        p7 ∨ q7 →
        p8 ∨ q8 →
        False := by
    grind (splits := 10)
  ```

* [#8443](https://github.com/leanprover/lean4/pull/8443) adds the lemmas about ordered rings and ordered fields which
  will be needed by the new algebraic normalization components of `grind`.

* [#8449](https://github.com/leanprover/lean4/pull/8449) upstreams and extends the Mathlib `clear_value` tactic. Given a
  local definition `x : T := v`, the tactic `clear_value x` replaces it
  with a hypothesis `x : T`, or throws an error if the goal does not
  depend on the value `v`. The syntax `clear_value x with h` creates a
  hypothesis `h : x = v` before clearing the value of `x`. Furthermore,
  `clear_value *` clears all values that can be cleared, or throws an
  error if none can be cleared.

* [#8450](https://github.com/leanprover/lean4/pull/8450) adds a feature to the `subst` tactic so that when `x : X := v`
  is a local definition, `subst x` substitutes `v` for `x` in the goal and
  removes `x`. Previously the tactic would throw an error.

* [#8466](https://github.com/leanprover/lean4/pull/8466) fixes another instance of the `grind` issue "unexpected kernel
  projection term during internalization".

* [#8472](https://github.com/leanprover/lean4/pull/8472) avoids name resolution blocking on the elaboration of a
  theorem's proof when looking up the theorem name.

* [#8479](https://github.com/leanprover/lean4/pull/8479) implements hash-consing for `grind` that takes alpha equivalence
  into account.

* [#8483](https://github.com/leanprover/lean4/pull/8483) ensures `grind` reuses the `simp` cache between different calls.
  Recall that `grind` uses `simp` to normalize terms during
  internalization.

* [#8491](https://github.com/leanprover/lean4/pull/8491) fixes the behavior of `simp_all?` and `simp_all?!`, aligning
  them with `simp_all` and `simp_all!` respectively.

* [#8506](https://github.com/leanprover/lean4/pull/8506) implements `match`-expressions in `grind` using `match`
  congruence equations. The goal is to minimize the number of `cast`
  operations that need to be inserted, and avoid `cast` over functions.
  The new approach support `match`-expressions of the form `match h : ...
  with ...`.

* [#8512](https://github.com/leanprover/lean4/pull/8512) adds a `value_of% ident` term that elaborates to the value of
  the local or global constant `ident`. This is useful for creating
  definition hypotheses:
  ```lean
  let x := ... complicated expression ...
  have hx : x = value_of% x := rfl
  ```

* [#8516](https://github.com/leanprover/lean4/pull/8516) is a followup to #8449 to refine the syntax of `clear_value`.
  The syntax for adding equality hypotheses before clearing values is now
  `clear_value (h : x = _)`. Any expression definitionally equal to `x`
  can be used in place of the underscore.

* [#8536](https://github.com/leanprover/lean4/pull/8536) fixes the support for `LawfulBEq` and `BEq` in `grind`.

* [#8541](https://github.com/leanprover/lean4/pull/8541) ensures that for any nested proof `h : p` in a goal, we
  propagate that `p` is true in the `grind` tactic.

* [#8542](https://github.com/leanprover/lean4/pull/8542) fixes two inappropriate uses of `whnfD` in `grind`. They were
  potential performance foot guns, and were producing unexpected errors
  since `whnfD` is not consistently used (and it should not be) in all
  modules.

* [#8544](https://github.com/leanprover/lean4/pull/8544) implements support for over-applied `ite` and `dite`
  applications in the `grind` tactic. It adds support for propagation and
  case-split.

* [#8549](https://github.com/leanprover/lean4/pull/8549) fixes the hash function used to implement congruence closure in
  `grind`. The hash of an `Expr` must not depend on whether the expression
  has been internalized or not.

* [#8564](https://github.com/leanprover/lean4/pull/8564) simplifies the interface between the `grind` core and the cutsat
  procedure. Before this PR, core would try to minimize the number of
  numeric literals that have to be internalized in cutsat. This
  optimization was buggy (see `grind_cutsat_zero.lean` test), and produced
  counterintuitive counterexamples.

* [#8569](https://github.com/leanprover/lean4/pull/8569) adds support for generalized E-match patterns to arbitrary
  theorems.

* [#8570](https://github.com/leanprover/lean4/pull/8570) fixes some issues in the E-matching generalized pattern support
  after the update stage0.

* [#8572](https://github.com/leanprover/lean4/pull/8572) adds some generalized `Option` theorems for `grind` . The avoid
  `casts` operations during E-matching.

* [#8576](https://github.com/leanprover/lean4/pull/8576) sets `ring := true` by default in `grind`. It also fixes a bug
  in the reification procedure, and improves the term internalization in
  the ring and cutsat modules.

## Library

* [#7352](https://github.com/leanprover/lean4/pull/7352) reworks the `simp` set around the `Id` monad, to not elide or
  unfold `pure` and `Id.run`

* [#7995](https://github.com/leanprover/lean4/pull/7995) adds a verification of `Array.qsort` properties, trying to use
  `grind` and `fun_induction` where possible.
  Currently this is in the `tests/` folder, but once `grind` is ready for
  production use we will move it out into the library.

* [#8182](https://github.com/leanprover/lean4/pull/8182) adds `ofList_eq_insertMany_empty` lemmas for all the hash/tree
  map types, with the exception of
  `Std.HashSet.Raw.ofList_eq_insertMany_empty`.

* [#8188](https://github.com/leanprover/lean4/pull/8188) takes the existing `getElem_map` statements for `HashMap`
  variants (also `getElem?`, `getElem!`, and `getD` statements), adds a
  prime to their name and an explanatory comment, and replaces the
  unprimed statement with a simpler statement that is only true with
  `LawfulBEq` present. The original statements which were simp lemmas are
  now low priority simp lemmas, so the nicer statements should fire when
  `LawfulBEq` is available.

* [#8202](https://github.com/leanprover/lean4/pull/8202) adds an inference that was repeatedly needed when proving
  `BitVec.msb_sdiv`, and is the symmetric version of
  `BitVec.one_eq_zero_iff`

* [#8206](https://github.com/leanprover/lean4/pull/8206) shows that negating a bitvector created from a natural number
  equals creating a bitvector from the the negative of that number (as an
  integer).

* [#8216](https://github.com/leanprover/lean4/pull/8216) completes adding `@[grind]` annotations for `Option` lemmas, and
  incidentally fills in some `Option` API gaps/defects.

* [#8218](https://github.com/leanprover/lean4/pull/8218) continues adding `@[grind]` attributes for List/Array/Vector,
  particularly to the lemmas involving the `toList`/`toArray` functions.

* [#8246](https://github.com/leanprover/lean4/pull/8246) add `@[grind]` annotations for HashMap and variants.

* [#8272](https://github.com/leanprover/lean4/pull/8272) adds lemmas about the length and use of `[]?` on results of
  `List.intersperse`.

* [#8291](https://github.com/leanprover/lean4/pull/8291) changes the statements of `Fin` lemmas to use `[NeZero n] (i :
  Fin n)` rather than `(i : Fin (n+1))` where possible.

* [#8298](https://github.com/leanprover/lean4/pull/8298) adds various `Option` lemmas and defines `Option.filterM` for
  applicative functors.

* [#8313](https://github.com/leanprover/lean4/pull/8313) changes the definition of `Vector` so it no longer extends
  `Array`. This prevents `Array` API from "leaking through".

* [#8315](https://github.com/leanprover/lean4/pull/8315) splits `Std.Classes.Ord` into `Std.Classes.Ord.Basic` (with few
  imports) and `Std.Classes.Ord.SInt` and `Std.Classes.Ord.Vector`. These
  changes avoid importing `Init.Data.BitVec.Lemmas` unnecessarily into
  various basic files.
  As the new import-only file `Std.Classes.Ord` imports all three of
  these, end-users are not affected.

* [#8318](https://github.com/leanprover/lean4/pull/8318) is follow-up to #8272, combining the conditional lemmas for
  `getElem_intersperse` into a single lemma with an `if` on the RHS.

* [#8327](https://github.com/leanprover/lean4/pull/8327) adds `@[grind]` annotations to the generic
  `getElem?_eq_none_iff`, `isSome_getElem?`, and `get_getElem?`.

* [#8328](https://github.com/leanprover/lean4/pull/8328) adds the `@[grind =]` attribute to all `contains_iff_mem`
  lemmas.

* [#8331](https://github.com/leanprover/lean4/pull/8331) improves the docstring for `PlainDateTime.now` and its variants.

* [#8346](https://github.com/leanprover/lean4/pull/8346) adds some missing lemmas about consequences of
  positivity/non-negativity of `a * b : Int`.

* [#8349](https://github.com/leanprover/lean4/pull/8349) fixes the signature of the intended `Inhabited` instance for
  `ExtDHashMap`.

* [#8357](https://github.com/leanprover/lean4/pull/8357) adds variants of `dite_eq_left_iff` that will be useful in a
  future PR.

* [#8358](https://github.com/leanprover/lean4/pull/8358) introduces a very minimal version of the new iterator library.
  It comes with list iterators and various consumers, namely `toArray`,
  `toList`, `toListRev`, `ForIn`, `fold`, `foldM` and `drain`. All
  consumers also come in a partial variant that can be used without any
  proofs. This limited version of the iterator library generates decent
  code, even with the old code generator.

* [#8378](https://github.com/leanprover/lean4/pull/8378) improves and extends the api around `Ord` and `Ordering`.

* [#8379](https://github.com/leanprover/lean4/pull/8379) adds missing `Option` lemmas.

* [#8380](https://github.com/leanprover/lean4/pull/8380) provides simple lemmas about `toArray`, `toList` and `toListRev`
  for the iterator library.

* [#8384](https://github.com/leanprover/lean4/pull/8384) provides lemmas about the behavior of `step`, `toArray`,
  `toList` and `toListRev` on list iterators created with `List.iter` and
  `List.iterM`.

* [#8389](https://github.com/leanprover/lean4/pull/8389) adds the `List/Array/Vector.ofFnM`, the monadic analogues of
  `ofFn`, along with basic theory.

* [#8392](https://github.com/leanprover/lean4/pull/8392) corrects some `Array` lemmas to be about `Array` not `List`.

* [#8397](https://github.com/leanprover/lean4/pull/8397) cleans up many duplicate instances (or, in some cases,
  needlessly duplicated `def X := ...; instance Y := X`).

* [#8399](https://github.com/leanprover/lean4/pull/8399) adds variants of `HashMap.getElem?_filter` that assume
  `LawfulBEq` and have a simpler right-hand-side. `simp` can already
  achieve these, via rewriting with `getKey_eq` under the lambda. However
  `grind` can not, and these lemmas help `grind` work with `HashMap`
  goals. There are variants for all variants of `HashMap`,
  `getElem?/getElem/getElem!/getD`, and for `filter` and `filterMap`.

* [#8405](https://github.com/leanprover/lean4/pull/8405) provides lemmas about the loop constructs `ForIn`, `fold`,
  `foldM` and `drain` and their relation to each other in the context of
  iterators.

* [#8418](https://github.com/leanprover/lean4/pull/8418) provides the `take` iterator combinator that transforms any
  iterator into an iterator that stops after a given number of steps. The
  change contains the implementation and lemmas.

* [#8422](https://github.com/leanprover/lean4/pull/8422) adds `LT` and `Decidable` `LT` instances for
  `Std.Time.Timestamp` and `Std.Time.Duration`.

* [#8434](https://github.com/leanprover/lean4/pull/8434) adds the equivalent of `List.take_cons` about `List.drop`.

* [#8435](https://github.com/leanprover/lean4/pull/8435) upstreams the `LawfulMonadLift(T)` classes, lemmas and instances
  from Batteries into Core because the iterator library needs them in
  order to prove lemmas about the `mapM` operator, which relies on
  `MonadLiftT`.

* [#8445](https://github.com/leanprover/lean4/pull/8445) adds a `@[simp]` lemma, and comments explaining that there is
  intentionally no verification API for `Vector.take`, `Vector.drop`, or
  `Vector.tail`, which should all be rewritten in terms of
  `Vector.extract`.

* [#8446](https://github.com/leanprover/lean4/pull/8446) adds basic `@[grind]` annotations for `TreeMap` and its
  variants. Likely more annotations will be added after we've explored
  some examples.

* [#8451](https://github.com/leanprover/lean4/pull/8451) provides the iterator combinator `filterMap` in a pure and
  monadic version and specializations `map` and `filter`. This new
  combinator allows to apply a function to the emitted values of a stream
  while filtering out certain elements.

* [#8460](https://github.com/leanprover/lean4/pull/8460) adds further `@[grind]` annotations for `Option`, as follow-up
  to the recent additions to the `Option` API in #8379 and #8298.

* [#8465](https://github.com/leanprover/lean4/pull/8465) adds further lemmas about `LawfulGetElem`, including marking
  some with `@[grind]`.

* [#8470](https://github.com/leanprover/lean4/pull/8470) adds `@[simp]` to `getElem_pos/neg` (similarly for `getElem!`).
  These are often already simp lemmas for concrete types.

* [#8482](https://github.com/leanprover/lean4/pull/8482) adds preliminary `@[grind]` annotations for `List.Pairwise` and
  `List.Nodup`.

* [#8484](https://github.com/leanprover/lean4/pull/8484) provides the iterator combinator `zip` in a pure and monadic
  version.

* [#8492](https://github.com/leanprover/lean4/pull/8492) adds `simp` lemmas for `toInt_*` and `toNat_*` with arithmetic
  operation given the hypothesis of no-overflow
  (`toNat_add_of_not_uaddOverflow`, `toInt_add_of_not_saddOverflow`,
  `toNat_sub_of_not_usubOverflow`, `toInt_sub_of_not_ssubOverflow`,
  `toInt_neg_of_not_negOverflow`, `toNat_mul_of_not_umulOverflow`,
  `toInt_mul_of_not_smulOverflow`). In particular, these are `simp` since
  (1) the `rhs` is strictly simpler than the `lhs` and (2) this version is
  also simpler than the standard operation when the hypothesis is
  available.

* [#8493](https://github.com/leanprover/lean4/pull/8493) provides the iterator combinators `takeWhile` (forwarding all
  emitted values of another iterator until a predicate becomes false)
  `dropWhile` (dropping values until some predicate on these values
  becomes false, then forwarding all the others).

* [#8497](https://github.com/leanprover/lean4/pull/8497) adds preliminary grind annotations for
  `List.Sublist`/`IsInfix`/`IsPrefix`/`IsSuffix`, along with test cases.

* [#8499](https://github.com/leanprover/lean4/pull/8499) changes the definition of `Array.ofFn.go` to use recursion on
  `Nat` (rather than well-founded recursion). This resolves a problem
  reported on [zulip](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Memory.20issues.20with.20.60Vector.2EofFn.60.2E/near/520622564)).

* [#8513](https://github.com/leanprover/lean4/pull/8513) removes the `@[reducible]` annotation on `Array.size`. This is
  probably best gone anyway in order to keep separation between the `List`
  and `Array` APIs, but it also helps avoid uselessly instantiating
  `Array` theorems when `grind` is working on `List` problems.

* [#8515](https://github.com/leanprover/lean4/pull/8515) removes the prime from `Fin.ofNat'`: the old `Fin.ofNat` has
  completed its 6 month deprecation cycle and is being removed.

* [#8527](https://github.com/leanprover/lean4/pull/8527) adds `grind` annotations for theorems about `List.countP` and
  `List.count`.

* [#8552](https://github.com/leanprover/lean4/pull/8552) provides array iterators (`Array.iter(M)`,
  `Array.iterFromIdx(M)`), infinite iterators produced by a step function
  (`Iter.repeat`), and a `ForM` instance for finite iterators that is
  implemented in terms of `ForIn`.

* [#8620](https://github.com/leanprover/lean4/pull/8620) removes the `NatCast (Fin n)` global instance (both the direct
  instance, and the indirect one via `Lean.Grind.Semiring`), as that
  instance causes causes `x < n` (for `x : Fin k`, `n : Nat`) to be
  elaborated as `x < ↑n` rather than `↑x < n`, which is undesirable. Note
  however that in Mathlib this happens anyway!

## Compiler

* [#8211](https://github.com/leanprover/lean4/pull/8211) adds support for generating IR from the LCNF representation of
  the new compiler.

* [#8236](https://github.com/leanprover/lean4/pull/8236) fixes an issue where the combination of `extern_lib` and
  `precompileModules` would lead to "symbol not found" errors.

* [#8268](https://github.com/leanprover/lean4/pull/8268) optimizes lean_nat_shiftr for scalar operands. The new compiler
  converts Nat divisions into right shifts, so this now shows up as hot in
  some profiles.

* [#8308](https://github.com/leanprover/lean4/pull/8308) makes the new compiler's specialization pass compute closures
  the same way as the old compiler, in particular when it comes to
  variables captured by lambdas.

* [#8367](https://github.com/leanprover/lean4/pull/8367) adds a new `structProjCases` pass to the new compiler, analogous
  to the `struct_cases_on` pass in the old compiler, which converts all
  projections from structs into `cases` expressions. When lowered to IR,
  this causes all of the projections from a single structure to be grouped
  together, which is an invariant relied upon by the IR RC passes (at
  least for linearity, if not general correctness).

* [#8409](https://github.com/leanprover/lean4/pull/8409) adds support to LCNF for native UInt8/UInt16/UInt32/UInt64
  literals.

* [#8456](https://github.com/leanprover/lean4/pull/8456) adds support for primitive USize literals in LCNF.

* [#8458](https://github.com/leanprover/lean4/pull/8458) adds closed term extraction to the new compiler, closely
  following the approach in the old compiler. In the future, we will
  explore some ideas to improve upon this approach.

* [#8462](https://github.com/leanprover/lean4/pull/8462) enables the LCNF extractClosed pass by default.

* [#8468](https://github.com/leanprover/lean4/pull/8468) switches the LCNF baseExt/monoExt environment extensions to use
  a custom environment extension that uses a PersistentHashMap. The
  optimizer relies upon the ability to update a decl multiple times, which
  does not work with SimplePersistentEnvExtension.

* [#8502](https://github.com/leanprover/lean4/pull/8502) changes the new compiler to use the kernel environment to find
  definitions, which causes compilation to be skipped when the decl had a
  kernel error (e.g. due to an unresolved metavariable). This matches the
  behavior of the old compiler.

* [#8521](https://github.com/leanprover/lean4/pull/8521) makes LCNF.toMono recursively process jmp args.

* [#8523](https://github.com/leanprover/lean4/pull/8523) moves the new compiler's noncomputable check into toMono,
  matching the recent change in the old compiler. This is mildly more
  complicated because we can't throw an error at the mere use of a
  constant, we need to check for a later relevant use. This is still a bit
  more conservative than it could theoretically be around join points and
  local functions, but it's hard to imagine that mattering in practice
  (and we can easily enable it if it does).

* [#8535](https://github.com/leanprover/lean4/pull/8535) extracts more Nats (and their downstream users) in extractClosed
  by fixing a silly oversight in the logic.

* [#8540](https://github.com/leanprover/lean4/pull/8540) changes the LCNF specialize pass to allow ground variables to
  depend on local fun decls (with no non-ground free variables). This
  enables specialization of Monad instances that depend on local lambdas.

* [#8559](https://github.com/leanprover/lean4/pull/8559) fixes an adversarial soundness attack described in #8554. The
  attack exploits the fact that `assert!` no longer aborts execution, and
  that users can redirect error messages.
  Another PR will implement the same fix for `Expr.Data`.

* [#8560](https://github.com/leanprover/lean4/pull/8560) is similar to #8559 but for `Expr.mkData`. This vulnerability
  has not been exploited yet, but adversarial users may find a way.

* [#8561](https://github.com/leanprover/lean4/pull/8561) increases maxHeartbeats in the isDefEqProjIssue test, because
  when running under the new compiler the `run_meta` call includes the
  allocations of the compiler itself. With the old compiler, many of the
  corresponding allocations were internal to C++ code and would not
  increase the heartbeat count.

* [#8565](https://github.com/leanprover/lean4/pull/8565) makes the LCNF specialization pass only treat type/instance
  params as ground vars. The current policy was too liberal and would
  result on computations being floated into specialized loops.

* [#8566](https://github.com/leanprover/lean4/pull/8566) changes the LCNF constant folding pass to not convert Nat
  multiplication to a left shift by a power of 2. The fast path test for
  this is sufficiently complex that it's simpler to just use the fast path
  for multiplication.

* [#8575](https://github.com/leanprover/lean4/pull/8575) makes LCNF's simpAppApp? bail out on trivial aliases as
  intended. It seems that there was a typo in the original logic, and this
  PR also extends it to include aliases of global constants rather than
  just local vars.

* [#8582](https://github.com/leanprover/lean4/pull/8582) fixes an accidental dropping of state in Param.toMono. When this
  code was originally written, there was no other state besides
  `typeParams`.

## Pretty Printing

* [#8041](https://github.com/leanprover/lean4/pull/8041) changes the behavior of `pp.showLetValues` to use a hoverable
  `⋯` to hide let values. This is now false by default, and there is a new
  option `pp.showLetValues.threshold` for allowing small expressions to be
  shown anyway. For tactic metavariables, there is an additional option
  `pp.showLetValues.tactic.threshold`, which by default is set to the
  maximal value, since in tactic states local values are usually
  significant.

* [#8372](https://github.com/leanprover/lean4/pull/8372) modifies the pretty printer to use `have` syntax instead of
  `let_fun` syntax.

* [#8457](https://github.com/leanprover/lean4/pull/8457) fixes an issue when including a hard line break in a `Format`
  that caused subsequent (ordinary) line breaks to be erroneously
  flattened to spaces.

* [#8504](https://github.com/leanprover/lean4/pull/8504) modifies the pretty printer so that dot notation is used for
  class parent projections. Previously, dot notation was never used for
  classes.

## Documentation

* [#8199](https://github.com/leanprover/lean4/pull/8199) adds a style guide for documentation, including both general
  principles and docstring-specific concerns.

## Server

* [#7665](https://github.com/leanprover/lean4/pull/7665) and [#8180](https://github.com/leanprover/lean4/pull/8180) add
  support for code actions that resolve 'unknown identifier' errors by either importing the missing declaration or by
  changing the identifier to one from the environment.

* [#8091](https://github.com/leanprover/lean4/pull/8091) improves the performance of the workspace symbol request.

* [#8242](https://github.com/leanprover/lean4/pull/8242) fixes the 'goals accomplished' diagnostics. They were
  accidentally broken in #7902.

* [#8350](https://github.com/leanprover/lean4/pull/8350) changes namespace completion to use the same algorithm as
  declaration identifier completion, which makes it use the short name
  (last name component) for completions instead of the full name, avoiding
  namespace duplications.

* [#8362](https://github.com/leanprover/lean4/pull/8362) fixes a bug where the unknown identifier code actions wouldn't
  work correctly for some unknown identifier error spans and adjusts
  several unknown identifier spans to actually end on the identifier in
  question.

## Lake

* [#8383](https://github.com/leanprover/lean4/pull/8383) fixes the use of `import Lake` with precompiled modules, which
  was previously broken on MacOS.

* [#8411](https://github.com/leanprover/lean4/pull/8411) fixes a doc bug in the Resolve.lean; in reverse order, B comes
  before A

* [#8528](https://github.com/leanprover/lean4/pull/8528) fixes the heuristic Lake uses to determine whether a `lean_lib`
  can be loaded via `lean --plugin` rather than `lean --load-dynlib`.
  Previously, a mismatch between the single root's name and the library's
  name would not be caught and cause loading to fail.

* [#8529](https://github.com/leanprover/lean4/pull/8529) changes `lake lean` and `lake setup-file` to precompile the
  imports of non-workspace files using the the import's whole library.
  This ensures that additional link objects are linked and available
  during elaboration.

* [#8539](https://github.com/leanprover/lean4/pull/8539) changes Lake to use relative path for the Lean messages produced
  by a module build. This makes the message portable across different
  machines, which is useful for Mathlib's cache.

## Other

* [#8192](https://github.com/leanprover/lean4/pull/8192) includes upgrades to the `release_checklist.py` script prepared
  while releasing v4.20.0-rc1.

* [#8366](https://github.com/leanprover/lean4/pull/8366) adds the `expose` attribute to `Ordering.then`. This is required
  for building with the new compiler, but works fine with the old compiler
  because it silently ignores the missing definition.


````
