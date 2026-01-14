/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.27.0-rc1 (2025-12-14)" =>
%%%
tag := "release-v4.27.0"
file := "v4.27.0"
%%%

````markdown
For this release, 372 changes landed. In addition to the 118 feature additions and 71 fixes listed below there were 28 refactoring changes, 13 documentation improvements, 25 performance improvements, 6 improvements to the test suite and 111 other changes.

## Highlights

### Module System Stabilized

[#11637](https://github.com/leanprover/lean4/pull/11637) declares the module system as no longer experimental and makes
the `experimental.module` option a no-op.

See the [Sources Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-scopes)
chapter in the reference manual for the documentation.

### Performance Gains

This release includes many performance improvements, notably:

- [#11162](https://github.com/leanprover/lean4/pull/11162) reduces the memory consumption of the language server (the
  watchdog process in particular). In Mathlib, it reduces memory
  consumption by about 1GB.

- [#11507](https://github.com/leanprover/lean4/pull/11507) optimizes the filesystem accesses during importing for a ~3% win
  on Linux, potentially more on other platforms.

### Error Messages

This release contains a series of changes to error messages aimed at making them more helpful and actionable.
Specifically, some messages now have hints, suggestions, and links to explanations.

PRs:
[#11119](https://github.com/leanprover/lean4/pull/11119),
[#11245](https://github.com/leanprover/lean4/pull/11245),
[#11346](https://github.com/leanprover/lean4/pull/11346),
[#11347](https://github.com/leanprover/lean4/pull/11347),
[#11456](https://github.com/leanprover/lean4/pull/11456),
[#11482](https://github.com/leanprover/lean4/pull/11482),
[#11518](https://github.com/leanprover/lean4/pull/11518),
[#11554](https://github.com/leanprover/lean4/pull/11554),
[#11555](https://github.com/leanprover/lean4/pull/11555),
[#11621](https://github.com/leanprover/lean4/pull/11621).

### New Features in Grind

#### Function-Valued Congruence Closure

[#11323](https://github.com/leanprover/lean4/pull/11323) introduces a new `grind` option, `funCC` (enabled by default),
which extends congruence closure to _function-valued_ equalities. When
`funCC` is enabled, `grind` tracks equalities of **partially applied
functions**, allowing reasoning steps such as:

```lean
a : Nat → Nat
f : (Nat → Nat) → (Nat → Nat)
h : f a = a
⊢ (f a) m = a m

g : Nat → Nat
f : Nat → Nat → Nat
h : f a = g
⊢ f a b = g b
```

This feature substantially improves grind’s support for higher-order and
partially-applied function equalities, while preserving compatibility with
first-order SMT behavior when funCC is disabled.

See the PR description for more details on usage.

#### Controlling Theorem Instantiation

[#11428](https://github.com/leanprover/lean4/pull/11428) implements support for **guards** in `grind_pattern`. The new
feature provides additional control over theorem instantiation. For
example, consider the following monotonicity theorem:

```lean
opaque f : Nat → Nat
theorem fMono : x ≤ y → f x ≤ f y := ...
```

With the new `guard` feature, we can instruct `grind` to instantiate the
theorem **only if** `x ≤ y` is already known to be true in the current `grind` state:

```lean
grind_pattern fMono => f x, f y where
  guard x ≤ y
  x =/= y
```

This allows for a significant reduction in the number of theorem instantiations.

See the PR description for a more detailed discussion and example proof traces.

#### Supplying Arbitrary Parameters

[#11268](https://github.com/leanprover/lean4/pull/11268) implements support for arbitrary `grind` parameters. The feature
is similar to the one available in `simp`, where a proof term is treated
as a local universe-polymorphic lemma. This feature relies on `grind -revert` (see [#11248](https://github.com/leanprover/lean4/pull/11248)).
For example, users can now write:

```lean
def snd (p : α × β) : β := p.2
theorem snd_eq (a : α) (b : β) : snd (a, b) = b := rfl

/--
trace: [grind.ematch.instance] snd_eq (a + 1): snd (a + 1, Type) = Type
[grind.ematch.instance] snd_eq (a + 1): snd (a + 1, true) = true
-/
#guard_msgs (trace) in
set_option trace.grind.ematch.instance true in
example (a : Nat) : (snd (a + 1, true), snd (a + 1, Type), snd (2, 2)) = (true, Type, snd (2, 2)) := by
  grind [snd_eq (a + 1)]
```

Note that in the example above, `snd_eq` is instantiated only twice, but with different universe parameters.

#### Grind Revert

[#11248](https://github.com/leanprover/lean4/pull/11248) implements the option `revert`, which is set to `false` by
default.

This is an internal change related to reverting hypotheses.
With the new default, the traces, counterexamples, and proof terms produced by `grind` are different.
To recover the old `grind` behavior, use `grind +revert`.

#### Other New Features in Grind

- `BitVec` support in `grind ring` ([#11639](https://github.com/leanprover/lean4/pull/11639))
  and `grind lia` ([#11640](https://github.com/leanprover/lean4/pull/11640));

- New configuration option, `grind -reducible`, which allows expansion of non-reducible declarations
  during definitional equality tests ([#11480](https://github.com/leanprover/lean4/pull/11480));

- Support for heterogeneous constructor injectivity ([#11491](https://github.com/leanprover/lean4/pull/11491));

- Support for the `LawfulOfScientific` class ([#11331](https://github.com/leanprover/lean4/pull/11331));

- Syntax `use [ns Foo]` and `instantiate only [ns Foo]` inside a `grind` tactic block,
  which has the effect of activating all grind patterns scoped to that
  namespace ([#11335](https://github.com/leanprover/lean4/pull/11335));

- New `grind_pattern` constraints ([#11405](https://github.com/leanprover/lean4/pull/11405) and
  [#11409](https://github.com/leanprover/lean4/pull/11409)).

### Well-Founded Recursion on `Nat`

Definitions that use well-founded recursion are generally irreducible.
With [#7965](https://github.com/leanprover/lean4/pull/7965), when the termination measure is of type `Nat`,
such definitions can be reduced, and an explicit `@[semireducible]` annotation is accepted
without the usual warning.

### Library Highlights

This release completes the revision of the `String` API, including dependently typed `String.Pos`,
full API support for `String.Slice`, and iterators using the new `Iterator` API.
There are also many additions to the `TreeMap`/`HashMap` API, including intersection, difference, and equality.

These updates include some **breaking changes**, namely:

- [#11180](https://github.com/leanprover/lean4/pull/11180) redefines `String.take` and variants to operate on
  `String.Slice`. While previously functions returning a substring of the
  input sometimes returned `String` and sometimes returned
  `Substring.Raw`, they now uniformly return `String.Slice`.

  This is a breaking change, because many functions now have a different
  return type. So for example, if `s` is a string and `f` is a function
  accepting a string, `f (s.drop 1)` will no longer compile because
  `s.drop 1` is a `String.Slice`. To fix this, insert a call to `copy` to
  restore the old behavior: `f (s.drop 1).copy`.

  Of course, in many cases, there will be more efficient options. For
  example, don't write `f <| s.drop 1 |>.copy |>.dropEnd 1 |>.copy`, write
  `f <| s.drop 1 |>.dropEnd 1 |>.copy` instead. Also, instead of `(s.drop
  1).copy = "Hello"`, write `s.drop 1 == "Hello".toSlice` instead.

- [#11446](https://github.com/leanprover/lean4/pull/11446) moves many constants of the iterator API from `Std.Iterators` to
  the `Std` namespace in order to make them more convenient to use. These
  constants include, but are not limited to, `Iter`, `IterM` and
  `IteratorLoop`. This is a breaking change. If something breaks, try
  adding `open Std` in order to make these constants available again. If
  some constants in the `Std.Iterators` namespace cannot be found, they
  can be found directly in `Std` now.

### Breaking Changes

- [#11474](https://github.com/leanprover/lean4/pull/11474) generalizes the `noConfusion` constructions to heterogeneous
  equalities (assuming propositional equalities between the indices). This
  lays ground work for better support for applying injection to
  heterogeneous equalities in grind.
  This is a breaking change for whoever uses the `noConfusion` principle
  manually and explicitly for a type with indices.

- [11562](https://github.com/leanprover/lean4/pull/11562) makes the `noConfusion` principles even more heterogeneous, by
  allowing not just indices but also parameters to differ.
  This is a breaking change for manual use of `noConfusion` for types with parameters.
  Pass suitable `rfl` arguments, and use `eq_of_heq` on the resulting equalities as needed.

- [#11490](https://github.com/leanprover/lean4/pull/11490) prevents `try` swallowing heartbeat errors from nested `simp`
  calls, and more generally ensures the `isRuntime` flag is propagated by
  `throwNestedTacticEx`. This prevents the behavior of proofs (especially
  those using `aesop`) being affected by the current recursion depth or
  heartbeat limit.
  This breaks a single caller in Mathlib where `simp` uses a lemma of the
  form `x = f (g x)` and stack overflows, which can be fixed by
  generalizing over `g x`.

## Language

* [#7965](https://github.com/leanprover/lean4/pull/7965) lets recursive functions defined by well-founded recursion use a
  different `fix` function when the termination measure is of type `Nat`.
  This fix-point operator use structural recursion on “fuel”, initialized
  by the given measure, and is thus reasonable to reduce, e.g. in `by
  decide` proofs.

* [#11196](https://github.com/leanprover/lean4/pull/11196) avoids match splitter calculation from testing all quadratically
  many pairs of alternatives for overlaps, by keeping track of possible
  overlaps during matcher calculation, storing that information in the
  `MatcherInfo`, and using that during matcher calculation.

* [#11200](https://github.com/leanprover/lean4/pull/11200) changes how sparse case expressions represent the
  none-of-the-above information. Instead of many `x.ctorIdx ≠ i`
  hypotheses, it introduces a single `Nat.hasNotBit mask x.ctorIdx`
  hypothesis which compresses that information into a bitmask. This avoids
  a quadratic overhead during splitter generation, where all n assumptions
  would be refined through `.subst` and `.cases` constructions for all n
  assumption of the splitter alternative.

* [#11221](https://github.com/leanprover/lean4/pull/11221) lets `realizeConst` use `withDeclNameForAuxNaming` so that
  auxiliary definitions created there get non-clashing names.

* [#11222](https://github.com/leanprover/lean4/pull/11222) implements `elabToSyntax` for creating scoped syntax `s :
  Syntax` for an arbitrary elaborator `el : Option Expr -> TermElabM Expr`
  such that `elabTerm s = el`.

* [#11236](https://github.com/leanprover/lean4/pull/11236) extracts two modules from `Match.MatchEqs`, in preparation of
  #11220
  and to use the module system to draw clear boundaries between concerns
  here.

* [#11239](https://github.com/leanprover/lean4/pull/11239) adds a `Unit` assumption to alternatives of the splitter that
  would otherwise not have arguments. This fixes #11211.

* [#11245](https://github.com/leanprover/lean4/pull/11245) improves the error message encountered in the case of a type
  class instance resolution failure, and adds an error explanation that
  discusses the common new-user case of binary operation overloading and
  points to the `trace.Meta.synthInstance` option for advanced debugging.

* [#11256](https://github.com/leanprover/lean4/pull/11256) replaces `MatcherInfo.numAltParams` with a more detailed data
  structure that allows us, in particular, to distinguish between an
  alternative for a constructor with a `Unit` field and the alternative
  for a nullary constructor, where an artificial `Unit` argument is
  introduced.

* [#11261](https://github.com/leanprover/lean4/pull/11261) continues the homogenization between matchers and splitters,
  following up on #11256. In particular it removes the ambiguity whether
  `numParams` includes the `discrEqns` or not.

* [#11269](https://github.com/leanprover/lean4/pull/11269) adds support for decidable equality of empty lists and empty
  arrays. Decidable equality for lists and arrays is suitably modified so
  that all diamonds are definitionally equal.

* [#11292](https://github.com/leanprover/lean4/pull/11292) adds intersection operation on
  `ExtDTreeMap`/`ExtTreeMap`/`ExtTreeSet` and proves several lemmas about
  it.

* [#11301](https://github.com/leanprover/lean4/pull/11301) allows setting reducibilityCoreExt in async contexts (e.g. when
  using `mkSparseCasesOn` in a realizable definition)

* [#11302](https://github.com/leanprover/lean4/pull/11302) renames the CTests tests to use filenames as test names. So
  instead of
  ```
          2080 - leanruntest_issue5767.lean (Failed)
  ```
  we get
  ```
          2080 - tests/lean/run/issue5767.lean (Failed)
  ```
  which allows Ctrl-Click’ing on them in the VSCode terminal.

* [#11303](https://github.com/leanprover/lean4/pull/11303) renames rename wrongly named `backwards.` options to
  `backward.`

* [#11304](https://github.com/leanprover/lean4/pull/11304) documents that `backward.*` options are only temporary
  migration aids and may disappear without further notice after 6 months
  after their introduction. Users are kindly asked to report if they rely
  on these options.

* [#11305](https://github.com/leanprover/lean4/pull/11305) removes the `group` field from option descriptions. It is
  unused, does not have a clear meaning and often matches the first
  component of the option name.

* [#11307](https://github.com/leanprover/lean4/pull/11307) removes all code that sets the `Option.Decl.group` field, which
  is unused and has no clearly documented meaning.

* [#11325](https://github.com/leanprover/lean4/pull/11325) adds `CoreM.toIO'`, the analogue of `CoreM.toIO` dropping the
  state from the return type, and similarly for `TermElabM.toIO'` and
  `MetaM.toIO'`.

* [#11333](https://github.com/leanprover/lean4/pull/11333) adds infrastructure for parallel execution across Lean's tactic
  monads.

* [#11338](https://github.com/leanprover/lean4/pull/11338) upstreams the `with_weak_namespace` command from Mathlib:
  `with_weak_namespace <id> <cmd>` changes the current namespace to `<id>`
  for the duration of executing command `<cmd>`, without causing scoped
  things to go out of scope. This is in preparation for upstreaming the
  `scoped[Foo.Bar]` syntax from Mathlib, which will be useful now that we
  are adding `grind` annotations in scopes.

* [#11346](https://github.com/leanprover/lean4/pull/11346) modifies the error message for type synthesis failure for the
  case where the type class in question is potentially derivable using a
  `deriving` command. Also changes the error explanation for type class
  instance synthesis failure with an illustration of this pattern.

* [#11347](https://github.com/leanprover/lean4/pull/11347) adds a focused error explanation aimed at the case where someone
  tries to use Natural-Numbers-Game-style `induction` proofs directly in
  Lean, where such proofs are not syntactically valid.

* [#11353](https://github.com/leanprover/lean4/pull/11353) applies beta reduction to specialization keys, allowing us to
  reuse specializations in more situations.

* [#11379](https://github.com/leanprover/lean4/pull/11379) sets `@[macro_inline]` on the (trivial) `.ctorIdx` for inductive
  types with one constructor, to reduce the number of symbols generated by
  the compiler.

* [#11385](https://github.com/leanprover/lean4/pull/11385) lets implicit instance names avoid name clashes with private
  declarations. This fixes #10329.

* [#11408](https://github.com/leanprover/lean4/pull/11408) adds a difference operation on
  `ExtDTreeMap`/`ExtTreeMap`/`TreeSet` and proves several lemmas about it.

* [#11422](https://github.com/leanprover/lean4/pull/11422) uses a kernel-reduction optimized variant of `Mon.mul` in `grind`.

* [#11425](https://github.com/leanprover/lean4/pull/11425) changes `Lean.Order.CCPO` and `.CompleteLattice` to carry a
  Prop. This avoids the `CCPO IO` instance from being `noncomputable`.

* [#11432](https://github.com/leanprover/lean4/pull/11432) fixes a typo in the docstring of `#guard_mgs`.

* [#11453](https://github.com/leanprover/lean4/pull/11453) fixes undefined behavior where `delete` (instead of `delete[]`)
  is called on an object allocated with `new[]`.

* [#11456](https://github.com/leanprover/lean4/pull/11456) refines several error messages, mostly involving invalid
  use of field notation, generalized field notation, and numeric
  projection. Provides a new error explanation for field notation.

* [#11463](https://github.com/leanprover/lean4/pull/11463) fixes a panic in `getEqnsFor?` when called on matchers generated
  from match expressions in theorem types.

* [#11474](https://github.com/leanprover/lean4/pull/11474) generalizes the `noConfusion` constructions to heterogeneous
  equalities (assuming propositional equalities between the indices). This
  lays ground work for better support for applying injection to
  heterogeneous equalities in grind.

* [#11476](https://github.com/leanprover/lean4/pull/11476) adds a `` {givenInstance}`C` `` documentation role that adds an
  instance of `C` to the document's local assumptions.

* [#11482](https://github.com/leanprover/lean4/pull/11482) gives suggestions based on the currently-available constants
  when projecting from an unknown type.

* [#11485](https://github.com/leanprover/lean4/pull/11485) ensures that `Nat`s in `.olean` files use a deterministic
  serialization in the case where `LEAN_USE_GMP` is not set.

* [#11490](https://github.com/leanprover/lean4/pull/11490) prevents `try` swallowing heartbeat errors from nested `simp`
  calls, and more generally ensures the `isRuntime` flag is propagated by
  `throwNestedTacticEx`. This prevents the behavior of proofs (especially
  those using `aesop`) being affected by the current recursion depth or
  heartbeat limit.

* [#11492](https://github.com/leanprover/lean4/pull/11492) uses the helper functions withImplicitBinderInfos and
  mkArrowN in more places.

* [#11493](https://github.com/leanprover/lean4/pull/11493) makes `Match.MatchEqs` a leaf module, to be less restricted in
  which features we can use there.

* [#11502](https://github.com/leanprover/lean4/pull/11502) adds two benchmarks for elaborating match statements of many
  `Nat` literals, one without and one with splitter generation.

* [#11508](https://github.com/leanprover/lean4/pull/11508) avoids generating hyps when not needed (i.e. if there is a
  catch-all so no completeness checking needed) during matching on values.

  This tweak was made possible by #11220.

* [#11510](https://github.com/leanprover/lean4/pull/11510) avoids running substCore twice in caseValues.

* [#11511](https://github.com/leanprover/lean4/pull/11511) implements a linter that warns when a deprecated coercion is
  applied. It also warns when the `Option` coercion or the
  `Subarray`-to-`Array` coercion is used in `Init` or `Std`. The linter is
  currently limited to `Coe` instances; `CoeFun` instances etc. are not
  considered.

* [#11518](https://github.com/leanprover/lean4/pull/11518) provides an additional hint when the type of an autobound
  implicit is required to have function type or equality type — this
  fails, and the existing error message does not address the fact that the
  source of the error is an unknown identifier that was automatically
  bound.

* [#11541](https://github.com/leanprover/lean4/pull/11541) adds support for underscores as digit separators in
  String.toNat?, String.toInt?, and related parsing functions. This makes
  the string parsing functions consistent with Lean's numeric literal
  syntax, which already supports underscores for readability (e.g.,
  100_000_000).

* [#11554](https://github.com/leanprover/lean4/pull/11554) adds `@[suggest_for]` annotations to Lean, allowing lean to
  provide corrections for `.every` or `.some` methods in place of `.all`
  or `.any` methods for most default-imported types (arrays, lists,
  strings, substrings, and subarrays, and vectors).

* [#11555](https://github.com/leanprover/lean4/pull/11555) scans the environment for viable replacements for a dotted
  identifier (like `.zero`) and suggests concrete alternatives as
  replacements.

* [#11562](https://github.com/leanprover/lean4/pull/11562) makes the `noConfusion` principles even more heterogeneous, by
  allowing not just indices but also parameters to differ.

* [#11566](https://github.com/leanprover/lean4/pull/11566) lets the compiler treat per-constructor `noConfusion` like the
  general one, and moves some more logic closer to no confusion
  generation.

* [#11571](https://github.com/leanprover/lean4/pull/11571) lets `whnf` not consult `isNoConfusion`, to speed up this hot
  path a bit.

* [#11587](https://github.com/leanprover/lean4/pull/11587) adjusts the new `meta` keyword of the experimental module system
  not to imply `partial` for general consistency.

* [#11607](https://github.com/leanprover/lean4/pull/11607) makes argument-less tactic invocations of `Std.Do` tactics such
  as `mintro` emit a proper error message "`mintro` expects at least one
  pattern" instead of claiming that `Std.Tactic.Do` needs to be imported.

* [#11611](https://github.com/leanprover/lean4/pull/11611) fixes a `noConfusion` compilation introduced by #11562.

* [#11619](https://github.com/leanprover/lean4/pull/11619) allows Lean to present suggestions based on `@[suggest_for]`
  annotations for unknown identifiers without internal dots. (The
  annotations in #11554 only gave suggestion for dotted identifiers like
  `Array.every`->`Array.all` and not for bare identifiers like
  `Result`->`Except` or `ℕ`->`Nat`.)

* [#11620](https://github.com/leanprover/lean4/pull/11620) ports Batteries.WF to Init.WFC for executable well-founded
  fixpoints. It introduces `csimp` theorems to replace the recursors and
  non-executable definitions with executable definitions.

* [#11621](https://github.com/leanprover/lean4/pull/11621) causes Lean to search through `@[suggest_for]` annotations on
  certain errors that look like unknown identifiers that got incorrectly
  autobound. This will correctly identify that a declaration of type
  `Maybe String` should be `Option String` instead.

* [#11624](https://github.com/leanprover/lean4/pull/11624) fixes a SIGFPE crash on x86_64 when evaluating `INT_MIN / -1` or
  `INT_MIN % -1` for signed integer types.

* [#11637](https://github.com/leanprover/lean4/pull/11637) declares the module system as no longer experimental and makes
  the `experimental.module` option a no-op, to be removed.

* [#11644](https://github.com/leanprover/lean4/pull/11644) makes `.ctorIdx` not an abbrev; we don't want `grind` to unfold
  it.

* [#11645](https://github.com/leanprover/lean4/pull/11645) fixes the docstring of `propagateForallPropUp`. It was
  copy’n’pasta before.

* [#11652](https://github.com/leanprover/lean4/pull/11652) teaches `grind` how to reduce `.ctorIdx` applied to
  constructors. It can also handle tasks like
  ```
  xs ≍ Vec.cons x xs' → xs.ctorIdx = 1
  ```
  thanks to a `.ctorIdx.hinj` theorem (generated on demand).

* [#11657](https://github.com/leanprover/lean4/pull/11657) improves upon #11652 by keeping the kernel-reduction-optimized
  definition.

## Library

* [#8406](https://github.com/leanprover/lean4/pull/8406) adds lemmas of the form `getElem_swapIfInBounds*` and deprecates
  `getElem_swap'`.

* [#9302](https://github.com/leanprover/lean4/pull/9302) modifies `Option.instDecidableEq` and `Option.decidableEqNone`
  so that the latter can be made into a global instance without causing
  diamonds. It also adds `Option.decidableNoneEq`.

* [#10204](https://github.com/leanprover/lean4/pull/10204) changes the interface of the `ForIn`, `ForIn'`, and `ForM`
  type classes to not take a `Monad m` parameter. This is a breaking change
  for most downstream `instance`s, which will now need to assume
  `[Monad m]`.

* [#10945](https://github.com/leanprover/lean4/pull/10945) adds `Std.Tricho r`, a type class for relations which identifies
  them as trichotomous. This is preferred to `Std.Antisymm (¬ r · ·)` in
  all cases (which it is equivalent to).

* [#11038](https://github.com/leanprover/lean4/pull/11038) introduces a new fixpoint combinator,
  `WellFounded.extrinsicFix`. A termination proof, if provided at all, can
  be given extrinsically, i.e., looking at the term from the outside, and
  is only required if one intends to formally verify the behavior of the
  fixpoint. The new combinator is then applied to the iterator API.
  Consumers such as `toList` or `ForIn` no longer require a proof that the
  underlying iterator is finite. If one wants to ensure the termination of
  them intrinsically, there are strictly terminating variants available
  as, for example, `it.ensureTermination.toList` instead of `it.toList`.

* [#11112](https://github.com/leanprover/lean4/pull/11112) adds intersection operation on `DHashMap`/`HashMap`/`HashSet`
  and provides several lemmas about its behaviour.

* [#11141](https://github.com/leanprover/lean4/pull/11141) provides a polymorphic `ForIn` instance for slices and an MPL
  `spec` lemma for the iteration over slices using `for ... in`. It also
  provides a version specialized to `Subarray`.

* [#11165](https://github.com/leanprover/lean4/pull/11165) provides intersection on `DTreeMap`/`TreeMap`/`TreeSet`and
  provides several lemmas about it.

* [#11178](https://github.com/leanprover/lean4/pull/11178) provides more lemmas about `Subarray` and `ListSlice` and it
  also adds support for subslices of these two types of slices.

* [#11180](https://github.com/leanprover/lean4/pull/11180) redefines `String.take` and variants to operate on
  `String.Slice`. While previously functions returning a substring of the
  input sometimes returned `String` and sometimes returned
  `Substring.Raw`, they now uniformly return `String.Slice`.

* [#11212](https://github.com/leanprover/lean4/pull/11212) adds support for difference operation for
  `DHashMap`/`HashMap`/`HashSet` and proves several lemmas about it.

* [#11218](https://github.com/leanprover/lean4/pull/11218) renames `String.offsetOfPos` to `String.Pos.Raw.offsetOfPos` to
  align with the other `String.Pos.Raw` operations.

* [#11222](https://github.com/leanprover/lean4/pull/11222) implements `elabToSyntax` for creating scoped syntax `s :
  Syntax` for an arbitrary elaborator `el : Option Expr -> TermElabM Expr`
  such that `elabTerm s = el`.

* [#11223](https://github.com/leanprover/lean4/pull/11223) adds missing lemmas relating `emptyWithCapacity`/`empty` and
  `toList`/`keys`/`values` for `DHashMap`/`HashMap`/`HashSet`.

* [#11231](https://github.com/leanprover/lean4/pull/11231) adds several lemmas that relate
  `getMin`/`getMin?`/`getMin!`/`getMinD` and insertion to the empty
  (D)TreeMap/TreeSet and their extensional variants.

* [#11232](https://github.com/leanprover/lean4/pull/11232) deprecates `String.toSubstring` in favor of
  `String.toRawSubstring` (cf. #11154).

* [#11235](https://github.com/leanprover/lean4/pull/11235) registers a node kind for `Lean.Parser.Term.elabToSyntax` in
  order to support the `Lean.Elab.Term.elabToSyntax` functionality without
  registering a dedicated parser for user-accessible syntax.

* [#11237](https://github.com/leanprover/lean4/pull/11237) fixes the error thrown by `UInt64.fromJson?` and
  `USize.fromJson?` to use the missing `s!`.

* [#11240](https://github.com/leanprover/lean4/pull/11240) renames `String.ValidPos` to `String.Pos`, `String.endValidPos`
  to `String.endPos` and `String.startValidPos` to `String.startPos`.

* [#11241](https://github.com/leanprover/lean4/pull/11241) provides intersection operation for
  `ExtDHashMap`/`ExtHashMap`/`ExtHashSet` and proves several lemmas about
  it.

* [#11242](https://github.com/leanprover/lean4/pull/11242) significantly changes the signature of the `ToIterator` type
  class. The obtained iterators' state is no longer dependently typed and
  is an `outParam` instead of being bundled inside the class. Among other
  benefits, `simp` can now rewrite inside of `Slice.toList` and
  `Slice.toArray`. The downside is that we lose flexibility. For example,
  the former combinator-based implementation of `Subarray`'s iterators is
  no longer feasible because the states are dependently typed. Therefore,
  this PR provides a hand-written iterator for `Subarray`, which does not
  require a dependently typed state and is faster than the previous one.

* [#11243](https://github.com/leanprover/lean4/pull/11243) adds `ofArray` to `DHashMap`/`HashMap`/`HashSet` and proves a
  simp lemma allowing to rewrite `ofArray` to `ofList`.

* [#11250](https://github.com/leanprover/lean4/pull/11250) introduces a function `String.split` which is based on
  `String.Slice.split` and therefore supports all pattern types and
  returns a `Std.Iter String.Slice`.

* [#11255](https://github.com/leanprover/lean4/pull/11255) reduces the allocations when using string patterns. In
  particular
  `startsWith`, `dropPrefix?`, `endsWith`, `dropSuffix?` are optimized.

* [#11263](https://github.com/leanprover/lean4/pull/11263) fixes several memory leaks in the new `String` API.

* [#11266](https://github.com/leanprover/lean4/pull/11266) adds `BEq` instance for `DHashMap`/`HashMap`/`HashSet` and their
  extensional variants and proves lemmas relating it to the equivalence of
  hashmaps/equality of extensional variants.

* [#11267](https://github.com/leanprover/lean4/pull/11267) renames congruence lemmas for union on
  `DHashMap`/`HashMap`/`HashSet`/`DTreeMap`/`TreeMap`/`TreeSet` to fit the
  convention of being in the `Equiv` namespace.

* [#11276](https://github.com/leanprover/lean4/pull/11276) cleans up the API around `String.find` and moves it uniformly to
  the new position types `String.ValidPos` and `String.Slice.Pos`

* [#11281](https://github.com/leanprover/lean4/pull/11281) adds a few deprecations for functions that never existed but
  that are still helpful for people migrating their code post-#11180.

* [#11282](https://github.com/leanprover/lean4/pull/11282) adds the alias `String.Slice.any` for `String.Slice.contains`.

* [#11285](https://github.com/leanprover/lean4/pull/11285) adds `Std.Slice.Pattern` instances for `p : Char -> Prop` as
  long as `DecidablePred p`, to allow things like `"hello".dropWhile (· =
  'h')`.

* [#11286](https://github.com/leanprover/lean4/pull/11286) adds a function `String.Slice.length`, with the following
  deprecation string: There is no constant-time length function on slices.
  Use `s.positions.count` instead, or `isEmpty` if you only need to know
  whether the slice is empty.

* [#11289](https://github.com/leanprover/lean4/pull/11289) redefines `String.foldl`, `String.isNat` to use their
  `String.Slice` counterparts.

* [#11290](https://github.com/leanprover/lean4/pull/11290) renames `String.replaceStartEnd` to `String.slice`,
  `String.replaceStart` to `String.sliceFrom`, and `String.replaceEnd` to
  `String.sliceTo`, and similar for the corresponding functions on
  `String.Slice`.

* [#11299](https://github.com/leanprover/lean4/pull/11299) add many `@[grind]` annotations for `Fin`, and updates the
  tests.

* [#11308](https://github.com/leanprover/lean4/pull/11308) redefines `front` and `back` on `String` to go through
  `String.Slice` and adds the new `String` functions `front?`, `back?`,
  `positions`, `chars`, `revPositions`, `revChars`, `byteIterator`,
  `revBytes`, `lines`.

* [#11316](https://github.com/leanprover/lean4/pull/11316) adds `grind_pattern Exists.choose_spec => P.choose`.

* [#11317](https://github.com/leanprover/lean4/pull/11317) adds `grind_pattern Subtype.property => self.val`.

* [#11321](https://github.com/leanprover/lean4/pull/11321) provides specialized lemmas about `Nat` ranges, including `simp`
  annotations and induction principles for proving properties for all
  ranges.

* [#11327](https://github.com/leanprover/lean4/pull/11327) adds two lemmas to prove `a / c < b / c`.

* [#11341](https://github.com/leanprover/lean4/pull/11341) adds a coercion from `String` to `String.Slice`.

* [#11343](https://github.com/leanprover/lean4/pull/11343) renames `String.bytes` to `String.toByteArray`.

* [#11354](https://github.com/leanprover/lean4/pull/11354) adds simple lemmas that show that searching from a position in a
  string returns something that is at least that position.

* [#11357](https://github.com/leanprover/lean4/pull/11357) updates the `foldr`, `all`, `any` and `contains` functions on
  `String` to be defined in terms of their `String.Slice` counterparts.

* [#11358](https://github.com/leanprover/lean4/pull/11358) adds `String.Slice.toInt?` and variants.

* [#11376](https://github.com/leanprover/lean4/pull/11376) aims to improve the performance of `String.contains`,
  `String.find`, etc. when using patterns of type `Char` or `Char -> Bool`
  by moving the needle out of the iterator state and thus working around
  missing unboxing in the compiler.

* [#11380](https://github.com/leanprover/lean4/pull/11380) renames `String.Slice.Pos.ofSlice` to `String.Pos.ofToSlice` to
  adhere with the (yet-to-be documented) naming convention for mapping
  positions to positions. It then adds several new functions so that for
  every way to construct a slice from a string and slice, there are now
  functions for mapping positions forwards and backwards along this
  construction.

* [#11384](https://github.com/leanprover/lean4/pull/11384) adds the necessary instances for `grind` to reason about
  `String.Pos.Raw`, `String.Pos` and `String.Slice.Pos`.

* [#11399](https://github.com/leanprover/lean4/pull/11399) adds support for the difference operation for
  `ExtDHashMap`/`ExtHashMap`/`ExtHashSet` and proves several lemmas about
  it.

* [#11404](https://github.com/leanprover/lean4/pull/11404) adds BEq instance for `DTreeMap`/`TreeMap`/`TreeSet` and their
  extensional variants and proves lemmas relating it to the equivalence of
  hashmaps/equality of extensional variants.

* [#11407](https://github.com/leanprover/lean4/pull/11407) adds the difference operation on `DTreeMap`/`TreeMap`/`TreeSet`
  and proves several lemmas about it.

* [#11421](https://github.com/leanprover/lean4/pull/11421) adds decidable equality to `DHashMap`/`HashMap`/`HashSet` and
  their extensional variants.

* [#11439](https://github.com/leanprover/lean4/pull/11439) performs minor maintenance on the String API

* [#11448](https://github.com/leanprover/lean4/pull/11448) moves the `Inhabited` instances in constant `DTreeMap` (and
  related) queries, such as `Const.get!`, where the `Inhabited` instance
  can be provided before proving a key.

* [#11452](https://github.com/leanprover/lean4/pull/11452) adds lemmas stating that if a get operation returns a value,
  then the queried key must be contained in the collection. These lemmas
  are added for HashMap and TreeMap-based collections, with a similar
  lemma also added for `Init.getElem`.

* [#11465](https://github.com/leanprover/lean4/pull/11465) fixes various typos across the codebase in documentation and
  comments.

* [#11503](https://github.com/leanprover/lean4/pull/11503) marks `Char -> Bool` patterns as default instances for string
  search. This means that things like `" ".find (·.isWhitespace)` can now
  be elaborated without error.

* [#11521](https://github.com/leanprover/lean4/pull/11521) fixes a segmentation fault that was triggered when initializing
  a new timer and a reset was called at the same time.

* [#11527](https://github.com/leanprover/lean4/pull/11527) adds decidable equality to `DTreeMap`/`TreeMap`/`TreeSet` and
  their extensional variants.

* [#11528](https://github.com/leanprover/lean4/pull/11528) adds lemmas relating `minKey?` and `min?` on the keys list for
  all `DTreeMap` and other containers derived from it.

* [#11542](https://github.com/leanprover/lean4/pull/11542) removes `@[grind =]` from `List.countP_eq_length_filter` and
  `Array.countP_eq_size_filter`, as users reported this was problematic.

* [#11548](https://github.com/leanprover/lean4/pull/11548) adds `Lean.ToJson` and `Lean.FromJson` instances for
  `String.Slice`.

* [#11565](https://github.com/leanprover/lean4/pull/11565) adds lemmas that relate `insert`/`insertIfNew` and `toList` on
  `DTreeMap`/`DHashMap`-derived containers.

* [#11574](https://github.com/leanprover/lean4/pull/11574) adds a lemma that the cast of a natural number into any ordered
  ring is non-negative. We can't annotate this directly for `grind`, but
  will probably add this to `grind`'s linarith internals.

* [#11578](https://github.com/leanprover/lean4/pull/11578) refactors the usage of `get` operation on
  `HashMap`/`TreeMap`/`ExtHashMap`/`ExtTreeMap` to `getElem` instance.

* [#11591](https://github.com/leanprover/lean4/pull/11591) adds missing lemmas about how `ReaderT.run`, `OptionT.run`,
  `StateT.run`, and `ExceptT.run` interact with `MonadControl` operations.

* [#11596](https://github.com/leanprover/lean4/pull/11596) adds `@[suggest_for ℤ]` on `Int` and `@[suggest_for ℚ]` on
  `Rat`, following the pattern established by `@[suggest_for ℕ]` on `Nat`
  in #11554.

* [#11600](https://github.com/leanprover/lean4/pull/11600) adds a few lemmas about `EStateM.run` on basic operations.

* [#11625](https://github.com/leanprover/lean4/pull/11625) adds `@[expose]` to `decidable_of_bool` so that
  proofs-by-`decide` elsewhere that reduce to `decidable_of_bool` continue
  to reduce.

* [#11654](https://github.com/leanprover/lean4/pull/11654) updates the `grind` docstring. It was still mentioning `cutsat`
  which has been renamed to `lia`. This issue was reported during ItaLean.

## Tactics

* [#11226](https://github.com/leanprover/lean4/pull/11226) finally removes the old `grind` framework `SearchM`. It has been
  replaced with the new `Action` framework.

* [#11244](https://github.com/leanprover/lean4/pull/11244) fixes minor issues in `grind`. In preparation for adding `grind
  -revert`.

* [#11247](https://github.com/leanprover/lean4/pull/11247) fixes an issue in the `grind` preprocessor. `simp` may introduce
  assigned (universe) metavariables (e.g., when performing
  zeta-reduction).

* [#11248](https://github.com/leanprover/lean4/pull/11248) implements the option `revert`, which is set to `false` by
  default. To recover the old `grind` behavior, you should use `grind
  +revert`. Previously, `grind` used the `RevSimpIntro` idiom, i.e., it
  would revert all hypotheses and then re-introduce them while simplifying
  and applying eager `cases`. This idiom created several problems:

  * Users reported that `grind` would include unnecessary parameters. See
  [here](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Grind.20aggressively.20includes.20local.20hypotheses.2E/near/554887715).
  * Unnecessary section variables were also being introduced. See the new
  test contributed by Sebastian Graf.
  * Finally, it prevented us from supporting arbitrary parameters as we do
  in `simp`. In `simp`, I implemented a mechanism that simulates local
  universe-polymorphic theorems, but this approach could not be used in
  `grind` because there is no mechanism for reverting (and re-introducing)
  local universe-polymorphic theorems. Adding such a mechanism would
  require substantial work: I would need to modify the local context
  object. I considered maintaining a substitution from the original
  variables to the new ones, but this is also tricky, because the mapping
  would have to be stored in the `grind` goal objects, and it is not just
  a simple mapping. After reverting everything, I would need to keep a
  sequence of original variables that must be added to the mapping as we
  re-introduce them, but eager case splits complicate this quite a bit.
  The whole approach felt overly messy.

* [#11265](https://github.com/leanprover/lean4/pull/11265) marks the automatically generated `sizeOf` theorems as `grind`
  theorems.

* [#11268](https://github.com/leanprover/lean4/pull/11268) implements support for arbitrary `grind` parameters. The feature
  is similar to the one available in `simp`, where a proof term is treated
  as a local universe-polymorphic lemma. This feature relies on `grind
  -revert` (see #11248). For example, users can now write:

  ```lean
  def snd (p : α × β) : β := p.2
  theorem snd_eq (a : α) (b : β) : snd (a, b) = b := rfl

* [#11273](https://github.com/leanprover/lean4/pull/11273) fixes a bug during proof construction in `grind`.

* [#11295](https://github.com/leanprover/lean4/pull/11295) fixes a bug in the propagation rules for `ite` and `dite` used
  in `grind`. The bug prevented equalities from being propagated to the
  satellite solvers. Here is an example affected by this issue.

* [#11315](https://github.com/leanprover/lean4/pull/11315) fixes an issue affecting `grind -revert`. In this mode, assigned
  metavariables in hypotheses were not being instantiated. This issue was
  affecting two files in Mathlib.

* [#11318](https://github.com/leanprover/lean4/pull/11318) fixes a local declaration internalization in `grind` that was
  exposed when using `grind -revert`. This bug was affecting a `grind`
  proof in Mathlib.

* [#11319](https://github.com/leanprover/lean4/pull/11319) improves the support for `Fin n` in `grind` when `n` is not a
  numeral.

* [#11323](https://github.com/leanprover/lean4/pull/11323) introduces a new `grind` option, `funCC` (enabled by default),
  which extends congruence closure to *function-valued* equalities. When
  `funCC` is enabled, `grind` tracks equalities of **partially applied
  functions**, allowing reasoning steps such as:
  ```lean
  a : Nat → Nat
  f : (Nat → Nat) → (Nat → Nat)
  h : f a = a
  ⊢ (f a) m = a m

* [#11326](https://github.com/leanprover/lean4/pull/11326) ensures that users can provide `grind` proof parameters whose
  types are not `forall`-quantified. Examples:

  ```lean
  opaque f : Nat → Nat
  axiom le_f (a : Nat) : a ≤ f a

* [#11330](https://github.com/leanprover/lean4/pull/11330) renames the `cutsat` tactic to `lia` for better alignment with
  standard terminology in the theorem proving community.

* [#11331](https://github.com/leanprover/lean4/pull/11331) adds support for the `LawfulOfScientific` class in `grind`.
  Examples:
  ```lean
  open Lean Grind Std
  variable [LE α] [LT α] [LawfulOrderLT α] [Field α] [OfScientific α]
           [LawfulOfScientific α] [IsLinearOrder α] [OrderedRing α]
  example : (2 / 3 : α) ≤ (0.67 : α) := by  grind
  example : (1.2 : α) ≤ (1.21 : α) := by grind
  example : (2 / 3 : α) ≤ (67 / 100 : α) := by grind
  example : (1.2345 : α) ≤ (1.2346 : α) := by grind
  example : (2.3 : α) ≤ (4.5 : α) := by grind
  example : (2.3 : α) ≤ (5/2 : α) := by grind
  ```

* [#11332](https://github.com/leanprover/lean4/pull/11332) adds a `grind_annotated "YYYY-MM-DD"` command that marks files
  as manually annotated for grind.

* [#11334](https://github.com/leanprover/lean4/pull/11334) adds an explicit normalization layer for ring constraints in the
  `grind linarith` module. For example, it will be used to clean up
  denominators when the ring is a field.

* [#11335](https://github.com/leanprover/lean4/pull/11335) enables the syntax `use [ns Foo]` and `instantiate only [ns
  Foo]` inside a `grind` tactic block, and has the effect of activating
  all grind patterns scoped to that namespace. We can use this to
  implement specialized tactics using `grind`, but only controlled subsets
  of theorems.

* [#11348](https://github.com/leanprover/lean4/pull/11348) activates the `grind_annotated` command in
  `Init.Data.List.Lemmas` by removing the TODO comment and uncommenting
  the command.

* [#11350](https://github.com/leanprover/lean4/pull/11350) implements a helper simproc for `grind`. It is part of the
  infrastructure used to cleanup denominators in `grind linarith`.

* [#11365](https://github.com/leanprover/lean4/pull/11365) enables parallelism in `try?`. Currently, we replace the
  `attempt_all` stages (there are two, one for builtin tactics including
  `grind` and `simp_all`, and a second one for all user extensions) with
  parallel versions. We do not (yet?) change the behaviour of `first`
  based stages.

* [#11373](https://github.com/leanprover/lean4/pull/11373) makes the library suggestions extension state available when
  importing from `module` files.

* [#11375](https://github.com/leanprover/lean4/pull/11375) adds support for cleaning up denominators in `grind linarith`
  when the type is a `Field`.

* [#11391](https://github.com/leanprover/lean4/pull/11391) implements new kinds of constraints for the `grind_pattern`
  command. These constraints allow users to control theorem instantiation
  in `grind`.
  It requires a manual `update-stage0` because the change affects the
  `.olean` format, and the PR fails without it.

* [#11396](https://github.com/leanprover/lean4/pull/11396) changes `set_library_suggestions` to create an auxiliary
  definition marked with `@[library_suggestions]`, rather than storing
  `Syntax` directly in the environment extension. This enables better
  persistence and consistency of library suggestions across modules.

* [#11405](https://github.com/leanprover/lean4/pull/11405) implements the following `grind_pattern` constraints:
  ```lean
  grind_pattern fax => f x  where
    depth x < 2

* [#11409](https://github.com/leanprover/lean4/pull/11409) implements support for the `grind_pattern` constraints
  `is_value` and `is_strict_value`.

* [#11410](https://github.com/leanprover/lean4/pull/11410) fixes a kernel type mismatch error in grind's denominator
  cleanup feature. When generating proofs involving inverse numerals (like
  `2⁻¹`), the proof context is compacted to only include variables
  actually used. This involves renaming variable indices - e.g., if
  original indices were `{0: r, 1: 2⁻¹}` and only `2⁻¹` is used, it gets
  renamed to index 0.

* [#11412](https://github.com/leanprover/lean4/pull/11412) fixes an issue where `grind` would fail after multiple
  `norm_cast`
  calls with the error "unexpected metadata found during internalization".

* [#11428](https://github.com/leanprover/lean4/pull/11428) implements support for **guards** in `grind_pattern`. The new
  feature provides additional control over theorem instantiation. For
  example, consider the following monotonicity theorem:

  ```lean
  opaque f : Nat → Nat
  theorem fMono : x ≤ y → f x ≤ f y := ...
  ```

* [#11429](https://github.com/leanprover/lean4/pull/11429) documents the `grind_pattern` command for manually selecting
  theorem instantiation patterns, including multi-patterns and the
  constraint system (`=/=`, `=?=`, `size`, `depth`, `is_ground`,
  `is_value`, `is_strict_value`, `gen`, `max_insts`, `guard`, `check`).

* [#11462](https://github.com/leanprover/lean4/pull/11462) adds `solve_by_elim` as a fallback in the `try?` tactic's simple
  tactics. When `rfl` and `assumption` both fail but `solve_by_elim`
  succeeds (e.g., for goals requiring hypothesis chaining or
  backtracking), `try?` will now suggest `solve_by_elim`.

* [#11464](https://github.com/leanprover/lean4/pull/11464) improves the error message when no library suggestions engine is
  registered to recommend importing `Lean.LibrarySuggestions.Default` for
  the built-in engine.

* [#11466](https://github.com/leanprover/lean4/pull/11466) removes the "first pass" behavior where `exact?` and `apply?`
  would try `solve_by_elim` on the original goal before doing library
  search. This simplifies the `librarySearch` API and focuses these
  tactics on their primary purpose: finding library lemmas.

* [#11468](https://github.com/leanprover/lean4/pull/11468) adds `+suggestions` support to `solve_by_elim`, following the
  pattern established by `grind +suggestions` and `simp_all +suggestions`.

* [#11469](https://github.com/leanprover/lean4/pull/11469) adds `+grind` and `+try?` options to `exact?` and `apply?`
  tactics.

* [#11471](https://github.com/leanprover/lean4/pull/11471) fixes an incorrect reducibility setting when using `grind`
  interactive mode.

* [#11480](https://github.com/leanprover/lean4/pull/11480) adds the `grind` option `reducible` (default: `true`). When
  enabled, definitional equality tests expand only declarations marked as
  `@[reducible]`.
  Use `grind -reducible` to allow expansion of non-reducible declarations
  during definitional equality tests.
  This option affects only definitional equality; the canonicalizer and
  theorem pattern internalization always unfold reducible declarations
  regardless of this setting.

* [#11481](https://github.com/leanprover/lean4/pull/11481) fixes a bug in `grind?`. The suggestion using the `grind`
  interactive mode was dropping the configuration options provided by the
  user. In the following account, the third suggestion was dropping the
  `-reducible` option.

* [#11484](https://github.com/leanprover/lean4/pull/11484) fixes a bug in the `grind` pattern validation. The bug affected
  type classes that were propositions.

* [#11487](https://github.com/leanprover/lean4/pull/11487) adds a heterogeneous version of the constructor injectivity
  theorems. These theorems are useful for indexed families, and will be
  used in `grind`.

* [#11491](https://github.com/leanprover/lean4/pull/11491) implements heterogeneous constructor injectivity in `grind`.

* [#11494](https://github.com/leanprover/lean4/pull/11494) re-enables star-indexed lemmas as a fallback for `exact?` and
  `apply?`.

* [#11519](https://github.com/leanprover/lean4/pull/11519) marks `Nat` power and divisibility theorems for `grind`. We use
  the new `grind_pattern` constraints to control theorem instantiation.
  Examples:

  ```lean
  example {x m n : Nat} (h : x = 4 ^ (m + 1) * n) : x % 4 = 0 := by
    grind

* [#11520](https://github.com/leanprover/lean4/pull/11520) implements the constraint `not_value x` in the `grind_pattern`
  command. It is the negation of the constraint `is_value`.

* [#11522](https://github.com/leanprover/lean4/pull/11522) implements `grind` propagators for `Nat` operators that have a
  simproc associated with them, but do not have any theory solver support.
  Examples:

  ```lean
  example (a b : Nat) : a = 3 → b = 6 → a &&& b = 2 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a ||| b = 7 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a ^^^ b = 5 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a <<< b = 192 := by grind
  example (a b : Nat) : a = 1135 → b = 6 → a >>> b = 17 := by grind
  ```

* [#11547](https://github.com/leanprover/lean4/pull/11547) ensures the auxiliary definitions created by
  `register_try?_tactic` are internal implementation details that should
  not be visible to user-facing linters.

* [#11556](https://github.com/leanprover/lean4/pull/11556) adds a `+all` option to `exact?` and `apply?` that collects all
  successful lemmas instead of stopping at the first complete solution.

* [#11573](https://github.com/leanprover/lean4/pull/11573) fixes `grind` rejecting dot notation terms, mistaking them for
  local hypotheses.

* [#11579](https://github.com/leanprover/lean4/pull/11579) ensures that ground theorems are properly handled as `grind`
  parameters. Additionally, `grind [(thm)]` and `grind [thm]` should be
  handled the same way.

* [#11580](https://github.com/leanprover/lean4/pull/11580) adds a missing `Nat.cast` missing normalization rule for
  `grind`. Example:
  ```lean
  example (n : Nat) : Nat.cast n = n := by
    grind
  ```

* [#11589](https://github.com/leanprover/lean4/pull/11589) improves indexing for `grind` patterns. We now include symbols
  occurring in nested ground patterns. This important to minimize the
  number of activated E-match theorems.

* [#11593](https://github.com/leanprover/lean4/pull/11593) fixes an issue where `grind` did not display deprecation
  warnings when deprecated lemmas were used in its argument list.

* [#11594](https://github.com/leanprover/lean4/pull/11594) fixes `grind?` to include term parameters (like `[show P by
  tac]`) in its suggestions. Previously, these were being dropped because
  term arguments are stored in `extraFacts` and not tracked via E-matching
  like named lemmas.

* [#11604](https://github.com/leanprover/lean4/pull/11604) fixes how theorems without parameters are handled in `grind`.

* [#11605](https://github.com/leanprover/lean4/pull/11605) fixes a bug in the internalizer of `a^p` terms in `grind
  linarith`.

* [#11609](https://github.com/leanprover/lean4/pull/11609) improves the case-split heuristics in `grind`. In this PR, we do
  not increment the number of case splits in the first case. The idea is
  to leverage non-chronological backtracking: if the first case is solved
  using a proof that doesn't depend on the case hypothesis, we backtrack
  and close the original goal directly. In this scenario, the case-split
  was "free", it didn't contribute to the proof. By not counting it, we
  allow deeper exploration when case-splits turn out to be irrelevant.
  The new heuristic addresses the second example in #11545

* [#11613](https://github.com/leanprover/lean4/pull/11613) ensures we apply the ring normalizer to equalities being
  propagated from the `grind` core module to `grind lia`. It also ensures
  we use the safe/managed polynomial functions when normalizing.

* [#11615](https://github.com/leanprover/lean4/pull/11615) adds a normalization rule for `Int.subNatNat` to `grind`.

* [#11628](https://github.com/leanprover/lean4/pull/11628) adds a few `*` normalization rules for `Semiring`s to `grind`.

* [#11629](https://github.com/leanprover/lean4/pull/11629) adds a missing condition in the pattern normalization code used
  in `grind`. It should ignore support ground terms.

* [#11635](https://github.com/leanprover/lean4/pull/11635) ensures the pattern normalizer used in `grind` does violate
  assumptions made by the gadgets `Grind.genPattern` and
  `Grind.getHEqPattern`.

* [#11638](https://github.com/leanprover/lean4/pull/11638) fixes bitvector literal internalization in `grind`. The fix
  ensures theorems indexed by `BitVec.ofNat` are properly activated.

* [#11639](https://github.com/leanprover/lean4/pull/11639) adds support for `BitVec.ofNat` in `grind ring`. Example:

  ```lean
  example (x : BitVec 8) : (x - 16#8)*(x + 272#8) = x^2 := by
    grind
  ```

* [#11640](https://github.com/leanprover/lean4/pull/11640) adds support for `BitVec.ofNat` in `grind lia`. Example:

  ```lean
  example (x y : BitVec 8) : y < 254#8 → x > 2#8 + y → x > 1#8 + y := by
    grind
  ```

* [#11653](https://github.com/leanprover/lean4/pull/11653) adds propagation rules corresponding to the `Semiring`
  normalization rules introduced in #11628. The new rules apply only to
  non-commutative semirings, since support for them in `grind` is limited.
  The normalization rules introduced unexpected behavior in Mathlib
  because they neutralize parameters such as `one_mul`: any theorem
  instance associated with such a parameter is reduced to `True` by the
  normalizer.

* [#11656](https://github.com/leanprover/lean4/pull/11656) adds support for `Int.sign`, `Int.fdiv`, `Int.tdiv`, `Int.fmod`,
  `Int.tmod`, and `Int.bmod` to `grind`. These operations are just
  preprocessed away. We assume that they are not very common in practice.
  Examples:
  ```lean
  example {x y : Int} : y = 0 → (x.fdiv y) = 0 := by grind
  example {x y : Int} : y = 0 → (x.tdiv y) = 0 := by grind
  example {x y : Int} : y = 0 → (x.fmod y) = x := by grind
  example {x y : Int} : y = 1 → (x.fdiv (2 - y)) = x := by grind
  example {x : Int} : x > 0 → x.sign = 1 := by grind
  example {x : Int} : x < 0 → x.sign = -1 := by grind
  example {x y : Int} : x.sign = 0 → x*y = 0 := by grind
  ```

* [#11658](https://github.com/leanprover/lean4/pull/11658) fixes a bug in the internalization of parametric literals in
  `grind`. That is, literals whose type is `BitVec _` or `Fin _`.

* [#11659](https://github.com/leanprover/lean4/pull/11659) adds `MessageData.withNamingContext` when generating pattern
  suggestions at `@[grind]`. It fixes another issue reported during
  ItaLean.

* [#11660](https://github.com/leanprover/lean4/pull/11660) fixes another theorem activation issue in `grind`.

* [#11663](https://github.com/leanprover/lean4/pull/11663) fixes the `grind` pattern validator. It covers the case where an
  instance is not tagged with the implicit instance binder. This happens
  in declarations such as
  ```lean
  ZeroMemClass.zero_mem {S : Type} {M : outParam Type} {inst1 : Zero M} {inst2 : SetLike S M}
    [self : @ZeroMemClass S M inst1 inst2] (s : S) : 0 ∈ s
  ```

## Compiler

* [#11082](https://github.com/leanprover/lean4/pull/11082) prevents symbol clashes between (non-`@[export]`) definitions
  from different Lean packages.

* [#11185](https://github.com/leanprover/lean4/pull/11185) fixes the `reduceArity` compiler pass to consider
  over-applications to functions that have their arity reduced.
  Previously, this pass assumed that the amount of arguments to
  applications was always the same as the number of parameters in the
  signature. This is usually true, since the compiler eagerly introduces
  parameters as long as the return type is a function type, resulting in a
  function with a return type that isn't a function type. However, for
  dependent types that sometimes are function types and sometimes not,
  this assumption is broken, resulting in the additional parameters to be
  dropped.

* [#11210](https://github.com/leanprover/lean4/pull/11210) fixes a bug in the LCNF simplifier unearthed while working on
  #11078. In some situations caused by `unsafeCast`, the simplifier would
  record incorrect information about `cases`, leading to further bugs down
  the line.

* [#11215](https://github.com/leanprover/lean4/pull/11215) fixes an issue where header nesting levels were properly tracked
  between, but not within, moduledocs.

* [#11217](https://github.com/leanprover/lean4/pull/11217) fixes fallout of the closure allocator changes in #10982. As far
  as we know
  this bug only meaningfully manifests in non default build configurations
  without mimalloc such as:
  `cmake --preset release -DUSE_MIMALLOC=OFF`

* [#11310](https://github.com/leanprover/lean4/pull/11310) makes the specializer (correctly) share more cache keys across
  invocations, causing us to produce less code bloat.

* [#11340](https://github.com/leanprover/lean4/pull/11340) fixes a miscompilation when encountering projections of non
  trivial structure types.

* [#11362](https://github.com/leanprover/lean4/pull/11362) accelerates termination of the ElimDeadBranches compiler pass.

* [#11366](https://github.com/leanprover/lean4/pull/11366) sorts the declarations fed into ElimDeadBranches in increasing
  size. This can improve performance when we are dealing with a lot of
  iterations.

* [#11381](https://github.com/leanprover/lean4/pull/11381) fixes a bug where the closed term extraction does not respect
  the implicit invariant of the
  c emitter to have closed term decls first, other decls second, within an
  SCC. This bug has not yet
  been triggered in the wild but was unearthed during work on upcoming
  modifications of the
  specializer.

* [#11383](https://github.com/leanprover/lean4/pull/11383) fixes the compilation of structure projections with unboxed
  arguments marked `extern`, adding missing `dec` instructions. It led to
  leaking single allocations when such functions were used as closures or
  in the interpreter.

* [#11388](https://github.com/leanprover/lean4/pull/11388) is a followup of #11381 and enforces the invariants on ordering
  of closed terms and constants required by the EmitC pass properly by
  toposorting before saving the declarations into the Environment.

* [#11426](https://github.com/leanprover/lean4/pull/11426) closes #11356.

* [#11445](https://github.com/leanprover/lean4/pull/11445) slightly improves the types involved in creating boxed
  declarations. Previously the type of
  the vdecl used for the return was always `tobj` when returning a boxed
  scalar. This is not the most
  precise annotation we can give.

* [#11451](https://github.com/leanprover/lean4/pull/11451) adapts the lambda lifter in LCNF to eta contract instead of
  lambda lift if possible. This prevents the creation of a few hundred
  unnecessary lambdas across the code base.

* [#11517](https://github.com/leanprover/lean4/pull/11517) implements constant folding for Nat.mul

* [#11525](https://github.com/leanprover/lean4/pull/11525) makes the LCNF simplifier eliminate cases where all alts are
  `.unreach` to just an `.unreach`.
    an `.unreach`

* [#11530](https://github.com/leanprover/lean4/pull/11530) introduces the new `tagged_return` attribute. It allows users to
  mark `extern` declarations to be guaranteed to always return `tagged`
  return values. Unlike with `object` or `tobject` the compiler does not
  emit reference counting operations for them. In the future information
  from this attribute will be used for a more powerful analysis to remove
  reference counts when possible.

* [#11576](https://github.com/leanprover/lean4/pull/11576) removes the old ElimDeadBranches pass and shifts the new one
  past lambda lifting.

* [#11586](https://github.com/leanprover/lean4/pull/11586) allows projections on `tagged` values in the IR type system.

## Documentation

* [#11119](https://github.com/leanprover/lean4/pull/11119) introduces a clarifying note to "undefined identifier" error
  messages when the undefined identifier is in a syntactic position where
  autobinding might generally apply, but where and autobinding is
  disabled. A corresponding note is made in the `lean.unknownIdentifier`
  error explanation.

* [#11364](https://github.com/leanprover/lean4/pull/11364) adds missing docstrings for constants that occur in the
  reference manual.

* [#11472](https://github.com/leanprover/lean4/pull/11472) adds missing docstrings for the `mkSlice` methods.

* [#11550](https://github.com/leanprover/lean4/pull/11550) reviews the docstrings for `Std.Do` that will appear in the Lean
  reference manual and adds those that were missing.

* [#11575](https://github.com/leanprover/lean4/pull/11575) fixes a typo in the docstring of the `cases` tactic.

* [#11595](https://github.com/leanprover/lean4/pull/11595) documents that tests in `tests/lean/run/` run with
  `-Dlinter.all=false`, and explains how to enable specific linters when
  testing linter behavior.

## Server

* [#11162](https://github.com/leanprover/lean4/pull/11162) reduces the memory consumption of the language server (the
  watchdog process in particular). In Mathlib, it reduces memory
  consumption by about 1GB.

* [#11164](https://github.com/leanprover/lean4/pull/11164) ensures that the code action provided on unknown identifiers
  correctly inserts `public` and/or `meta` in `module`s

* [#11577](https://github.com/leanprover/lean4/pull/11577) fixes the tactic framework reporting file progress bar ranges
  that cover up progress inside tactic blocks nested in tactic
  combinators. This is a purely visual change, incremental re-elaboration
  inside supported combinators was not affected.

## Lake

* [#11198](https://github.com/leanprover/lean4/pull/11198) fixes an error message in Lake which suggested incorrect
  lakefile syntax.

* [#11216](https://github.com/leanprover/lean4/pull/11216) ensures that the `text` argument of `computeArtifact` is always
  provided in Lake code, fixing a hashing bug with
  `buildArtifactUnlessUpToDate` in the process.

* [#11270](https://github.com/leanprover/lean4/pull/11270) adds a module resolution procedure to Lake to disambiguate
  modules that are defined in multiple packages.

* [#11500](https://github.com/leanprover/lean4/pull/11500) adds a workspace-index to the name of the package used by build
  target. To clarify the distinction between the different uses of a
  package's name, this PR also deprecates `Package.name` for more
  use-specific variants (e.g., `Package.keyName`, `Package.prettyName`,
  `Package.origName`).

## Other

* [#11328](https://github.com/leanprover/lean4/pull/11328) fixes freeing memory accidentally retained for each document
  version in the language server on certain elaboration workloads. The
  issue must have existed since 4.18.0.

* [#11437](https://github.com/leanprover/lean4/pull/11437) adds recording functionality such that `shake` can more
  precisely track whether an import should be preserved solely for its
  `attribute` commands.

* [#11496](https://github.com/leanprover/lean4/pull/11496) implements new flags and annotations for `shake` for use in
  Mathlib:

  > Options:
  >   --keep-implied
  > Preserves existing imports that are implied by other imports and thus
  not technically needed
  >     anymore
  >
  >   --keep-prefix
  > If an import `X` would be replaced in favor of a more specific import
  `X.Y...` it implies,
  > preserves the original import instead. More generally, prefers
  inserting `import X` even if it
  > was not part of the original imports as long as it was in the original
  transitive import closure
  >     of the current module.
  >
  >   --keep-public
  > Preserves all `public` imports to avoid breaking changes for external
  downstream modules
  >
  >   --add-public
  > Adds new imports as `public` if they have been in the original public
  closure of that module.
  > In other words, public imports will not be removed from a module
  unless they are unused even
  > in the private scope, and those that are removed will be re-added as
  `public` in downstream
  > modules even if only needed in the private scope there. Unlike
  `--keep-public`, this may
  > introduce breaking changes but will still limit the number of inserted
  imports.
  >
  > Annotations:
  > The following annotations can be added to Lean files in order to
  configure the behavior of
  > `shake`. Only the substring `shake: ` directly followed by a directive
  is checked for, so multiple
  > directives can be mixed in one line such as `-- shake:
  keep-downstream, shake: keep-all`, and they
  > can be surrounded by arbitrary comments such as `-- shake: keep
  (metaprogram output dependency)`.
  >
  >   * `module -- shake: keep-downstream`:
  > Preserves this module in all (current) downstream modules, adding new
  imports of it if needed.
  >
  >   * `module -- shake: keep-all`:
  > Preserves all existing imports in this module as is. New imports now
  needed because of upstream
  >     changes may still be added.
  >
  >   * `import X -- shake: keep`:
  > Preserves this specific import in the current module. The most common
  use case is to preserve a
  > public import that will be needed in downstream modules to make sense
  of the output of a
  > metaprogram defined in this module. For example, if a tactic is
  defined that may synthesize a
  > reference to a theorem when run, there is no way for `shake` to detect
  this by itself and the
  > module of that theorem should be publicly imported and annotated with
  `keep` in the tactic's
  >     module.
  >     ```
  >     public import X  -- shake: keep (metaprogram output dependency)
  >
  >     ...
  >
  >     elab \"my_tactic\" : tactic => do
  > ... mkConst ``f -- `f`, defined in `X`, may appear in the output of
  this tactic
  >     ```

* [#11507](https://github.com/leanprover/lean4/pull/11507) optimizes the filesystem accesses during importing for a ~3% win
  on Linux, potentially more on other platforms.

````
