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

set_option linter.typography.quotes false

#doc (Manual) "Lean 4.29.0 (2026-03-27)" =>
%%%
tag := "release-v4.29.0"
file := "v4.29.0"
%%%

For this release, 453 changes landed. In addition to the 112 feature additions and 107 fixes listed below there were 30 refactoring changes, 21 documentation improvements, 29 performance improvements, 26 improvements to the test suite and 115 other changes.

# Highlights

_Violetta Sim has helpfully written the release highlights from 4.16 through 4.29, and the Lean developers gratefully acknowledge her contributions._


## Performance Improvements

[#12082](https://github.com/leanprover/lean4/pull/12082) and
[#12044](https://github.com/leanprover/lean4/pull/12044) reduce
startup time by storing closed terms directly in the binary, where
possible, and initializing the remaining ones lazily instead of at
startup.

[#12406](https://github.com/leanprover/lean4/pull/12406) significantly
reduces the memory consumed by LRAT proof checking in `bv_decide`.

## New Extensible `do` Elaborator

[#12459](https://github.com/leanprover/lean4/pull/12459) adds a new,
extensible `do` elaborator. Users can opt into the new elaborator by
unsetting the option `backward.do.legacy`.

New elaborators for the builtin `doElem` syntax category can be
registered with attribute `doElem_elab`. For new syntax, additionally
a control info handler must be registered with attribute
`doElem_control_info` that specifies whether the new syntax `return`s
early, `break`s, `continue`s and which `mut` vars it reassigns.

Do elaborators have type
``TSyntax `doElem → DoElemCont → DoElabM Expr``, where `DoElabM` is
essentially `TermElabM` and the `DoElemCont` represents how the rest
of the `do` block is to be elaborated. Consult the docstrings for more
details.

*Breaking Changes:*

- The syntax for `let pat := rhs | otherwise` and similar now scope
  over the `doSeq` that follows. Furthermore, `otherwise` and the
  sequence that follows are now `doSeqIndented` in order not to steal
  syntax from record syntax.

*Breaking Changes* when opting into the new `do` elaborator by unsetting
`backward.do.legacy`:

- `do` notation now always requires `Pure`.
- `do match` is now always non-dependent. There is
  `do match (dependent := true)` that expands to a term match as a
  workaround for some dependent uses.

## mvcgen: Specifications in the Local Context

[#12395](https://github.com/leanprover/lean4/pull/12395) adds mvcgen
support for specifications in the local context. Example:

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
  mvcgen [foo_spec, bar] -- unfold `bar` and automatically apply the spec for the higher-order argument `k`
```

## grind: Higher-Order Miller Pattern Support in E-matching

[#12483](https://github.com/leanprover/lean4/pull/12483) adds support
for higher-order Miller patterns in `grind`'s e-matching engine.
Previously, lambda arguments in e-matching patterns were always
treated as `dontCare`, meaning they could not contribute to matching
or bind pattern variables. This was a significant limitation for
theorems where lambda arguments carry essential structure, such as
`List.foldl`, `List.foldrM`, or any combinator that takes a function
argument.

With this change, when a pattern argument is a lambda whose body
satisfies the *Miller pattern condition* — i.e., pattern variables
are applied only to distinct lambda-bound variables — the lambda is
preserved as an `ho[...]` pattern. At instantiation time, these
higher-order patterns are matched via `isDefEq` after all first-order
pattern variables have been assigned by the E-graph.

*Example*

```
@[grind =] theorem applyFlip_spec (f : Nat → Nat → Nat) (a b : Nat)
    : applyFlip (fun x y => f y x) a b = f b a := sorry
```

The pattern `applyFlip ho[fun x => fun y => #2 y x] #1 #0` captures
the lambda argument structurally: `#2` (the pattern variable for `f`)
is applied to distinct lambda-bound variables `y` and `x`. When
`grind` encounters `applyFlip (fun x y => Nat.add y x) 3 4`, it binds
`f := Nat.add` via `isDefEq` and fires the rewrite.

## One Axiom per Native Computation

[#12217](https://github.com/leanprover/lean4/pull/12217) implements
RFC [#12216](https://github.com/leanprover/lean4/issues/12216): native
computation ({tactic}`native_decide`, {tactic}`bv_decide`) is represented in the logic
as one axiom per computation, asserting the equality that was obtained
from the native computation. `#print axiom` will no longer show
`Lean.trustCompiler`, but rather the auto-generated names of these
axioms (with, for example, `._native.bv_decide.` in the name). See the
RFC for more information.

## More Reliable Universe Level Inference in `inductive`/`structure` Commands

[#12514](https://github.com/leanprover/lean4/pull/12514) improves
universe level inference for the `inductive` and `structure` commands
to be more reliable and to produce better error messages. See the PR
description for more information.

*Breaking change.* Universe level metavariables present only in
constructor fields are no longer promoted to be universe level
parameters: use explicit universe level parameters. This promotion was
inconsistently done depending on whether the inductive type's universe
level had a metavariable, and also it caused confusion for users,
since these universe levels are not constrained by the type former's
parameters.

*Breaking change.* Now recursive types do not count as “obvious
`Prop` candidates”. Use an explicit `Prop` type former annotation on
recursive inductive predicates.

## Simpler `noncomputable` Semantics

[#12028](https://github.com/leanprover/lean4/pull/12028) gives a
simpler semantics to `noncomputable`, improving predictability as well
as preparing codegen to be moved into a separate build step without
breaking immediate generation of error messages.

Specifically, `noncomputable` is now needed whenever an axiom or
another `noncomputable` def is used by a def except for the following
special cases:

- uses inside proofs, types, type formers, and constructor arguments
  corresponding to (fixed) inductive parameters are ignored
- uses of functions marked `@[extern]/@[implemented_by]/@[csimp]` are
  ignored
- for applications of a function marked `@[macro_inline]`,
  noncomputability of the inlining is instead inspected

*Breaking change*: After this change, more `noncomputable`
annotations than before may be required in exchange for improved
future stability.

## Changes to Instance and Reducibility Handling

v4.29.0 brings a significant and breaking change to the handling of reducibility settings.
We address a longstanding problem: prior to v4.29.0, the `isDefEq` algorithm would bump the
transparency level up to `.default` (i.e. become willing to unfold default transparency definitions)
when comparing implicit arguments.

This was a serious problem, causing both immediate unpredictable performance problems in
`isDefEq`, and hiding many places where definitional abuse was occurring in downstream libraries.

In order to ensure scalability, and address these definitional abuse problems, we have
made the quite disruptive change, in [#12179](https://github.com/leanprover/lean4/pull/12179),
of removing this transparency level bump as the default path.

The changes to the transparency bump in comparing implicit arguments can be controlled in two ways:
* Definitions can be tagged with the new `@[implicit_reducible]` attribute.
  This is intermediate between `@[reducible]` and `@[semireducible]` (i.e. the default setting),
  in that the definition is mostly treated as semireducible, except when `isDefEq` is processing
  implicit arguments or match discriminants.
  See [#12247](https://github.com/leanprover/lean4/pull/12247) and [#12567](https://github.com/leanprover/lean4/pull/12567).
* The option `set_option backward.isDefEq.respectTransparency false` restores the previous behaviour prior to `v4.29.0`
  (equivalently, all semireducible definitions are treated as `implicit_reducible`).
  As a backward compatibility option, this may eventually be removed, but given how disruptive this change is we anticipate leaving the option available for the medium term.


As a consequence of these changes to transparency handling, existing definitional abuse problems in downstream libraries now surface in places
where previously they didn't. To help address these problems, which primarily, but not exclusively,
are caused by incorrectly implemented typeclass instances, we have made changes in [#12897](https://github.com/leanprover/lean4/pull/12897)
to `inferInstanceAs` and the default `deriving` handler.
These ensure that instances created using them do not leak the definition of the types involved,
when the instances are reduced at less than semireducible transparency.

`inferInstanceAs α` synthesizes an instance of type `α` but now adjusts it to conform to the
expected type `β`, which must be inferable from context.

Example:
```
def D := Nat
instance : Inhabited D := inferInstanceAs (Inhabited Nat)
```

The adjustment will make sure that the resulting instance will not leak the RHS `Nat` when
reduced at transparency levels below `semireducible`, i.e. where `D` would not be unfolded either.

More specifically, given the source type (the argument) and target type (the expected type),
`inferInstanceAs` synthesizes an instance for the source type and then unfolds and rewraps its
components (fields, nested instances) as necessary to make them compatible with the target type. The
individual steps are represented by the following options, which all default to enabled and can be
disabled to help with porting:

* `backward.inferInstanceAs.wrap`: master switch for instance adjustment in both `inferInstanceAs`
  and the default deriving handler
* `backward.inferInstanceAs.wrap.reuseSubInstances`: reuse existing instances for the target type
  for sub-instance fields to avoid non-defeq instance diamonds
* `backward.inferInstanceAs.wrap.instances`: wrap non-reducible instances in auxiliary definitions
* `backward.inferInstanceAs.wrap.data`: wrap data fields in auxiliary definitions (proof fields are
  always wrapped)

If you just need to synthesize an instance without transporting between types, use `inferInstance`
instead, potentially with a type annotation for the expected type.

A third significant change in `v4.29.0` is that `simp` and `dsimp` no longer process typeclass instances.
This behaviour was producing non-standard instances, and causing problems in Mathlib.
See [#12244](https://github.com/leanprover/lean4/pull/12244) and [#12195](https://github.com/leanprover/lean4/pull/12195).
The old behavior can be restored with

```
set_option backward.dsimp.instances true
```

or `simp +instances` for `simp`. Our experience so far, however, is that this is not often needed.

Finally we have fixed in [#12172](https://github.com/leanprover/lean4/pull/12172) a problem with how
we determine whether a function parameter is an instance, which has follow-on effects in several algorithms that depend on this classification.
This may cause potential regressions: automation may now behave differently
in cases where it previously misidentified instance parameters.
For example, a rewrite rule in `simp` that was not firing due to
incorrect indexing may now fire.

### Migration guide

Any projects wanting to postpone dealing with the adaptations required by the changes to transparency level bumps can
simply use `set_option backward.isDefEq.respectTransparency false`.

This can be set on a project-wide level in your `lakefile.toml`:
```
[leanOptions]
backward.isDefEq.respectTransparency = false
```

However we encourage you to instead localize the option in the files that need it,
or even on individual declarations using `set_option backward.isDefEq.respectTransparency false in ...`.
This makes it easier to start identifying the definitional abuse problems in your code.

If your project is downstream of Mathlib, you may find the following two scripts useful:
* `scripts/add_set_option.py` (available in `.lake/packages/mathlib/scripts/add_set_option.py` if you have Mathlib as a dependency)
  which tries compiling your project, and automatically wrapping any failing declaration with `set_option backward.isDefEq.respectTransparency false in ...`,
  in those cases where doing so resolves the failure.
* `scripts/rm_set_option.py`, which compiles your project and identifies all occurrences of `set_option backward.isDefEq.respectTransparency false in ...` which can be removed without causing a failure (in that same declaration).
  This may happen because of earlier changes which resolve the definitional abuse problem.

These scripts can also be copied out of Mathlib and run on any project.

Again, when downstream of Mathlib you may also use the experimental `#defeq_abuse in ...` command,
which attempts to identify and explain, or at least give clues to, the underlying definitional abuse problem that
may explain why a declaration currently needs `set_option backward.isDefEq.respectTransparency false in ...`.
We encourage users to report problems with this command on the [Zulip](https://leanprover.zulipchat.com/),
and we hope that as this diagnostic command stabilizes we will be able to make it available as part of a future Lean toolchain.

You are encouraged to review the construction of instances for all default transparency type synonyms in your project.
Where possible, you should use the `deriving` handler, or the new `inferInstanceAs` elaborator,
rather than writing term mode constructions which require unfolding the type synonym in order to typecheck.
The `inferInstanceAs` command now *requires* an expected type.
If you encounter errors where `inferInstanceAs` now gives an error because an expected type was not provided,
you may find that you should simply be using `inferInstance` instead.

## Universe Levels as Output Parameters

[#12423](https://github.com/leanprover/lean4/pull/12423) adds the
attribute `@[univ_out_params]` for specifying which universe levels
should be treated as output parameters. By default, any universe level
that does not occur in any input parameter is considered an output
parameter.

## Library Highlights

This release includes a new string search infrastructure, using a
polymorphic pattern system that works uniformly over characters,
predicates, and strings. See:

- [#12333](https://github.com/leanprover/lean4/pull/12333) adds the
  basic typeclasses that will be used in the verification of our
  string searching infrastructure.

- [#12424](https://github.com/leanprover/lean4/pull/12424) gives a
  proof of `LawfulToForwardSearcherModel` for `Slice` patterns, which
  amounts to proving that our implementation of KMP is correct.

There are also various additions to the library, including:

- [#11938](https://github.com/leanprover/lean4/pull/11938) introduces
  projected minima and maxima, also known as “argmin/argmax”, for
  lists under the names `List.minOn` and `List.maxOn`. It also introduces
  `List.minIdxOn` and `List.maxIdxOn`, which return the index of the
  minimal or maximal element.

- [#11994](https://github.com/leanprover/lean4/pull/11994) provides
  more lemmas about sums of lists/arrays/vectors, especially sums of
  `Nat` or `Int` lists/arrays/vectors.

- [#12363](https://github.com/leanprover/lean4/pull/12363) introduces
  iterators for vectors via `Vector.iter` and `Vector.iterM`, together
  with the usual lemmas.

- [#12452](https://github.com/leanprover/lean4/pull/12452) upstreams
  `List.scanl`, `List.scanr` and their lemmas from batteries into the
  standard library.

## New Features in Lake

- [#12203](https://github.com/leanprover/lean4/pull/12203) changes
  artifact transfer from the local cache to prefer hard links over
  copies, with a fallback to copying when hard linking fails (e.g., on
  a different filesystem). Cache artifacts are now marked read-only to
  prevent accidental corruption via hard-linked paths.

- [#12444](https://github.com/leanprover/lean4/pull/12444) adds the
  Lake CLI command `lake cache clean`, which deletes the Lake cache
  directory.

- [#12490](https://github.com/leanprover/lean4/pull/12490) adds a
  system-wide Lake configuration file and uses it to configure the
  remote cache services used by `lake cache`.

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

* [#12325](https://github.com/leanprover/lean4/pull/12325) adds a warning to any `def` of class type that does not also
  declare an appropriate reducibility.

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
    mvcgen [foo_spec, bar] -- unfold `bar` and automatically apply the spec for the higher-order argument `k`
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

* [#12451](https://github.com/leanprover/lean4/pull/12451) provides the necessary hooks for the new do elaborator to call
  into the let and match elaborator.

* [#12459](https://github.com/leanprover/lean4/pull/12459) adds a new, extensible `do` elaborator. Users can opt into the
  new elaborator by unsetting the option `backward.do.legacy`.

* [#12460](https://github.com/leanprover/lean4/pull/12460) fixes an `AppBuilder` exception in the `cbv` tactic when
  simplifying projections whose projection function is dependent (closes
  #12457).

* [#12507](https://github.com/leanprover/lean4/pull/12507) fixes #12495 where equational theorem generation fails for
  structurally recursive definitions using a Box-like wrapper around
  nested inductives.

* [#12514](https://github.com/leanprover/lean4/pull/12514) improves universe level inference for the `inductive` and
  `structure` commands to be more reliable and to produce better error
  messages. Recall that the main constraint for inductive types is that if
  `u` is the universe level for the type and `u > 0`, then each
  constructor field's universe level `v` satisfies `v ≤ u`, where a
  *constructor field* is an argument that is not one of the type's
  *parameters* (recall: the type's parameters are a prefix of the
  parameters shared by the type former and all the constructors). Given
  this constraint, the `inductive` elaborator attempts to find reasonable
  assignments to metavariables that may be present:
  - For the universe level `u`, choosing an assignment that makes this
  level least is reasonable, provided it is unique.
  - For constructor fields, choosing the unique assignment is usually
  reasonable.
  - For the type's parameters, promoting level metavariables to new
  universe level parameters is reasonable.

* [#12524](https://github.com/leanprover/lean4/pull/12524) adds `Std.Iter.toHashSet` and variants.

* [#12525](https://github.com/leanprover/lean4/pull/12525) adds declaration names to leanchecker error messages to make
  debugging easier when the kernel rejects a declaration.

* [#12530](https://github.com/leanprover/lean4/pull/12530) improves the error message when `mvcgen` cannot resolve the name
  of a spec theorem.

* [#12538](https://github.com/leanprover/lean4/pull/12538) enables `backward.whnf.reducibleClassField` for v4.29.

* [#12558](https://github.com/leanprover/lean4/pull/12558) fixes a `(kernel) declaration has metavariables` error that
  occurred when a `by` tactic was used in a dependent inductive type index
  that refers to a previous index:

  ```
  axiom P : Prop
  axiom Q : P → Prop
  -- Previously gave: (kernel) declaration has metavariables 'Foo'
  inductive Foo : (h : P) → (Q (by exact h)) → Prop
  ```

* [#12564](https://github.com/leanprover/lean4/pull/12564) fixes `getStuckMVar?` to detect stuck metavariables through
  auxiliary parent projections created for diamond inheritance. These
  coercions (e.g., `AddMonoid'.toAddZero'`) are not registered as regular
  projections because they construct the parent value from individual
  fields rather than extracting a single field. Previously,
  `getStuckMVar?` would give up when encountering them, preventing TC
  synthesis from being triggered.

* [#12567](https://github.com/leanprover/lean4/pull/12567) renames `instance_reducible` to `implicit_reducible` and adds a
  new
  `backward.isDefEq.implicitBump` option to prepare for treating all
  implicit
  arguments uniformly during definitional equality checking.

* [#12572](https://github.com/leanprover/lean4/pull/12572) is part 2 of the `implicit_reducible` refactoring (part 1:
  #12567).

* [#12574](https://github.com/leanprover/lean4/pull/12574) renames `SpecTheorems.add` to `SpecTheorems.insert`

* [#12576](https://github.com/leanprover/lean4/pull/12576) adds `Sym.mkPatternFromDeclWithKey` to the Sym API to generalize
  and implement `Sym.mkEqPatternFromDecl`. This is useful to implement
  custom rewrite-like tactics that want to use `Pattern`s for
  discrimination tree lookup.

* [#12621](https://github.com/leanprover/lean4/pull/12621) fixes a bug where `reduceRecMatcher?` and `reduceProj?` bypassed
  the `@[cbv_opaque]` attribute. These kernel-level reduction functions
  use `whnf` internally, which does not know about `@[cbv_opaque]`. This
  meant `@[cbv_opaque]` values were unfolded when they appeared as match
  discriminants, recursor major premises, or projection targets. The fix
  introduces `withCbvOpaqueGuard`, which wraps these calls with
  `withCanUnfoldPred` to prevent `whnf` from unfolding `@[cbv_opaque]`
  definitions.

* [#12633](https://github.com/leanprover/lean4/pull/12633) makes `isDefEqProj` bump transparency to `.instances` (via
  `withInstanceConfig`) when comparing the struct arguments of class
  projections. This makes the behavior consistent with `isDefEqArgs`,
  which already applies the same bump for instance-implicit parameters
  when comparing function applications.

* [#12639](https://github.com/leanprover/lean4/pull/12639) fixes the interaction between
  `backward.whnf.reducibleClassField` and `isDefEqDelta`'s
  argument-comparison heuristic.

* [#12650](https://github.com/leanprover/lean4/pull/12650) fixes a performance regression introduced by enabling
  `backward.whnf.reducibleClassField`
  (https://github.com/leanprover/lean4/pull/12538). The
  `isNonTrivialRegular` function in `ExprDefEq` was classifying class
  projections as nontrivial at all transparency levels, but the extra
  `.instances` reduction in `unfoldDefault` that motivates this
  classification only applies at `.reducible` transparency. At higher
  transparency levels, the nontrivial classification caused unnecessary
  heuristic comparison attempts in `isDefEqDelta` that cascaded through
  BitVec reductions, causing elaboration of `Lean.Data.Json.Parser` to
  double from ~3.6G to ~7.2G instructions.

* [#12698](https://github.com/leanprover/lean4/pull/12698) adds a `result? : Option TraceResult` field to `TraceData` and
  populates it in `withTraceNode` and `withTraceNodeBefore`, so that
  metaprograms walking trace trees can determine success/failure
  structurally instead of string-matching on emoji.

* [#12699](https://github.com/leanprover/lean4/pull/12699) gives the `generate` function's "apply @Foo to Goal" trace nodes
  their own trace sub-class `Meta.synthInstance.apply` instead of sharing
  the parent `Meta.synthInstance` class.

* [#12701](https://github.com/leanprover/lean4/pull/12701) fixes a gap in how `@[implicit_reducible]` is assigned to parent
  projections during structure elaboration.

* [#12719](https://github.com/leanprover/lean4/pull/12719) marks `levelZero`, `levelOne`, and `Level.ofNat` as
  `@[implicit_reducible]` so that `Level.ofNat 0 =?= Level.zero` succeeds when
  the definitional equality checker respects transparency annotations.

* [#12756](https://github.com/leanprover/lean4/pull/12756) adds `deriving noncomputable instance` syntax so that
  delta-derived instances can be marked noncomputable.

* [#12789](https://github.com/leanprover/lean4/pull/12789) skips the noncomputable pre-check in `deriving instance` when
  the instance type is `Prop`, since proofs are erased by the compiler and
  computability is irrelevant.

* [#12778](https://github.com/leanprover/lean4/pull/12778) fixes an inconsistency in `getStuckMVar?` where the instance
  argument to class projection functions and auxiliary parent projections
  was not whnf-normalized before checking for stuck metavariables. Every
  other case in `getStuckMVar?` (recursors, quotient recursors, `.proj`
  nodes) normalizes the major argument via `whnf` before recursing — class
  projection functions and aux parent projections were the exception.

* [#12897](https://github.com/leanprover/lean4/pull/12897) adjusts the results of `inferInstanceAs` and the `def` `deriving`
  handler to conform to recently strengthened restrictions on reducibility.
  When deriving or inferring an instance for a semireducible type definition,
  the definition's RHS is no longer leaked when the instance is reduced at
  lower than semireducible transparency. The synthesized instance's components
  (fields, nested instances) are unfolded and rewrapped as necessary.

* [#13043](https://github.com/leanprover/lean4/pull/13043) fixes a bug where `inferInstanceAs` and the default `deriving`
  handler, when used inside a `meta section`, would create auxiliary
  definitions (via `normalizeInstance`) that were not marked as `meta`.
  This caused the compiler to reject the parent `meta` definition with:

  ```
  Invalid `meta` definition `instEmptyCollectionNamePrefixRel`, `instEmptyCollectionNamePrefixRel._aux_1` not marked `meta`
  ```

* [#13059](https://github.com/leanprover/lean4/pull/13059) switches the meta marking of auxiliary definitions created by
  `normalizeInstance` from using `isMetaSection` to the `declName?` pattern,
  fixing a bug where `deriving` in meta sections would fail because aux defs
  were incorrectly marked `meta` while the instance itself was not.

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

* [#12441](https://github.com/leanprover/lean4/pull/12441) removes `Subarray.foldl(M)`, `Subarray.toArray` and
  `Subarray.size` in favor of the `Std.Slice`-namespaced operations. Dot
  notation will continue to work. If, say, `Subarray.size` is explicitly
  referred to, an error suggesting to use `Std.Slice.size` will show up.

* [#12442](https://github.com/leanprover/lean4/pull/12442) derives `DecidableEq` instances for the types of ranges such as
  `a...b` (in this case, `Std.Rco`).

* [#12445](https://github.com/leanprover/lean4/pull/12445) provides lemmas characterizing `Nat.toDigits`, `Nat.repr` and
  `ToString Nat`.

* [#12449](https://github.com/leanprover/lean4/pull/12449) marks `String.toString_eq_singleton` as a `simp` lemma.

* [#12450](https://github.com/leanprover/lean4/pull/12450) moves the `String.Slice`/`String` iterators out into their own
  file, in preparation for verification.

* [#12452](https://github.com/leanprover/lean4/pull/12452) upstreams `List.scanl`, `List.scanr` and their lemmas from
  batteries into the standard library.

* [#12456](https://github.com/leanprover/lean4/pull/12456) verifies all of the `String` iterators except for the bytes
  iterator by relating them to `String.toList`.

* [#12504](https://github.com/leanprover/lean4/pull/12504) makes the `Rat.abs_*` lemmas (`abs_zero`, `abs_nonneg`,
  `abs_of_nonneg`, `abs_of_nonpos`, `abs_neg`, `abs_sub_comm`,
  `abs_eq_zero_iff`, `abs_pos_iff`) protected, so they don't shadow the
  general `abs_*` lemmas when the `Rat` namespace is opened in downstream
  projects.

* [#12521](https://github.com/leanprover/lean4/pull/12521) shows `HashSet.ofList l ~m l.foldl (init := ∅) fun acc a =>
  acc.insert a` (which is "just" the definition).

* [#12531](https://github.com/leanprover/lean4/pull/12531) bundles some lemmas about hash maps into equivalences for easier
  rewriting.

* [#12582](https://github.com/leanprover/lean4/pull/12582) uses a `ptrEq` fast path for `Name.quickCmp`. It is particularly
  effective at speeding up
  `quickCmp` calls in `TreeMap`'s indexed by `FVarId` as usually there is
  only one pointer per `FVarId`
  so equality is always instantly detected without traversing the linked
  list of `Name` components.

* [#12583](https://github.com/leanprover/lean4/pull/12583) inlines the accessor for the computed hash field of `Name`. This
  ensures that accessing the
  value is basically always just a single load instead of doing a full
  function call.

* [#12596](https://github.com/leanprover/lean4/pull/12596) adds an `Std.Do` spec lemma for `ForIn` over strings.

* [#12641](https://github.com/leanprover/lean4/pull/12641) derives the linear order on string positions (`String.Pos.Raw`,
  `String.Pos`, `String.Slice.Pos`) via `Std.LinearOrderPackage`, which
  ensures that all data-carrying and propositional instances are present.

* [#12642](https://github.com/leanprover/lean4/pull/12642) adds dsimprocs for reducing `String.toList` and `String.push`.

* [#12651](https://github.com/leanprover/lean4/pull/12651) adds some missing lemmas about `min`, `minOn`, `List.min`,
  `List.minOn`.

* [#12757](https://github.com/leanprover/lean4/pull/12757) marks `Id.run` as `[implicit_reducible]` to ensure that
  `Id.instMonadLiftTOfPure` and `instMonadLiftT Id` are definitionally
  equal when using `.implicitReducible` transparency setting.

* [#12821](https://github.com/leanprover/lean4/pull/12821) removes the `@[grind →]` attribute from
  `List.getElem_of_getElem?` and `Vector.getElem_of_getElem?`. These were
  identified as problematic in Mathlib by
  https://github.com/leanprover/lean4/issues/12805.

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

* [#12226](https://github.com/leanprover/lean4/pull/12226) fixes a bug where `grind [foo]` fails when the theorem `foo` has
  a different universe variable name than the goal, even though universe
  polymorphism should allow the universes to unify.

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

* [#12500](https://github.com/leanprover/lean4/pull/12500) improves the error messages produced by the `decide_cbv` tactic
  by only reducing the left-hand side of the equality introduced by
  `of_decide_eq_true`, rather than attempting to reduce both sides via
  `cbvGoal`.

* [#12506](https://github.com/leanprover/lean4/pull/12506) adds the ability to register theorems with the `cbv_eval`
  attribute in the reverse direction using the `←` modifier, mirroring the
  existing `simp` attribute behavior. When `@[cbv_eval ←]` is used, the
  equation `lhs = rhs` is inverted to `rhs = lhs`, allowing `cbv` to
  rewrite occurrences of `rhs` to `lhs`.

* [#12562](https://github.com/leanprover/lean4/pull/12562) fixes #12554 where the `cbv` tactic throws "unexpected kernel
  projection term during structural definitional equality" when a rewrite
  theorem's pattern contains a lambda and the expression being matched has
  a `.proj` (kernel projection) at the corresponding position.

* [#12568](https://github.com/leanprover/lean4/pull/12568) removes `tryMatchEquations` and `tryMatcher` from
  `Lean.Meta.Tactic.Cbv.Main`, as both are already defined and used in
  `Lean.Meta.Tactic.Cbv.ControlFlow`. The copies in `Main.lean` were
  unreachable dead code.

* [#12585](https://github.com/leanprover/lean4/pull/12585) removes unnecessary `trySynthInstance ` in `ite` and `dite`
  simprocs used by `cbv` that previously contributed to too much of
  unnecessary unrolling by the tactic.

* [#12588](https://github.com/leanprover/lean4/pull/12588) adds a benchmark for `cbv` tactic that involves evaluating
  `List.mergeSort` on a reversed list on natural numbers.

* [#12601](https://github.com/leanprover/lean4/pull/12601) adds a warning when using `cbv` or `decide_cbv` in tactic mode,
  matching the existing warning in conv mode
  (`src/Lean/Elab/Tactic/Conv/Cbv.lean`). The warning informs users that
  these tactics are experimental and still under development. It can be
  disabled with `set_option cbv.warning false`.

* [#12612](https://github.com/leanprover/lean4/pull/12612) fixes a crash in the `cbv` tactic's `handleProj` simproc when
  processing a dependent projection (e.g. `Sigma.snd`) whose struct is
  rewritten via `@[cbv_eval]` to a non-definitionally-equal term that
  cannot be further reduced.

* [#12615](https://github.com/leanprover/lean4/pull/12615) fixes a flipped condition in `handleConst` that prevented `cbv`
  from unfolding nullary (non-function) constant definitions like
  `def myVal : Nat := 42`. The check `unless eType matches .forallE` was
  intended to skip bare function constants (whose unfold theorems expect
  arguments) but instead skipped value constants. The fix changes the
  guard to `if eType matches .forallE`, matching the logic used in the
  standard `simp` ground evaluator.

* [#12622](https://github.com/leanprover/lean4/pull/12622) fixes a bug where `simp` made no progress on class projection
  reductions when `backward.whnf.reducibleClassField` is `true`.

* [#12627](https://github.com/leanprover/lean4/pull/12627) reverts #12615, which accidentally broke Leroy's compiler
  verification course benchmark.

* [#12646](https://github.com/leanprover/lean4/pull/12646) enables the `cbv` tactic to unfold nullary (non-function)
  constant
  definitions such as `def myNat : Nat := 42`, allowing ground term
  evaluation
  (e.g. `evalEq`, `evalLT`) to recognize their values as literals.

* [#12782](https://github.com/leanprover/lean4/pull/12782) adds high priority to instances for `OfSemiring.Q` in the grind
  ring envelope. When Mathlib is imported, instance synthesis for types
  like `OfSemiring.Q Nat` becomes very expensive because the solver
  explores many irrelevant paths before finding the correct instances. By
  marking these instances as high priority and adding shortcut instances
  for basic operations (`Add`, `Sub`, `Mul`, `Neg`, `OfNat`, `NatCast`,
  `IntCast`, `HPow`), instance synthesis resolves quickly.

# Compiler

* [#12044](https://github.com/leanprover/lean4/pull/12044) implements lazy initialization of closed terms. Previous work
  has already made sure that ~70% of the closed terms occurring in core
  can be statically initialized from the binary. With this the remaining
  ones are initialized lazily instead of at startup.

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

* [#12548](https://github.com/leanprover/lean4/pull/12548) ports the RC insertion from IR to LCNF.

* [#12580](https://github.com/leanprover/lean4/pull/12580) makes `computed_field` respect the inline attributes on the
  function for computing the
  field. This means we can inline the accessor for the field, allowing
  quicker access.

* [#12604](https://github.com/leanprover/lean4/pull/12604) makes the derived value analysis in RC insertion recognize
  `Array.uget` as another kind of
  "projection-like" operation. This allows it to reduce reference count
  pressure on elements accessed
  through uget.

* [#12625](https://github.com/leanprover/lean4/pull/12625) ensures that failure in initial compilation marks the relevant
  definitions as `noncomputable`, inside and outside `noncomputable
  section`, so that follow-up errors/noncomputable markings are detected
  in initial compilation as well instead of somewhere down the pipeline.

* [#12644](https://github.com/leanprover/lean4/pull/12644) ports the toposorting pass from IR to LCNF.

* [#12759](https://github.com/leanprover/lean4/pull/12759) replaces the `isImplicitReducible` check with `Meta.isInstance`
  in the `shouldInline` function within `inlineCandidate?`.

# Pretty Printing

* [#12688](https://github.com/leanprover/lean4/pull/12688) adds the `pp.fvars.anonymous` option (default `true`) that
  controls the display of loose free variables (fvars not in the local
  context). When `false`, they display as `_fvar._` instead of their internal
  name. This is useful for stabilizing output in `#guard_msgs`.
  [#12745](https://github.com/leanprover/lean4/pull/12745) fixes the
  behavior when the option is set to `false`.

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

* [#12616](https://github.com/leanprover/lean4/pull/12616) adds documentation to the Cbv evaluator files under
  `Meta/Tactic/Cbv/`. Module docstrings describe the evaluation strategy,
  limitations, attributes, and unfolding order. Function docstrings cover
  the public API and key internal simprocs.

* [#13115](https://github.com/leanprover/lean4/pull/13115) updates the `inferInstanceAs` docstring to reflect current
  behavior: it requires an
  expected type from context and should not be used as a simple
  `inferInstance` synonym. The
  old example (`#check inferInstanceAs (Inhabited Nat)`) no longer works,
  so it's replaced
  with one demonstrating the intended transport use case.

# Server

* [#12197](https://github.com/leanprover/lean4/pull/12197) fixes a bug in `System.Uri.fileUriToPath?` where it wouldn't use
  the default Windows path separator in the path it produces.

* [#12332](https://github.com/leanprover/lean4/pull/12332) fixes an issue on new NeoVim versions that would cause the
  language server to display an error when using certain code actions.

* [#12553](https://github.com/leanprover/lean4/pull/12553) fixes an issue where commands that do not support incrementality
  did not have their elaboration interrupted when a relevant edit is made
  by the user. As all built-in variants of def/theorem share a common
  incremental elaborator, this likely had negligible impact on standard
  Lean files but could affect other use cases heavily relying on custom
  commands such as Verso.

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

* [#12490](https://github.com/leanprover/lean4/pull/12490) adds a system-wide Lake configuration file and uses it to
  configure the remote cache services used by `lake cache`.

* [#12532](https://github.com/leanprover/lean4/pull/12532) fixes a bug with `cache clean` where it would fail if the cache
  directory does not exist.

* [#12537](https://github.com/leanprover/lean4/pull/12537) fixes a bug where Lake recached artifacts already present within
  the cache. As a result, Lake would attempt to overwrite the read-only
  artifacts, causing a permission denied error.

* [#12835](https://github.com/leanprover/lean4/pull/12835) changes Lake to only emit `.nobuild` traces (introduced in
  #12076) if the normal trace file already exists. This fixes an issue
  where a `lake build --no-build` would create the build directory and
  thereby prevent a cloud release fetch in a future build.

* [#13141](https://github.com/leanprover/lean4/pull/13141) changes Lake to run `git clean -xf` when updating dependency
  repositories, ensuring stale untracked files (such as `.hash` files) in the
  source tree are removed. Stale `.hash` files could cause incorrect trace
  computation and break builds.

# Other

* [#12351](https://github.com/leanprover/lean4/pull/12351) extends the `@[csimp]` attribute to be correctly tracked by
  `lake shake`

* [#12375](https://github.com/leanprover/lean4/pull/12375) extends shake with tracking of attribute names passed to
  `simp`/`grind`.

* [#12463](https://github.com/leanprover/lean4/pull/12463) fixes two issues discovered during the first test of the revised
  nightly release workflow
  (https://github.com/leanprover/lean4/pull/12461):

  *1. Date logic:* The `workflow_dispatch` path used `date -u +%F`
  (current UTC date) to find the base nightly to revise. If the most
  recent nightly was from yesterday (e.g. `nightly-2026-02-12`) but UTC
  has rolled over to Feb 13, the code would look for `nightly-2026-02-13`,
  not find it, and create a fresh nightly instead of a revision. Now finds
  the latest `nightly-*` tag via `sort -rV` and creates a revision of
  that.

* [#12517](https://github.com/leanprover/lean4/pull/12517) adds tooling for profiling Lean programs with human-readable
  function names in Firefox Profiler:

  - *`script/lean_profile.sh`* — One-command pipeline: record with
  samply, symbolicate, demangle, and open in Firefox Profiler
  - *`script/profiler/lean_demangle.py`* — Faithful port of
  `Name.demangleAux` from `NameMangling.lean`, with a postprocessor that
  folds compiler suffixes into compact annotations (`[λ, arity↓]`, `spec
  at context[flags]`)
  - *`script/profiler/symbolicate_profile.py`* — Resolves raw addresses
  via samply's symbolication API
  - *`script/profiler/serve_profile.py`* — Serves demangled profiles to
  Firefox Profiler without re-symbolication
  - *`PROFILER_README.md`* — Documentation including a guide to reading
  demangled names

* [#12533](https://github.com/leanprover/lean4/pull/12533) adds human-friendly demangling of Lean symbol names in runtime
  backtraces. When a Lean program panics, stack traces now show readable
  names instead of mangled C identifiers.
