/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.33.0-rc1 (2026-07-15)" =>
%%%
tag := "release-v4.33.0"
file := "v4.33.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 194 changes landed.
In addition to the 53 feature additions,
and 41 fixes listed below,
there were 12 refactoring changes,
11 documentation improvements,
21 performance improvements,
6 improvements to the test suite,
and 50 other changes.

# Language

````markdown

- [#14352](https://github.com/leanprover/lean4/pull/14352)
  provides the experimental `postprocess_traces tracePostprocessor in cmd` command, which is useful for working with large trees of trace nodes. It runs the command `cmd` and then transforms the traces using a function `tracePostprocessor`. The transformation can affect which nodes are expanded or collaped by default, it can change messages of the trace nodes, and it can add or delete nodes.
  Example:
  ```lean
  module
  meta import Lean.PostprocessTraces
  -- Expand all ancestors of `synthInstance` trace nodes
  -- for better discoverability in large trace trees
  postprocess_traces exposeSubtrees (ofClass `Meta.synthInstance) in
  set_option trace.Meta.isDefEq true in
  set_option trace.Meta.synthInstance true in
  def x ...
  ```

- [#14375](https://github.com/leanprover/lean4/pull/14375)
  adds proper borrow annotations to `Syntax.structEq`. They are needed because it is so early in bootstrapping that it routes through `Substring`'s bootstrapping wrappers without borrow annotations. They are relevant because `Syntax.structEq` ends up getting called transitively from `alphaEq`.

- [#14196](https://github.com/leanprover/lean4/pull/14196)
  improves on the warnings and errors regarding reducibility attributes. Partially addresses #13351.

- [#14361](https://github.com/leanprover/lean4/pull/14361)
  optimizes `applyAbstractResult?` by attempting to skip the `check` invocation used to propagate universe constraints. The optimization is very simple: it checks whether the result contains any metavariables that may be assigned.

- [#14333](https://github.com/leanprover/lean4/pull/14333)
  makes the `@[deprecated]` attribute error when deprecating a declaration in favor of itself.

- [#14325](https://github.com/leanprover/lean4/pull/14325)
  adds a linter which warns on `open` statements which do not in fact open all namespaces which end in the given name.

- [#14335](https://github.com/leanprover/lean4/pull/14335)
  makes `partial_fixpoint` report a helpful monotonicity error instead of a confusing `Unknown constant` error when a non-monadic definition uses a nested recursive call (e.g. `f (f x)`), which requires the function to be tail recursive.

- [#14330](https://github.com/leanprover/lean4/pull/14330)
  makes `tryResolve` assign the goal metavariable directly after successfully unifying the goal type with the candidate instance type, instead of re-checking the types with `isDefEq`. The recheck is redundant for metavariable-free goals and can be expensive.

- [#14259](https://github.com/leanprover/lean4/pull/14259)
  adds a hint to a `unusedVariables` linter, suggesting to rename the unreferenced name with an underscore.

- [#14153](https://github.com/leanprover/lean4/pull/14153)
  adds `Insert` instances for `NameMap` and `NameSet`.

- [#13956](https://github.com/leanprover/lean4/pull/13956)
  makes the kernel's `(kernel) deep recursion detected` error deterministic by bounding kernel type checking with the existing `maxRecDepth` option instead of the physical stack size. The limit previously depended on the native stack, so it varied across platforms, builds, and optimization levels and could not be reproduced reliably; it is now a function of `maxRecDepth` alone and is raised the usual way with `set_option maxRecDepth <num>`.

- [#14297](https://github.com/leanprover/lean4/pull/14297)
  makes a bare `return` inside a `match (dependent := true)` branch of a `do` block target the dependently-refined branch type, so a branch like `| 0 => return 0` type-checks against the refined `do`-block result type without wrapping it in a nested `(do …)`.

- [#13895](https://github.com/leanprover/lean4/pull/13895)
  enables the `backward.isDefEq.respectTransparency.types` option by default. When assigning a metavariable at reducible, instances or implicit transparency, this means that the metavariable's and its assigned value's types are compared at implicit, previously default, transparency. It also makes many existing declarations implicit-reducible. This change increases users' control over what is being unfolded, improving scalability for large projects.

- [#14249](https://github.com/leanprover/lean4/pull/14249)
  extends `dupNamespace` linter to allow users to opt-in via `linter.extra.dupNamespace.consecutiveOnly` option to check non-consecutive repeated usages of namespace components. By default, only consecutive ones are checked. Opting in for non-consecutive checks matches the behaviour introduced in [mathlib4#39793](https://github.com/leanprover-community/mathlib4/pull/39793).

- [#14247](https://github.com/leanprover/lean4/pull/14247)
  fixes an error ("Couldn't interpret binder") when a docstring is attached to a `coinductive` predicate and `doc.verso` is enabled.

- [#14234](https://github.com/leanprover/lean4/pull/14234)
  fixes autocompletion (and other InfoTree-driven consumers such as the interactive term goal and hover popups) to see the augmented `openDecls` and `options` when the cursor is under a term-level `open ... in <term>` or `set_option ... in <term>` scope. Previously both elaborators only updated the runtime `Core.Context` via `withTheReader` / `withOptions`, but did not push a corresponding `PartialContextInfo.commandCtx` node into the InfoTree; consumers therefore saw the outer command's `openDecls` / `options` and, for example, offered names fully-qualified even under a matching `open`, or rendered pretty-printed goals ignoring a local `set_option pp.fullNames true`.

- [#14214](https://github.com/leanprover/lean4/pull/14214)
  reverts leanprover/lean4#14193 . The benchmark issue that it was a reaction to was almost certainly not caused by it, but was instead noise; the actual gains were modest compared to the downside of a more complex mental model for users.

- [#14200](https://github.com/leanprover/lean4/pull/14200)
  causes docstrings in macros to follow the value of the `doc.verso` option at the the macro's definition site, rather than its use site. Before, the use-site option was used, making it impossible to use macros in contexts where the option's value disagreed because the parsed format was incorrect. Now, the parsed format in the syntax is used regardless of the option's local setting.

- [#14198](https://github.com/leanprover/lean4/pull/14198)
  fixes a bug where references to parameters by names failed for unbracketed binders, in the presence of `_` parameters, and in macro-generated declarations.

- [#14191](https://github.com/leanprover/lean4/pull/14191)
  fixes an issue where escaped content at the start of a line in a valid block-opening positon in Verso content was skipped as if it were whitespace.

- [#14193](https://github.com/leanprover/lean4/pull/14193)
  restricts the options propagated to parsers to those that start with `doc.verso`, to improve performance over #14189.

- [#14189](https://github.com/leanprover/lean4/pull/14189)
  propagates the values of options from set_option ... in ... forms used in commands, terms, and tactics into the parsing of the body. This means that Verso syntax can be more conveniently enabled or disabled, and brings `set_option ... in ...` semantically in line with `open ... in ...`.

- [#14115](https://github.com/leanprover/lean4/pull/14115)
  adds support for extensible Markdown rendering of Verso docstrings.

- [#14181](https://github.com/leanprover/lean4/pull/14181)
  lets `match` use `Float` and `Float32` literals as patterns, just like `String`, `UInt64`, and other literal types. The compiler compares the scrutinee against each literal using the type's `DecidableEq` instance (bit-pattern equality), so e.g. `0.0` and `-0.0` are distinct patterns. Negative literals such as `-1.5` are supported.

- [#14114](https://github.com/leanprover/lean4/pull/14114)
  changes the Hoare-triple notation so `;` introduces the exceptional postcondition as a single `EPred` term rather than a list of exception cases wrapped in `epost⟨…⟩`. This lets the notation express an `epost` variable or any `EPred`, and makes `epost⟨…⟩` an ordinary explicit constructor written in that slot.

- [#13637](https://github.com/leanprover/lean4/pull/13637)
  splits `TransparencyMode.instances` and `ReducibilityStatus.implicitReducible` into two transparency levels so that `@[implicit_reducible]` annotations no longer have the side effects `@[instance_reducible]` has, such as allowing type class search to see through the marked declarations.

- [#14120](https://github.com/leanprover/lean4/pull/14120)
  fixes language server-oriented API such as `findDocString?` that sources its information from `.olean.server` under the module system to also work on the cmdline if the module in question is imported with `all`.

- [#14112](https://github.com/leanprover/lean4/pull/14112)
  adds the `wait_for_expected_type%` term elaborator, which elaborates its argument against the expected type but postpones while that type is an unassigned metavariable. This lets a notation defer an assertion until an `outParam` is resolved by instance synthesis, so a bare lambda checks against the folded carrier instead of unfolding it into a pointwise function lattice.

````

# Library

````markdown

- [#14303](https://github.com/leanprover/lean4/pull/14303)
  removes helper definitions used by the builtin simprocs for basic types from the respective namespaces.

- [#14302](https://github.com/leanprover/lean4/pull/14302)
  moves three public lemmas about `ExceptT` out of `Std.Internal.Do.WP.Lemmas` (an internal module) to `Init.Control.Lawful.Instances`, where the rest of the `ExceptT` lemmas live.

- [#14293](https://github.com/leanprover/lean4/pull/14293)
  moves the public declaration `Function.Injective.leftInverse` out of `Init.Grind` and into `Init.Data.Function`.

- [#14255](https://github.com/leanprover/lean4/pull/14255)
  renames `Int.Linear` to `Int.Internal.Linear` to make it more clear that these are internal implementation details of `omega`/`grind`/`simp +arith` and should not be relied on directly by users.

- [#14265](https://github.com/leanprover/lean4/pull/14265)
  moves various declarations that were polluting public namespaces into internal namespaces (like `Lean`).

- [#14269](https://github.com/leanprover/lean4/pull/14269)
  makes Windows transition times use ceil when converting seconds, which avoids dropping fractional seconds and causing off-by-one behavior.

- [#14231](https://github.com/leanprover/lean4/pull/14231)
  marks `Array.back`, `Array.back!`, and `Array.back?` as `@[expose]`, so that in a downstream module their bodies are available for definitional reduction. Previously `decide` could not evaluate goals such as `#[1, 2, 3].back? = some 3` from another module, even though the `getElem?`/`size` accessors these functions are defined in terms of are already exposed.

- [#14267](https://github.com/leanprover/lean4/pull/14267)
  makes `Fin.foldl` reduce in the kernel by marking its inner `loop` `semireducible` (well-founded definitions are `irreducible` by default) and exposing `foldl`, so the kernel's special support for well-founded recursion on `Nat` applies. Previously `Fin.foldl` got stuck under `decide`/`#reduce`/`Decidable`, unlike the already-reducing `Fin.foldr`:

  ```lean
  example : Fin.foldl 8 (fun a i => a + i.val) 0 = 28 := by decide  -- now succeeds
  ```

- [#13804](https://github.com/leanprover/lean4/pull/13804)
  adds the parsing of Posix TZ String (generating a `RecurringRule` type) in TzIf V2 and V3 footer so lean can generate timezone transitions in case the timestamp is not covered by the transitions array in `ZoneRules`.

- [#14263](https://github.com/leanprover/lean4/pull/14263)
  renames `IO.AsyncList` to `Lean.AsyncList` to avoid polluting the public `IO` namespace.

- [#14260](https://github.com/leanprover/lean4/pull/14260)
  moves some declarations in `Lean.Data.Lsp.Communication` that were polluting the global `IO.FS.Stream` namespace into an internal namespace.

- [#14258](https://github.com/leanprover/lean4/pull/14258)
  moves the declarations in `Lean.Data.Lsp.Utf16` from `Char` to `Char.Internal` and from `String` to `String.Internal`, so that the `String` namespace is not polluted in this implementation module.

- [#14256](https://github.com/leanprover/lean4/pull/14256)
  renames the `LLVM` namespace to `Lean.LLVM` in order to reduce pollution of the global namespace.

- [#14252](https://github.com/leanprover/lean4/pull/14252)
  speeds up `Selectable.one`, `Selectable.combine`, and `Selectable.tryOne` by using a cheap randomness source as opposed to calling into `getRandomBytes` every time.

- [#14244](https://github.com/leanprover/lean4/pull/14244)
  replaces "can seen" with "can be seen" in the documentation of `Quot` and rewraps the paragraph to fit 100 columns without splitting short snippets.

- [#14212](https://github.com/leanprover/lean4/pull/14212)
  adds `List.Nodup.length_le_of_subset`: a duplicate-free list that is a subset of another list is no longer than that list. This is currently only available in Batteries (via the `Subperm` API); here it is proved directly by induction.

- [#14211](https://github.com/leanprover/lean4/pull/14211)
  adds `List.perm_ext_iff_of_nodup`: two duplicate-free lists are permutations of each other if and only if they have the same elements. This is currently only available in Batteries (where it is proved via `Subperm`); here it is proved directly from `perm_iff_count`.

- [#14210](https://github.com/leanprover/lean4/pull/14210)
  adds the round-trip lemmas between `List.idxOf` and indexing: `List.getElem_idxOf` (`xs[xs.idxOf x] = x` when `x` occurs in `xs`) and `List.Nodup.idxOf_getElem` (`idxOf xs[i] xs = i` for a duplicate-free `xs`). These are currently only available in Batteries.

- [#14216](https://github.com/leanprover/lean4/pull/14216)
  marks `Nat.ne_of_gt` as `protected` so that it must be referred to by its fully qualified name, consistent with the surrounding `Nat` order lemmas. In-namespace references are updated to the qualified name accordingly.

- [#14209](https://github.com/leanprover/lean4/pull/14209)
  adds `List.pairwise_lt_finRange`, `List.pairwise_le_finRange`, and `List.nodup_finRange`, stating that `List.finRange n` is strictly increasing, increasing, and free of duplicates. These are basic facts about `finRange` currently only available in Batteries.

- [#14177](https://github.com/leanprover/lean4/pull/14177)
  reduces the aggressiveness of e-matching for `List.count` and `Array.count`. Previously, any invocation of count would directly trigger theory about filter. However, given that `count` has its own set of `grind` annotations, we believe that `count` should only start connecting with `filter`, when an invocation of `filter` is already available in the e-graph. This way we do not unnecessarily trigger `filter` theory from `count`.

- [#14194](https://github.com/leanprover/lean4/pull/14194)
  reduces the aggressiveness of e-matching for `eraseIdx` by not automatically translating into `drop`/`take` anymore at every opportunity.

- [#14192](https://github.com/leanprover/lean4/pull/14192)
  reduces the aggressiveness of e-matching annotations for bounding the result of `count` operations above by the size of their container. They now only get triggered when the size and count operations are both already in the e-graph. Similarly to how find's annotations work.

- [#14190](https://github.com/leanprover/lean4/pull/14190)
  adds two small, independent pieces of `Lean.Order.CompleteLattice` infrastructure used by the `Std.Internal.Do` verification framework.

- [#14182](https://github.com/leanprover/lean4/pull/14182)
  stops automatically connected `findIdx` to `findIdx?` through e-matching whenever `findIdx` is available and instead only does so when `findIdx` and `findIdx?` are available.

- [#13799](https://github.com/leanprover/lean4/pull/13799)
  fixes the `aligned` types and order of the names so `Week.Ordinal.OfMonth` now is `Week.OfMonth.Ordinal` and we have `Week.OfMonth.Aligned.Ordinal` that is a really big type but it express that we can have from 1 to 5 aligned weeks.

- [#14180](https://github.com/leanprover/lean4/pull/14180)
  implements a `DecidableEq Float` instance, which checks for equality of the underlying bit patterns.

- [#14178](https://github.com/leanprover/lean4/pull/14178)
  teaches grind about the fact that it might be interesting to work with `count a xs = 0 ↔ a ∉ xs` once `count a xs` and `a ∈ xs` have appeared in the e-graph.

- [#14116](https://github.com/leanprover/lean4/pull/14116)
  fixes the deadlock using `Selectable.combine` and also fixes a simple problem with recursive mutexes in `Selectable.one`. This PR fixes #14090

- [#14174](https://github.com/leanprover/lean4/pull/14174)
  updates the docstrings for `Std.Time.GenericFormat.parse` and `Std.Time.GenericFormat.parse!` to say that they parse into `DateTime`, matching their return types.

- [#14110](https://github.com/leanprover/lean4/pull/14110)
  completely rewrites the implementation of `Float.ofScientific`.

- [#14091](https://github.com/leanprover/lean4/pull/14091)
  changes the definition of the `Float` and `Float32` types to wrap the `Float.Model` type introduced in #14079.

- [#14079](https://github.com/leanprover/lean4/pull/14079)
  adds types `Float.Model` and `Float32.Model` which will serve as logical models for the `Float` and `Float32` types.

- [#14034](https://github.com/leanprover/lean4/pull/14034)
  adds the Hoare triple lemma `Triple.observe` to `Std.Do`. It proves a triple for `prog` from a specification of a stateless program `obs`: observing the postcondition `Q` of `obs` (via `h`) and using `Q` to establish `wp⟦prog⟧ Post` (via `hgoal`) yields `⦃Pre⦄ prog ⦃Post⦄`. The premise `hp` requires `obs` to be stateless: its successful runs leave the state unchanged, which holds for every program of a stateless monad such as `Except`.

- [#14067](https://github.com/leanprover/lean4/pull/14067)
  adds the weakest-precondition spec lemma `Spec.monadLift_Id` so that `mvcgen`/`mvcgen'` can discharge a do-bind that lifts an `Id` value into a `Pure`/`WPMonad` transformer stack (for example `let x ← (pure 5 : Id Nat)` inside `StateT Nat Id`).

- [#14078](https://github.com/leanprover/lean4/pull/14078)
  fixes a bug in the `IntX.ofIntClamp` family of functions.

````

# Tactics

````markdown

- [#14393](https://github.com/leanprover/lean4/pull/14393)
  implements `grind` propagators that evaluate `BitVec` operations on literals

- [#14392](https://github.com/leanprover/lean4/pull/14392)
  adds a new `liaSteps` configuration option to `grind`. The motivation is to quickly interrupt the search for hard linear integer arithmetic problems.

- [#14390](https://github.com/leanprover/lean4/pull/14390)
  fixes an issue in the `grind` ring solver. When a ring `R` does not satisfy `[NoNatZeroDivisors R]`, polynomial simplification could lose information, affecting completeness.

- [#14195](https://github.com/leanprover/lean4/pull/14195)
  extends `vcgen` with automatic frame inference: the `@[frameproc]` attribute lets a program type register how it frames a resource, and `vcgen` then carries that resource across a call without the user specifying an explicit `frames` clause. Framing is no longer tied to the lattice meet but works for any join-preserving frame operator, so cost budgets, separation-logic footprints, and trace invariants frame through the same mechanism.

- [#14379](https://github.com/leanprover/lean4/pull/14379)
  fixes a bootstrapping issue in the `grind` normalizer. The `BitVec.ofNatLT` normalization theorem must be added to the `grind` normalization set **before** we process `Init/Data/BitVec/Lemmas.lean`. Otherwise, patterns are not properly normalized.

- [#14373](https://github.com/leanprover/lean4/pull/14373)
  fixes nontermination in `grind` triggered by constraints of the form `0 ∣ p`.

- [#14371](https://github.com/leanprover/lean4/pull/14371)
  fixes two bugs in `grind` caused by non-normalized bitvector literals. `BitVec.ofNatLT` literals and out-of-range `OfNat.ofNat` literals (e.g., `(17 : BitVec 4)`) were not reduced to the `OfNat.ofNat` normal form used by `grind`, so two representations of the same value were treated as distinct values, and `grind` produced invalid proofs rejected by the kernel:

  ```lean
  example (x : BitVec 4) (_h1 : x = BitVec.ofNatLT 1 (by decide)) (_h2 : x = 1#4) : True := by
    grind -- kernel error before this PR
  ```

- [#14370](https://github.com/leanprover/lean4/pull/14370)
  fixes a bug in the `BitVec` simproc when `bitVecOfNat := false`. This bug
  affects `grind` since it uses `bitVecOfNat := false`. Here is an example reported by Henrik
  that exposed the issue.

- [#14358](https://github.com/leanprover/lean4/pull/14358)
  implements a fast path for `grind`'s internal envelope type `Ring.OfSemiring.Q type`.

- [#14346](https://github.com/leanprover/lean4/pull/14346)
  optimizes the construction of the `grind`-relevant instances for the auxiliary `grind` type `IntModule.OfNatModule.Q`. It was a major bottleneck in Mathlib.

- [#14314](https://github.com/leanprover/lean4/pull/14314)
  ensures the `shareCommon` internal cache is reused at `repairAndShare`.

- [#14299](https://github.com/leanprover/lean4/pull/14299)
  makes `shareCommon` maintain the `SymM` representation invariants used by `grind` and `Sym.simp`: reducible constants are eagerly unfolded, and kernel projections are folded into projection function applications. These invariants were previously established only by the `grind` preprocessor and were easy to violate from user simprocs and internal code paths (e.g., `Sym.inferType` returns types from environment signatures that were never preprocessed), producing silent E-matching and indexing failures. Violations are now detected when terms enter the table of maximally shared terms and repaired automatically.

- [#14295](https://github.com/leanprover/lean4/pull/14295)
  lets `vcgen` handle a program wrapped in an `mdata` node, such as the `save_info` annotation left behind by spec elaboration, instead of failing with an internal error.

- [#14290](https://github.com/leanprover/lean4/pull/14290)
  makes `int_toBitVec` SymM compatible by splitting it into a SymM and a MetaM simp set. Existing users of `int_toBitVec` should now use `int_toBitVec_meta` in their `simp` invocation instead.

- [#14289](https://github.com/leanprover/lean4/pull/14289)
  ensures that `finish?` adds `intros` and `by_contra`, when needed, to the resulting tactic script as preprocessing steps.

- [#14287](https://github.com/leanprover/lean4/pull/14287)
  implements the `rw` tactic for `sym =>` mode.
  It also breaks `Lean/Elab/Tatic/Grind/Sym.lean` into smaller files.

- [#14137](https://github.com/leanprover/lean4/pull/14137)
  adds a pointer-equality fast path to the `Sym` pattern matcher: when a pattern subterm is pointer-equal to the target, it is a closed term equal to the target with no variables to bind, so matching succeeds immediately without traversing the subterm.

- [#14281](https://github.com/leanprover/lean4/pull/14281)
  ensures the RHS of equational theorems is not zeta reduced during preprocessing. This issue was affecting vcgen (see new test by @sgraf812 ).

- [#14280](https://github.com/leanprover/lean4/pull/14280)
  fixes a bug where `sym => apply <rule>` could close a goal with a proof term containing a loose instance metavariable.

- [#14279](https://github.com/leanprover/lean4/pull/14279)
  adds a new `hygienic` parameter to `intro`-like functions in `SymM`.

- [#14278](https://github.com/leanprover/lean4/pull/14278)
  implements the `case => ..` tactic in `sym =>` mode. It is relevant for `vcgen` (see new test). The new feature tries to simulate the `case => ..` tactic in regular tactic mode.

- [#14277](https://github.com/leanprover/lean4/pull/14277)
  fixes spurious `apply` failures in `SymM`.

- [#14241](https://github.com/leanprover/lean4/pull/14241)
  changes the way that structures are handled by `bv_decide`. Previously support for equality of structures in `bv_decide` was limited. Now it will use the `ext_iff` lemmas if available and otherwise not reason about equality of structures. This change should increase the reasoning power of `bv_decide` on structures. However, this is a breaking change and might require users to annotated previously existing structures with `@[ext]` or otherwise define and tag extensionality lemmas for them.

- [#14227](https://github.com/leanprover/lean4/pull/14227)
  refactors the way that `bv_decide` handles `USize` and `ISize`. This is necessary for `SymM` support in `bv_decide` because calling `revert` in `SymM` is illegal.

- [#13830](https://github.com/leanprover/lean4/pull/13830)
  adds automatic `try?` suggestions at common proof sites, gated by three options
  that default to off:

  * `autoTry.onEmptyProof` — suggests on empty proofs and empty subproofs: empty `by`,
    empty `· `, empty `case h => `, and so on.
  * `autoTry.onUnsolvedGoal` — like `autoTry.onEmptyProof`, but also fires on proofs and
    subproofs that already contain some tactics and left a goal unsolved. The suggestion
    is appended to the existing sequence (e.g. `by skip` → `by skip; <found>`).
  * `autoTry.onSorry` — suggests on `sorry` tactics; the suggestion *replaces* the `sorry`.

- [#14205](https://github.com/leanprover/lean4/pull/14205)
  stops the `impossible` tactic combinator to run `cleanup` on the
  goal before negation, as that would defeat the point.

- [#13712](https://github.com/leanprover/lean4/pull/13712)
  makes `exact?`, `apply?`, `rw?`, and `grind +locals` no longer wait for prior async
  theorem bodies in the same file to finish kernel-checking when iterating the current module's
  declarations. Before, these tactics walked `env.constants.map₂`, which forces `env.checked` and
  thus blocks on every pending async branch; in an editor session this manifested as `try?` and
  `exact?` appearing to hang near the top of long files.

- [#14167](https://github.com/leanprover/lean4/pull/14167)
  adds a `frames` clause to the `vcgen` tactic that attaches a state assertion (a frame) to a matched program, so facts about state the program leaves untouched survive a call whose registered spec drops them.

- [#14146](https://github.com/leanprover/lean4/pull/14146)
  renames the experimental Sym-based `mvcgen'` tactic to `vcgen`, including its grind-mode step, the `with` discharging clause, and the `simplifying_assumptions`/`until`/`invariants` syntax. The original `mvcgen` tactic is unchanged.

- [#14142](https://github.com/leanprover/lean4/pull/14142)
  speeds up `mvcgen'` spec lookup by internalizing each matched spec pattern into the `SymM` share table on first lookup, so its instance arguments become pointer-equal to the program's and need not be re-internalized on every later lookup.

- [#14138](https://github.com/leanprover/lean4/pull/14138)
  fixes the error message for `mvcegn' ... with <tac>`. The main motivation for doing so is when we write `mvcgen' with grind` the error message user sees is `unexpected identifier; expected grind`, which cannot be more confusing. That happens because we except a `grind` sequence, syntax category for which is called `grind`.
  I am defining a separate syntax category for discharger tactic called `mvcgenWith`, and throw a more meaningful exception if it is a tactic.

- [#14134](https://github.com/leanprover/lean4/pull/14134)
  speeds up `mvcgen'` matching by internalizing each backward rule's pattern into the `SymM` share table once, when the rule is cached, instead of re-internalizing its instance arguments on every match.

- [#14080](https://github.com/leanprover/lean4/pull/14080)
  extracts a `WP` type class from `WPMonad` so that weakest-precondition reasoning and `mvcgen'` apply to any program type, not only monads. This enables verifying deeply embedded languages: a program type with a `WP` instance but no `WPMonad` instance, for example an inductive command syntax with its own operational semantics, can now be specified with `Triple` and decomposed by `mvcgen'`.

- [#14119](https://github.com/leanprover/lean4/pull/14119)
  fixes `mvcgen`/`mvcgen'` failing to split a `match` whose discriminant telescope is dependent, i.e. when a later discriminant's type mentions an earlier discriminant (such as `match n, h with` where `h : 0 < n`). Abstracting such a matcher previously produced an ill-typed pre-splitter motive.

- [#14107](https://github.com/leanprover/lean4/pull/14107)
  tags `Nat.min_def`, `Nat.max_def`, `Int.min_def`, and `Int.max_def` with the `@[lia]` attribute, so the `lia` tactic instantiates them via E-matching and can prove goals involving `min`/`max` out of the box. This addresses the most common case where `omega` could previously be replaced by `lia` but `lia` could not see the `min`/`max` definitions, requiring a fall back to the full `grind` tactic.

- [#14098](https://github.com/leanprover/lean4/pull/14098)
  adds a builtin `@[lia]` attribute that supplies a small E-matching lemma set to the `lia` tactic. Previously `lia` (the `cutsat`-only `grind` configuration) ran with E-matching disabled, so it could not see definitional lemmas such as `Nat.max_def`. Now `lia` instantiates only the lemmas tagged `@[lia]`, leaving the much larger `@[grind]` set disabled.

- [#14102](https://github.com/leanprover/lean4/pull/14102)
  changes the name `WhileInvariant` from `Std/Internal/SpecLemmas` to `RepeatInvariant`, since in most of the cases it will be called when verifying `forIn` -repeat loops. Also, we add a new abbreviation to construct `RepeatInvarinat`s. This abbreviation specifies a condition `inv` which should hold at the end of each loop itreation (even the breaking one), and a condition `onDone` which should hold in the end of the loop *in addition to `inv`*.
  In the case of a normal `while` loop the latter one could always be taken as negation of the loop condition.

- [#14099](https://github.com/leanprover/lean4/pull/14099)
  adds `⊤` normalisation in `mvcgen'`.
  During the run of `mvcgen`, in particular when introducing extra state arguments, `⊤` might turn into `⊤ s₁ s₂ ⋯ sₙ`.
  I am adding a procedure which constructs the proof of `⊤ s₁ s₂ ⋯ sₙ = ⊤` on the fly and replaces it.

- [#14095](https://github.com/leanprover/lean4/pull/14095)
  makes `mvcgen'` report a clear error when an entailment's assertion lattice is a dependent function type such as `(a : α) → β a → Prop`, instead of looping until it runs out of heartbeats. The order is the ordinary pointwise function order; the limitation is that `mvcgen'`'s peel rule `Lean.Order.le_of_forall_le` cannot currently be applied to a dependent function lattice.

- [#14081](https://github.com/leanprover/lean4/pull/14081)
  unifies how `mvcgen'` turns `@[spec]` annotations into backward rules, makes the annotated priority take effect for equational specs, and rejects `@[spec]` annotations that are neither a Hoare triple, an equation, nor a definition to unfold.

- [#14089](https://github.com/leanprover/lean4/pull/14089)
  lets `mvcgen` and `mvcgen'` apply `@[spec]` theorems whose statement is a reducible abbreviation wrapping a Hoare triple, such as `abbrev foo.spec := ⦃P⦄ foo ⦃Q⦄`. Previously the program stayed stuck because the spec, although registered, was discarded at lookup time.

- [#14015](https://github.com/leanprover/lean4/pull/14015)
  ports the experimental `mvcgen'` tactic to the new `Std.Internal.Do` meta theory, where verification-condition generation works on lattice entailments `pre ⊑ wp x post epost`. Two changes are visible at the proof surface: `mvcgen'` now eagerly introduces all state components as local hypotheses, so more facts reach `grind`; and loop invariants no longer have to restate the exceptional postcondition.

````

# Compiler

```markdown

- [#14372](https://github.com/leanprover/lean4/pull/14372)
  moves `Lean.initializing`, `enableInitializersExecution`, and `isInitializerExecutionEnabled` to `BaseIO` from `IO`.

- [#14365](https://github.com/leanprover/lean4/pull/14365)
  ensures that `unsafe` terms get properly inlined. Previously having some unsafe term `t` occurring inline as `unsafe t` would create a separate auxiliary declaration that might not end up getting inlined.

- [#14343](https://github.com/leanprover/lean4/pull/14343)
  fixes the new 1GB stack size not being used for the main `lean` thread itself, e.g. for serialization or `--run`.

- [#14139](https://github.com/leanprover/lean4/pull/14139)
  disables symbol stripping of our libleanshared.so in release mode again. As it turns out `--strip-unneeded` doesn't only strip symbols that we do not care about.

- [#14272](https://github.com/leanprover/lean4/pull/14272)
  changes `dbgTraceIfShared` to take its message borrowed (`s : @& String`), with the matching `b_obj_arg`/`b_lean_obj_arg` adjustments in the runtime and header. The C implementation only reads the string and never consumed it, so the owned argument leaked on every call; the leak goes unnoticed in typical use because string literals are compiled to persistent constants, which are exempt from reference counting. A dynamically constructed message leaks once per call. Borrowing matches what the implementation actually does and spares callers a reference-count operation. Found while auditing the runtime for the pattern fixed in #14271.

- [#13679](https://github.com/leanprover/lean4/pull/13679)
  fixes an issue where code generation broke when using structures with private fields and types inaccessible in the current scope.

- [#14127](https://github.com/leanprover/lean4/pull/14127)
  fixes a theoretical but not practical race condition on `lean_task_imp.m_canceled` by making it atomic.

- [#14108](https://github.com/leanprover/lean4/pull/14108)
  changes the `m_imp` field of `lean_task` to an atomic. This is necessary because  in `get_task_state_core` we access the `m_imp` to see if the task is finished *before* taking the mutex. Thus the memory access as it is done currently is UB.

```

# FFI

```markdown

- [#14184](https://github.com/leanprover/lean4/pull/14184)
  exports a `lean_set_initializing` symbol for users of Lean that need to emulate multiple `withImporting` calls from a C FFI.

```

# Documentation

```markdown

- [#14222](https://github.com/leanprover/lean4/pull/14222)
  converts a number of comments that seem to have been clearly intended as docstrings into docstrings, avoiding those already converted in #13006.

```

# Server

```markdown

- [#11958](https://github.com/leanprover/lean4/pull/11958)
  adjusts the elaborator and snapshot tree system so as not to rerun tactics when whitespace directly following them is changed, preventing loss of progress when preparing to type the next tactic.

- [#14296](https://github.com/leanprover/lean4/pull/14296)
  makes go-to-definition and find-references work on a `let mut` variable that is referenced after a `for` loop (or any construct that threads mutable state through a tuple).

```

# Lake

```markdown

- [#14366](https://github.com/leanprover/lean4/pull/14366)
  fixes `lake new` and `lake init` to not emit library files on the `exe` template. It also fixes a related bug where the commands could sometimes overwrite library files for existing packages.

- [#14300](https://github.com/leanprover/lean4/pull/14300)
  adds the `presetup`, `depTrace`, and `depHash` facets, which provide different views of a module's full set of dependencies. Also, the `setup` facet is no longer buildable on the CLI (as it produces JSON and not artifacts) and now includes full set of transitive import artifacts, fixing their absence from `lake lean`'s `setup.json`.

- [#14364](https://github.com/leanprover/lean4/pull/14364)
  adds `getLakeSharedDynlib` to the Lake API. It is a simple monadic convenience function that retrieves `LakeInstall.sharedDynlib` for the detected Lake installation.

- [#14285](https://github.com/leanprover/lean4/pull/14285)
  makes Lake reconfigure when it cannot read the configuration trace, instead of aborting with `error: compiled configuration is invalid; run with '-R' to reconfigure`. `importConfigFile` already reconfigures automatically for a stale, wrong-toolchain, or partially-malformed trace; an unparsable trace is no more informative than a missing one, so it is now handled the same way — routed into the same `elabConfig (← acquireTrace h) …` path — recovering on its own rather than requiring a manual `-R`. When the trace has no usable `options` field it falls back to `cfg.lakeOpts`, the same options value the fresh-configure branch uses when no trace exists.

- [#14284](https://github.com/leanprover/lean4/pull/14284)
  makes an interrupted Lake configuration recoverable. `importConfigFile` writes the compiled-configuration trace to a buffered handle and then calls `IO.FS.Handle.truncate` — which sets the file size but does not flush buffered writes, as its own docstring notes — before the potentially slow configuration elaboration. A `lake` process killed in that window (an interrupted or cancelled build) leaves the trace on disk as a NUL-byte size placeholder with no `.olean`, so later invocations fail with `error: compiled configuration is invalid; run with '-R' to reconfigure`. Flushing the complete trace before truncating and elaborating means an interruption instead leaves a valid trace and no `.olean`, which Lake's existing up-to-date check already treats as a trigger to reconfigure automatically.

- [#14254](https://github.com/leanprover/lean4/pull/14254)
  adds two new module facets: `linkInfoExport` and `linkInfoNoExport`. They provide information on how to link a module. It also provides `Sync` variants for `buildSharedLib`, `buildLeanSharedLib`, and `buildLeanExe` that work from within a `Job` rather than across them.

- [#14235](https://github.com/leanprover/lean4/pull/14235)
  makes Lake's module archives (`.ltar`) content-stable: byte-identical module outputs now produce a byte-identical archive regardless of the inputs, checkout path, or machine that built them, so input-only changes (e.g. a comment edit in an imported module) upload no new archive bytes and identical outputs deduplicate across revisions on cache services.

- [#14206](https://github.com/leanprover/lean4/pull/14206)
  adapts the deferred docstring check mechanism to use the linter mechanism, presenting an interface akin to that of environment linters. This replaces custom CI setup with an already-used interface. Deferred checks are governed by the option `linter.doc.deferred`.

- [#14240](https://github.com/leanprover/lean4/pull/14240)
  ensures executables are executable when restored from the Lake cache even if they were not originally executable in the cache (e.g., because they were downloaded through `lake cache get`).

- [#14219](https://github.com/leanprover/lean4/pull/14219)
  adds API for retrieving the complete set of core dynamic libraries. In current terms, these are `libleanshared`, `libleanshared_1`, and `libleanshared_2`. and `libInit_shared`. These libraries have different interdependencies on Windows and Unix, so they are modelled with `Dynlib` in order to track this information.

- [#14220](https://github.com/leanprover/lean4/pull/14220)
  adds `Dynlib.runtimeOnlyDeps`. It specifies transitive dependencies that should not be linked, but need to be preloaded for `lean` elaboration when precompiling (e.g., libraries dynamically loaded at runtime via `dlopen`).

- [#14156](https://github.com/leanprover/lean4/pull/14156)
  allows modules which do not depend on any dynamic libraries to toggle `platformIndependent` between `true` and unset without a rebuild.

- [#14130](https://github.com/leanprover/lean4/pull/14130)
  fixes `Package.remoteUrl?` so an empty `remoteUrl` returns `none` and a non-empty `remoteUrl` returns `some remoteUrl`.

- [#13646](https://github.com/leanprover/lean4/pull/13646)
  adds a new Lake package option `requiresModuleSystem`. When a package sets it to `true`, Lake emits a warning whenever a non-module-system file (one without a `module` header) imports a module of the package, both from downstream consumers and from non-module files within the package itself. This signals that the package's API expects the visibility and elaboration semantics of the module system. A companion option `allowNonModules` lets an importing package opt out of these warnings, declaring that it knowingly mixes non-module-system files with module-system dependencies.

```

# Other

```markdown

- [#14354](https://github.com/leanprover/lean4/pull/14354)
  implements a minor optimization at `withExporting/withoutExporting`. When they call `modifyEnv` to toggle `Environment.isExporting`, and `MonadEnv` `MetaM`'s `modifyEnv` wipes all `Core` and `Meta` caches.

- [#14131](https://github.com/leanprover/lean4/pull/14131)
  fixes `finishCommentBlock` so it does not skip a `-` when it is not followed by `/`.

```
