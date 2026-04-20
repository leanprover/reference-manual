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

#doc (Manual) "Lean 4.30.0-rc1 (2026-04-01)" =>
%%%
tag := "release-v4.30.0"
file := "v4.30.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 298 changes landed.
In addition to the 120 feature additions
and 68 fixes listed below,
there were 17 refactoring changes,
8 documentation improvements,
19 performance improvements,
12 improvements to the test suite,
and 54 other changes.

# Language

````markdown

- [#13188](https://github.com/leanprover/lean4/pull/13188)
  extends the `missingDocs` linter to detect and warn about empty doc strings (e.g. `/---/` or `/-- -/`), in addition to missing doc strings. Previously, an empty doc comment would silence the linter even though it provides no documentation value. Now empty doc strings produce a distinct "empty doc string for ..." warning, while `@[inherit_doc]` still suppresses warnings as before.

- [#13192](https://github.com/leanprover/lean4/pull/13192)
  fixes the handling of anonymous dependent `if` (`if _ : cond then ... else ...`) inside `do` blocks when using the new do elaborator.

- [#13011](https://github.com/leanprover/lean4/pull/13011)
  adds a `@[deprecated_arg]` attribute that marks individual function parameters as deprecated. When a caller uses the old parameter name, the elaborator emits a deprecation warning with a code action hint to rename or delete the argument, and silently forwards the value to the correct binder.

- [#13153](https://github.com/leanprover/lean4/pull/13153)
  registers the new `spec_invariant_type` attribute alongside the old
  `mvcgen_invariant_type`, renames internal identifiers, and replaces the
  hardcoded `Invariant` check in `Spec.lean` with `isSpecInvariantType`.

- [#13117](https://github.com/leanprover/lean4/pull/13117)
  re-enables `#print axioms` under the module system by computing axiom dependencies at olean serialization time. It reverts #8174 and replaces it with a proper fix.

- [#13142](https://github.com/leanprover/lean4/pull/13142)
  replaces the per-level `OLeanLevel → Array α` return type of `exportEntriesFnEx` with a new `OLeanEntries (Array α)` structure that bundles exported, server, and private entries together. This allows extensions to share expensive computation across all three olean levels instead of being called three separate times.

- [#13120](https://github.com/leanprover/lean4/pull/13120)
  reverts the `mvcgen witnesses` syntax addition and undoes the back compat hack in `elabMVCGen`.

- [#13111](https://github.com/leanprover/lean4/pull/13111)
  reverts #12882 which added the `@[mvcgen_witness_type]` tag attribute and `witnesses` section to `mvcgen`. Théophile Wallez confirmed he doesn't need this feature and can get by with `invariants`, so there is no use in having it.

- [#13059](https://github.com/leanprover/lean4/pull/13059)
  switches `normalizeInstance` from using `isMetaSection` to the existing `declName?` pattern (already used by `unsafe` in `BuiltinNotation.lean` and `private_decl%` in `BuiltinTerm.lean`) for determining whether aux defs should be marked `meta`.

- [#12973](https://github.com/leanprover/lean4/pull/12973)
  makes theorems opaque in almost all ways, including in the kernel.

- [#12987](https://github.com/leanprover/lean4/pull/12987)
  extracts the functional (lambda) passed to `brecOn` in structural
  recursion into a named `_f` helper definition (e.g. `foo._f`), similar to
  how well-founded recursion uses `._unary`. This way the functional shows up
  with a helpful name in kernel diagnostics rather than as an anonymous lambda.

- [#13043](https://github.com/leanprover/lean4/pull/13043)
  fixes a bug where `inferInstanceAs` and the default `deriving` handler, when used inside a `meta section`, would create auxiliary definitions (via `normalizeInstance`) that were not marked as `meta`. This caused the compiler to reject the parent `meta` definition with:

  ```
  Invalid `meta` definition `instEmptyCollectionNamePrefixRel`, `instEmptyCollectionNamePrefixRel._aux_1` not marked `meta`
  ```

- [#13029](https://github.com/leanprover/lean4/pull/13029)
  removes the unused `change ... with` tactic syntax.

- [#12897](https://github.com/leanprover/lean4/pull/12897)
  adjusts the results of `inferInstanceAs` and the `def` `deriving` handler to conform to recently strengthened restrictions on reducibility. This change ensures that when deriving or inferring an instance for a semireducible type definition, the definition's RHS is not leaked when the instance is reduced at lower than semireducible transparency.

- [#13005](https://github.com/leanprover/lean4/pull/13005)
  further enforces that all modules used in compile-time execution must be meta imported in preparation for enabling https://github.com/leanprover/lean4/pull/10291

- [#12840](https://github.com/leanprover/lean4/pull/12840)
  fixes an issue where the use of private imports led to unknown namespaces in downstream modules.

- [#12953](https://github.com/leanprover/lean4/pull/12953)
  fixes an issue where the `induction` and `cases` tactics would swallow diagnostics (such as unsolved goals errors) when the `using` clause contains a nested tactic.

- [#12979](https://github.com/leanprover/lean4/pull/12979)
  makes `#print` show the full internal private name (including
  module prefix) in the declaration signature when `pp.privateNames` is
  set to true. Previously, `pp.privateNames` only affected names in the
  body but the signature always stripped the private prefix.

- [#12964](https://github.com/leanprover/lean4/pull/12964)
  fixes an issue where `realizeConst` would generate auxiliary declarations
  (like `_sparseCasesOn`) using the original defining module's private name prefix
  rather than the realizing module's prefix. When two modules independently realized
  the same imported constant, they produced identically-named auxiliary declarations,
  causing "environment already contains" errors on diamond import.

- [#12881](https://github.com/leanprover/lean4/pull/12881)
  adds `Invariant.withEarlyReturnNewDo`, `StringInvariant.withEarlyReturnNewDo`, and `StringSliceInvariant.withEarlyReturnNewDo` which use `Prod` instead of `MProd` for the state tuple, matching the new do elaborator's output. The existing `withEarlyReturn` definitions are reverted to `MProd` for backwards compatibility with the legacy do elaborator. Tests and invariant suggestions are updated to use the `NewDo` variants.

- [#12880](https://github.com/leanprover/lean4/pull/12880)
  applies `@[mvcgen_invariant_type]` to `Std.Do.Invariant` and removes the hard-coded fallback in `isMVCGenInvariantType` that was needed for bootstrapping (cf. #12874). It also extracts `StringInvariant` and `StringSliceInvariant` as named abbreviations tagged with `@[mvcgen_invariant_type]`, so that `mvcgen` classifies string and string slice loop invariants correctly.

- [#12874](https://github.com/leanprover/lean4/pull/12874)
  adds an `@[mvcgen_invariant_type]` tag attribute so that users can mark
  custom types as invariant types for the `mvcgen` tactic. Goals whose type is an
  application of a tagged type are classified as invariants rather than verification
  conditions. The hard-coded check for `Std.Do.Invariant` is kept as a fallback
  until a stage0 update allows applying the attribute directly.

- [#12767](https://github.com/leanprover/lean4/pull/12767)
  makes sure that identifiers with `Meta` or `Simproc` in their name do not show up in library search results.

- [#12866](https://github.com/leanprover/lean4/pull/12866)
  adds `optType` support to the `doPatDecl` parser, allowing
  `let ⟨width, height⟩ : Nat × Nat ← action` in do-notation. Previously, only
  the less ergonomic `let ⟨width, height⟩ : Nat × Nat := ← action` workaround
  was available. The type annotation is propagated to the monadic action as an
  expected type, matching `doIdDecl`'s existing behavior.

- [#12698](https://github.com/leanprover/lean4/pull/12698)
  adds a `result? : Option TraceResult` field to `TraceData` and populates it in `withTraceNode` and `withTraceNodeBefore`, so that metaprograms walking trace trees can determine success/failure structurally instead of string-matching on emoji.

- [#12233](https://github.com/leanprover/lean4/pull/12233)
  replaces the default `instantiateMVars` implementation with a two-pass variant that fuses fvar substitution into the traversal, avoiding separate `replace_fvars` calls for delayed-assigned MVars and preserving sharing. The old single-pass implementation is removed entirely.

- [#12560](https://github.com/leanprover/lean4/pull/12560)
  changes the way the linting for `linter.unusedSimpArgs` gets the value from the environment. This is achieved by using the appropriate helper functions defined in `Lean.Linter.Basic`.

- [#11427](https://github.com/leanprover/lean4/pull/11427)
  modifies `#eval e` to elaborate `e` with section variables in scope. While evaluating expressions with free variables is not possible, this lets `#eval` give a better error message than "unknown identifier."

- [#12841](https://github.com/leanprover/lean4/pull/12841)
  changes the elaboration of the `structure`/`class` commands so that default values have later fields in context as well. This allows field defaults to depend on fields that come both before and after them. While this was already the case for inherited fields to some degree, it now applies uniformly to all fields. Additionally, when elaborating the default value for a field, all fields that depend on it are cleared from the context to avoid situations where the default value depends on itself.

- [#12749](https://github.com/leanprover/lean4/pull/12749)
  changes "structure-like" terminology to "non-recursive structure" across internal documentation, error messages, the metaprogramming API, and the kernel, to clarify Lean's type theory. A *structure* is a one-constructor inductive type with no indices — these can be created by either the `structure` or `inductive` commands — and are supported by the primitive `Expr.proj` projections. Only *non-recursive* structures have an eta conversion rule. The PR description contains the APIs that were renamed.

- [#12662](https://github.com/leanprover/lean4/pull/12662)
  adjusts the module parser to set the leading whitespace of the first token to the whitespace up to that token. If there are no actual tokens in the file, the leading whitespace is set on the final (empty) EOI token. This ensures that we do not lose the initial whitespace (e.g. comments) of a file in `Syntax`.

- [#12325](https://github.com/leanprover/lean4/pull/12325)
  adds a warning to any `def` of class type that does not also declare an appropriate reducibility.

- [#12817](https://github.com/leanprover/lean4/pull/12817)
  moves the universe-level-count check from `unfold_definition_core` into `is_delta`, establishing the invariant that if `is_delta` succeeds then `unfold_definition` also succeeds. This prevents a crash (SIGSEGV or garbled error) that occurred when call sites in `lazy_delta_reduction_step` unconditionally dereferenced the result of `unfold_definition` even on a level-parameter-count mismatch.

- [#12802](https://github.com/leanprover/lean4/pull/12802)
  re-applies https://github.com/leanprover/lean4/pull/12757 (reverted in https://github.com/leanprover/lean4/pull/12801) with the `release-ci` label to test whether it causes the async extension PANIC seen in the v4.29.0-rc5 tag CI.

- [#12789](https://github.com/leanprover/lean4/pull/12789)
  skips the noncomputable pre-check in `processDefDeriving` when the instance type is `Prop`. Since proofs are erased by the compiler, computability is irrelevant for `Prop`-valued instances.

- [#12776](https://github.com/leanprover/lean4/pull/12776)
  fixes `@[implicit_reducible]` on well-founded recursive definitions.

- [#12778](https://github.com/leanprover/lean4/pull/12778)
  fixes an inconsistency in `getStuckMVar?` where the instance argument to class projection functions and auxiliary parent projections was not whnf-normalized before checking for stuck metavariables. Every other case in `getStuckMVar?` (recursors, quotient recursors, `.proj` nodes) normalizes the major argument via `whnf` before recursing — class projection functions and aux parent projections were the exception.

- [#12756](https://github.com/leanprover/lean4/pull/12756)
  adds `deriving noncomputable instance Foo for Bar` syntax so that delta-derived instances can be marked noncomputable. Previously, when the underlying instance was noncomputable, `deriving instance` would fail with an opaque async compilation error.

- [#12699](https://github.com/leanprover/lean4/pull/12699)
  gives the `generate` function's "apply @Foo to Goal" trace nodes their own trace sub-class `Meta.synthInstance.apply` instead of sharing the parent `Meta.synthInstance` class.

- [#12701](https://github.com/leanprover/lean4/pull/12701)
  fixes a gap in how `@[implicit_reducible]` is assigned to parent projections during structure elaboration.

- [#12719](https://github.com/leanprover/lean4/pull/12719)
  marks `levelZero` and `Level.ofNat` as `@[implicit_reducible]` so that `Level.ofNat 0 =?= Level.zero` succeeds when the definitional equality checker respects transparency annotations. Without this, coercions between structures with implicit `Level` parameters fail, as reported by @FLDutchmann on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/near/576131374).

- [#12695](https://github.com/leanprover/lean4/pull/12695)
  fixes a bug in `Meta.zetaReduce` where `have` expressions were not being zeta reduced. It also adds a feature where applications of local functions are beta reduced, and another where zeta-delta reduction can be disabled. These are all controllable by flags:
  - `zetaDelta` (default: true) enables unfolding local definitions
  - `zetaHave` (default: true) enables zeta reducing `have` expressions
  - `beta` (default: true) enables beta reducing applications of local definitions

- [#12696](https://github.com/leanprover/lean4/pull/12696)
  fixes a test case reported by Alexander Bentkamp that runs into a heartbeat limit due to daring use of `withDefault` `rfl` in `mvcgen`.

- [#12680](https://github.com/leanprover/lean4/pull/12680)
  fixes an issue where `mutual public structure` would have a private constructor. The fix copies the fix from #11940.

- [#12602](https://github.com/leanprover/lean4/pull/12602)
  restricts and in particular simplifies the semantics of `evalConst` with `(checkMeta := true)` (which is the default): it now fails iff the passed constant name is not `meta` (and we are under `module`).

- [#12603](https://github.com/leanprover/lean4/pull/12603)
  adds a feature where `inductive` constructors can override the binder kinds of the type's parameters, like in #9480 for `structure`. For example, it's possible to make `x` explicit in the constructor `Eq.refl`, rather than implicit:
  ```lean
  inductive Eq {α : Type u} (x : α) : α → Prop where
    | refl (x) : Eq x x
  ```

- [#12647](https://github.com/leanprover/lean4/pull/12647)
  adds the missing `popScopes` call to `withNamespace`, which previously
  only dropped scopes from the elaborator's `Command.State` but did not pop the
  environment's `ScopedEnvExtension` state stacks. This caused scoped syntax
  declarations to leak keywords outside their namespace when `withNamespace` had
  been called.

- [#12673](https://github.com/leanprover/lean4/pull/12673)
  allows for a leightweight version of dependent `match` in the new `do` elaborator: discriminant types get abstracted over previous discriminants. The match result type and the local context still are not considered for abstraction. For example, if both `i : Nat` and `h : i < len` are discrminants, then if an alternative matches `i` with `0`, we also have `h : 0 < len`:

  ```lean
  example {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
    let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
      match i, h with
      | 0,   _ => pure b
      | i+1, h =>
        have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
        have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
        have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
        match (← f as[as.size - 1 - i] (Array.getElem_mem this) b) with
        | ForInStep.done b  => pure b
        | ForInStep.yield b => loop i (Nat.le_of_lt h') b
    loop as.size (Nat.le_refl _) b
  ```

- [#12608](https://github.com/leanprover/lean4/pull/12608)
  continues #9674, cleaning up binder annotations inside the bodies of `let rec` and `where` definitions.

- [#12666](https://github.com/leanprover/lean4/pull/12666)
  fixes spurious unused variable warnings for variables used in non-atomic match discriminants in `do` notation. For example, in `match Json.parse s >>= fromJson? with`, the variable `s` would be reported as unused.

- [#12661](https://github.com/leanprover/lean4/pull/12661)
  fixes false-positive "unused variable" warnings for mutable variables reassigned inside `try`/`catch` blocks with the new do elaborator.

````

# Library

```markdown

- [#13175](https://github.com/leanprover/lean4/pull/13175)
  fixes the wrong behavior of a stream in http_body.

- [#12144](https://github.com/leanprover/lean4/pull/12144)
  introduces the `Body` type class, the `ChunkStream` and `Full` types that are used to represent streaming bodies of Requests and Responses.

- [#13129](https://github.com/leanprover/lean4/pull/13129)
  implements verification infrastructure for backwards patterns that is analogous to the existing infrastructure for forward patterns. Based on this it adds verification for the `skipSuffix?`, `endsWith` and `dropSuffix?` functions on strings.

- [#12912](https://github.com/leanprover/lean4/pull/12912)
  adds trivial lemmas about `ExceptCpsT.runK` to match the existing lemmas about `.run`.

- [#13109](https://github.com/leanprover/lean4/pull/13109)
  adds lemmas about the `String` operations `drop`, `dropEnd`, `take`, `takeEnd`.

- [#13106](https://github.com/leanprover/lean4/pull/13106)
  verifies `String.Pos.nextn` by providing the low-level API `nextn_zero`/`nextn_add_one` as well as a `Splits` lemma.

- [#13105](https://github.com/leanprover/lean4/pull/13105)
  proves `theorem front?_eq {s : String} : s.front? = s.toList.head?` and related results.

- [#13098](https://github.com/leanprover/lean4/pull/13098)
  generalizes some theorems about `Nat.ofDigitChars` which were needlessly restricted to base 10.

- [#13096](https://github.com/leanprover/lean4/pull/13096)
  show the trivial result that given `c : l.Cursor`, we have that `c.pos ≤ l.length`.

- [#13092](https://github.com/leanprover/lean4/pull/13092)
  fixes an issue where `Std.Iter.joinString` had an extra universe parameter because of an `IteratorLoop` instance which was actually unnecessary.

- [#13091](https://github.com/leanprover/lean4/pull/13091)
  adds the function `String.Slice.join` and adds lemmas about `String.join` and `String.Slice.join`.

- [#13090](https://github.com/leanprover/lean4/pull/13090)
  adds the single lemma `Char.toNat_mk`.

- [#13061](https://github.com/leanprover/lean4/pull/13061)
  adds lemmas about `BEq` on `List String.Slice`.

- [#13058](https://github.com/leanprover/lean4/pull/13058)
  adds `EquivBEq` and `LawfulHashable` instances to `String.Slice`.

- [#13057](https://github.com/leanprover/lean4/pull/13057)
  adds some variants of existing lemmas about `String.toNat?` and friends.

- [#13056](https://github.com/leanprover/lean4/pull/13056)
  adds the functions `Std.Iter.joinString` and `Std.Iter.intercalateString`.

- [#13054](https://github.com/leanprover/lean4/pull/13054)
  adds the simproc String.reduceToSingleton`, which is disabled by default and turns `"c"` into `String.singleton 'c'`.

- [#13003](https://github.com/leanprover/lean4/pull/13003)
  reorganizes the instances `ToString Int` and `Repr Int` so that they both point at a common definition `Int.repr` (the same setup is used for `Nat`). It then verifies the functions `Int.repr`, `String.isInt` and `String.toInt`.

- [#12999](https://github.com/leanprover/lean4/pull/12999)
  verifies the `String.dropPrefix?` function for our various patterns.

- [#12469](https://github.com/leanprover/lean4/pull/12469)
  adds the `Inhabited` instance for `Thunk`.

- [#12128](https://github.com/leanprover/lean4/pull/12128)
  introduces the `URI` data type.

- [#12990](https://github.com/leanprover/lean4/pull/12990)
  verifies the `String.startsWith` and `String.skipPrefix?` functions for our various pattern types.

- [#12988](https://github.com/leanprover/lean4/pull/12988)
  introduces the functions `String.Slice.skipPrefix?`, `String.Slice.Pos.skip?`, `String.Slice.skipPrefixWhile`, `String.Slice.Pos.skipWhile` and redefines `String.Slice.takeWhile` and `String.Slice.dropWhile` to use these new functions.

- [#12984](https://github.com/leanprover/lean4/pull/12984)
  renames the function `ForwardPattern.dropPrefix?` to `ForwardPattern.skipPrefix`?

- [#12828](https://github.com/leanprover/lean4/pull/12828)
  redefines the `String.isNat` function to use less state and perform short-circuiting. It then verifies the `String.isNat` and `String.toNat?` functions.

- [#12980](https://github.com/leanprover/lean4/pull/12980)
  adds theorems about `Char`, `Nat` and `List`.

- [#12977](https://github.com/leanprover/lean4/pull/12977)
  removes most of the `simp` annotations added in #12945, to mitigate the performance impact. The lemmas remain.

- [#12966](https://github.com/leanprover/lean4/pull/12966)
  adds simp lemmas that simplify `n.digitChar = '0'` to `n = 0` and a simproc that simplifies `n.digitChar = '!'` to `False`.

- [#12924](https://github.com/leanprover/lean4/pull/12924)
  fixes a regression introduced in Lean 4.29.0-rc2 where `simp` no longer simplifies inside type class instance arguments due to the `backward.isDefEq.respectTransparency` change. This breaks proofs where a term like `(a :: l).length` appears both in the main expression and inside implicit instance arguments (e.g., determining a `BitVec` width).

- [#12950](https://github.com/leanprover/lean4/pull/12950)
  adds simp lemmas equating kernel-friendly function names with their operator notation equivalents: `Nat.land_eq`, `Nat.lor_eq`, `Nat.xor_eq`, `Nat.shiftLeft_eq'`, `Nat.shiftRight_eq'`, and `Bool.rec_eq`. These are useful when proofs involve reflection and need to simplify kernel-reduced terms back to operator notation.

- [#12955](https://github.com/leanprover/lean4/pull/12955)
  fixes the windows build with signal handlers.

- [#12945](https://github.com/leanprover/lean4/pull/12945)
  adds a few `forall` lemmas to the `simp` set.

- [#12900](https://github.com/leanprover/lean4/pull/12900)
  fixes some process signals that were incorrectly numbered.

- [#12127](https://github.com/leanprover/lean4/pull/12127)
  introduces the `Headers` data type, that provides a good and convenient abstraction for parsing, querying, and encoding HTTP/1.1 headers.

- [#12936](https://github.com/leanprover/lean4/pull/12936)
  fixes `Id.run_seqLeft` and `Id.run_seqRight` to apply when the two monad results are different.

- [#12909](https://github.com/leanprover/lean4/pull/12909)
  fixes the typo in `Int.sq_nonnneg`.

- [#12919](https://github.com/leanprover/lean4/pull/12919)
  fixes the `HSub PlainTime Duration` instance, which had its operands reversed: it computed `duration - time` instead of `time - duration`. For example, subtracting 2 minutes from `time("13:02:01")` would give `time("10:57:59")` rather than the expected `time("13:00:01")`. We also noticed that `HSub PlainDateTime Millisecond.Offset` is similarly affected.

- [#12885](https://github.com/leanprover/lean4/pull/12885)
  shifts some material in `Init` to make sure that the `ToString` instances of basic types don't rely on `String.Internal.append`.

- [#12857](https://github.com/leanprover/lean4/pull/12857)
  removes the use of `native_decide` in the HTTP library and adds proofs to remove the `panic!`.

- [#12852](https://github.com/leanprover/lean4/pull/12852)
  implements an iterator for `PersistentHashMap`.

- [#12844](https://github.com/leanprover/lean4/pull/12844)
  provides the iterator combinator `append` that permits the concatenation of two iterators.

- [#12481](https://github.com/leanprover/lean4/pull/12481)
  provides lemmas about `toArray` and `keysArray` on tree maps and tree sets that are analogous to the existing `toList` and `keys` lemmas.

- [#12385](https://github.com/leanprover/lean4/pull/12385)
  implements a merge sort algorithm on arrays. It has been measured to be about twice as fast as `List.mergeSort` for large arrays with random elements, but for small or almost sorted ones, the list implementation is faster. Compared to `Array.qsort`, it is stable and has O(n log n) worst-case cost. Note: There is still a lot of potential for optimization. The current implementation allocates O(n log n) arrays, one per recursive call.

- [#12821](https://github.com/leanprover/lean4/pull/12821)
  removes the `@[grind →]` attribute from `List.getElem_of_getElem?` and `Vector.getElem_of_getElem?`. These were identified as problematic in Mathlib by https://github.com/leanprover/lean4/issues/12805.

- [#12807](https://github.com/leanprover/lean4/pull/12807)
  makes the lemmas about `String.find?` and `String.contains` that were added recently into public declarations.

- [#12757](https://github.com/leanprover/lean4/pull/12757)
  marks `Id.run` as `[implicit_reducible]` to ensure that `Id.instMonadLiftTOfPure` and `instMonadLiftT Id` are definitionally equal when using `.implicitReducible` transparency setting.

- [#12793](https://github.com/leanprover/lean4/pull/12793)
  takes a more principled approach in deriving `String` pattern lemmas by reducing to simpler cases similar to how the instances are defined.

- [#12126](https://github.com/leanprover/lean4/pull/12126)
  introduces the core HTTP data types: `Request`, `Response`, `Status`, `Version`, and `Method`. Currently, URIs are represented as `String` and headers as `HashMap String (Array String)`. These are placeholders, future PRs will replace them with strict implementations.

- [#12783](https://github.com/leanprover/lean4/pull/12783)
  adds user-facing API lemmas for `s.contains t`, where `s` and `t` are both a string or a slice.

- [#12760](https://github.com/leanprover/lean4/pull/12760)
  adds general projection lemmas for `ExceptConds` conjunction:

  - `ExceptConds.and_elim_left`: `(x ∧ₑ y) ⊢ₑ x`
  - `ExceptConds.and_elim_right`: `(x ∧ₑ y) ⊢ₑ y`

- [#12779](https://github.com/leanprover/lean4/pull/12779)
  provides a `ForwardPatternModel` for string patterns and deduces theorems and lawfulness instances from the corresponding results for slice patterns.

- [#12777](https://github.com/leanprover/lean4/pull/12777)
  adds lemmas about `String.find?` and `String.contains`.

- [#12771](https://github.com/leanprover/lean4/pull/12771)
  generalizes `String.Slice.Pos.cast`, which turns an `s.Pos` into a `t.Pos`, to no longer require `s = t`, but merely `s.copy = t.copy`.

- [#12433](https://github.com/leanprover/lean4/pull/12433)
  adds a bitblasting circuit for `BitVec.cpop` with a divide-and-conquer for a parallel-prefix-sum.

- [#12435](https://github.com/leanprover/lean4/pull/12435)
  provides injectivity lemmas for `List.getElem`, `List.getElem?`, `List.getElem!` and `List.getD` as well as for `Option`. Note: This introduces a breaking change, changing the signature of `Option.getElem?_inj`.

- [#12725](https://github.com/leanprover/lean4/pull/12725)
  shows that lawful searchers split the empty string to `[""]`.

- [#12723](https://github.com/leanprover/lean4/pull/12723)
  relates `String.split` to `List.splitOn` and `List.splitOnP`, provided that we are splitting by a character or character predicate.

- [#12710](https://github.com/leanprover/lean4/pull/12710)
  deprecated the handful of names in core involving the component `cons₂` in favor of `cons_cons`.

- [#12709](https://github.com/leanprover/lean4/pull/12709)
  adds various `String` lemmas that will be useful for deriving high-level theorems about `String.split`.

- [#12708](https://github.com/leanprover/lean4/pull/12708)
  changes the order of implicit parameters `α` and `ps` such that `α` consistently comes before `ps` in `PostCond.noThrow`, `PostCond.mayThrow`, `PostCond.entails`, `PostCond.and`, `PostCond.imp` and theorems.

- [#12707](https://github.com/leanprover/lean4/pull/12707)
  adds lemmas about `String.intercalate` and `String.Slice.intercalate`.

- [#12706](https://github.com/leanprover/lean4/pull/12706)
  adds a dsimproc which evaluates `String.singleton ' '` to `" "`.

- [#12697](https://github.com/leanprover/lean4/pull/12697)
  adds two new unfolding theorems to Std.Do: `PostCond.entails.mk` and `Triple.of_entails_wp`.

- [#12702](https://github.com/leanprover/lean4/pull/12702)
  upstreams `List.splitOn` and `List.splitOnP` from Batteries/mathlib.

- [#12405](https://github.com/leanprover/lean4/pull/12405)
  adds several useful lemmas for `List`, `Array` and `Vector` whenever they were missing, improving API coverage and consistency among these types.
  - `size_singleton`/`sum_singleton`/`sum_push`
  - `foldlM_toArray`/`foldlM_toList`/`foldl_toArray`/`foldl_toList`/`foldrM_toArray`/`foldrM_toList`/`foldr_toList`
  - `toArray_toList`
  - `foldl_eq_apply_foldr`/`foldr_eq_apply_foldl`, `foldr_eq_foldl`: relates `foldl` and `foldr` for associative operations with identity
  - `sum_eq_foldl`: relates sum to `foldl` for associative operations with identity
  - `Perm.pairwise_iff`/`Perm.pairwise`: pairwise properties are preserved under permutations of arrays

- [#12430](https://github.com/leanprover/lean4/pull/12430)
  provides `WellFounded.partialExtrinsicFix`, which makes it possible to implement and verify partially terminating functions, safely building on top of the seemingly less general `extrinsicFix` (which is now called `totalExtrinsicFix`). A proof of termination is only necessary in order to formally verify the behavior of `partialExtrinsicFix`.

- [#12685](https://github.com/leanprover/lean4/pull/12685)
  adds some missing material about transferring positions across the subslicing operations `slice`, `sliceFrom`, `sliceTo`.

- [#12678](https://github.com/leanprover/lean4/pull/12678)
  marks `List.flatten`, `List.flatMap`, `List.intercalate` as noncomputable to ensure that their `csimp` variants are used everywhere.

- [#12668](https://github.com/leanprover/lean4/pull/12668)
  adds lemmas about string positions and patterns that will be useful for providing high-level API lemmas for `String.split` and friends.

```

# Tactics

```markdown

- [#13177](https://github.com/leanprover/lean4/pull/13177)
  adds `@[expose]` to `Lean.Grind.abstractFn` and
  `Lean.Grind.simpMatchDiscrsOnly` so that the kernel can unfold them when
  type-checking `grind`-produced proofs inside `module` blocks. Other
  similar gadgets (`nestedDecidable`, `PreMatchCond`, `alreadyNorm`) were
  already exposed; these two were simply missed.

- [#13166](https://github.com/leanprover/lean4/pull/13166)
  replaces the `grind` canonicalizer with a new type-directed normalizer (`Sym.canon`) that goes inside binders and applies targeted reductions in type positions, eliminating the O(n^2) `isDefEq`-based approach.

- [#13149](https://github.com/leanprover/lean4/pull/13149)
  simplifies the `grind` canonicalizer by removing dead state and unnecessary
  complexity, and fixes two bugs discovered during the cleanup.

- [#13080](https://github.com/leanprover/lean4/pull/13080)
  adds `SymExtension`, a typed extensible state mechanism for `SymM`,
  following the same pattern as `Grind.SolverExtension`. Extensions are
  registered at initialization time via `registerSymExtension` and provide
  typed `getState`/`modifyState` accessors. Extension state persists across
  `simp` invocations within a `sym =>` block and is re-initialized on each
  `SymM.run`.

- [#13048](https://github.com/leanprover/lean4/pull/13048)
  adds two new `sym_simproc` DSL primitives and helper grind-mode
  tactics.

- [#13046](https://github.com/leanprover/lean4/pull/13046)
  prevents `Sym.simp` from looping on permutation theorems like
  `∀ x y, x + y = y + x`.

- [#13042](https://github.com/leanprover/lean4/pull/13042)
  extends the `simp` tactic in `sym =>` mode to support local
  hypotheses in the extra theorem list.

- [#13041](https://github.com/leanprover/lean4/pull/13041)
  extends `mkTheoremFromDecl` and `mkTheoremFromExpr` to handle
  theorems whose conclusion is not an equality, enabling `Sym.simp` to use
  a broader class of lemmas as rewrite rules.

- [#13040](https://github.com/leanprover/lean4/pull/13040)
  adds validation to the `register_sym_simp` command:

  - Reject duplicate variant names
  - Validate `pre`/`post` syntax by elaborating them via `elabSymSimproc`
    in a minimal `GrindTacticM` context, catching unknown theorem names
    and unknown theorem set references at registration time

- [#13039](https://github.com/leanprover/lean4/pull/13039)
  adds the `simp` tactic to the `sym =>` interactive mode, completing
  the `Sym.simp` interactive infrastructure.

- [#13034](https://github.com/leanprover/lean4/pull/13034)
  adds the `register_sym_simp` command for declaring named `Sym.simp`
  variants with `pre`/`post` simproc chains and optional config overrides.

- [#13033](https://github.com/leanprover/lean4/pull/13033)
  adds `r == e` guards to the `norm_eq_var` and `norm_eq_var_const` branches of `Int.Linear.simpEq?`. Without these guards, `simpEq?` returns a non-trivial proof for already-normalized equations like `x = -1`, causing `exists_prop_congr` to fire repeatedly and build an infinitely growing term.

- [#13032](https://github.com/leanprover/lean4/pull/13032)
  fixes #12842 where `grind` exhausts memory on goals involving high-degree polynomials such as `(x + y)^2 = x^128 + y^2` over `Fin 2`.

- [#13031](https://github.com/leanprover/lean4/pull/13031)
  adds the built-in elaborators for the `sym_simproc` and `sym_discharger` DSL syntax categories introduced in #13026.

- [#13027](https://github.com/leanprover/lean4/pull/13027)
  fixes a nondeterministic crash in `grind` caused by a `BEq`/`Hashable` invariant
  violation in the congruence table. `congrHash` uses each expression's own `funCC` flag to
  compute its hash (one-level decomposition for `funCC = true`, full recursive decomposition
  for `funCC = false`), but `isCongruent` only checked the stored expression's flag. When two
  expressions with mismatched `funCC` flags accidentally hash-collided (via pointer-based
  `ptrAddrUnsafe` hashing), `isCongruent` could declare them congruent despite different
  argument counts, leading to an assertion failure in `mkCongrProof`.

- [#13026](https://github.com/leanprover/lean4/pull/13026)
  adds the infrastructure for simproc and discharger DSLs used to specify `pre`/`post` simproc chains and conditional rewrite dischargers in `Sym.simp` variants.

- [#13024](https://github.com/leanprover/lean4/pull/13024)
  fixes an issue where `grind` could prove each conjunct individually but failed on the conjunction. The root cause: `solverAction`'s `.propagated` path calls `processNewFacts` which drains the `newFacts` queue, but the resulting propagation cascade (congruence closure, or-propagation, `propagateForallPropDown`) can call `addNewRawFact`, enqueuing to the separate `newRawFacts` queue. These raw facts were never drained.

- [#13018](https://github.com/leanprover/lean4/pull/13018)
  adds named theorem sets for `Sym.simp` with associated attributes, following the same pattern as `Meta.simp`'s `register_simp_attr`.

- [#12996](https://github.com/leanprover/lean4/pull/12996)
  adds per-result `contextDependent` tracking to `Sym.Simp.Result` and splits the simplifier cache into persistent (context-independent) and transient (context-dependent, cleared on binder entry). This replaces the coarse `wellBehavedMethods` flag.

- [#12970](https://github.com/leanprover/lean4/pull/12970)
  adds a `sym =>` tactic that enters an interactive symbolic simulation
  mode built on `grind`. Unlike `grind =>`, it does not eagerly introduce
  hypotheses or apply by-contradiction, giving users explicit control over
  `intro`, `apply`, and `internalize` steps.

- [#12944](https://github.com/leanprover/lean4/pull/12944)
  changes the interaction between `@[cbv_opaque]` and `@[cbv_eval]`
  attributes in the `cbv` tactic. Previously, `@[cbv_opaque]` completely blocked
  all reduction including `@[cbv_eval]` rewrite rules. Now, `@[cbv_eval]` rules
  can fire on `@[cbv_opaque]` constants, allowing users to provide custom rewrite
  rules without exposing the full definition. Equation theorems, unfold theorems,
  and kernel reduction remain suppressed for opaque constants.

- [#12923](https://github.com/leanprover/lean4/pull/12923)
  fixes a bug where `max u v` and `max v u` fail to match in SymM's pattern matching. Both `processLevel` (Phase 1) and `isLevelDefEqS` (Phase 2) treated `max` positionally, so `max u v ≠ max v u` structurally even though they are semantically equal.

- [#12920](https://github.com/leanprover/lean4/pull/12920)
  adds eta reduction to the sym discrimination tree lookup functions (`getMatch`, `getMatchWithExtra`, `getMatchLoop`). Without this, expressions like `StateM Nat` that unfold to eta-expanded forms `(fun α => StateT Nat Id α)` fail to match discrimination tree entries for the eta-reduced form `(StateT Nat Id)`.

- [#12887](https://github.com/leanprover/lean4/pull/12887)
  optimizes the `String.reduceEq`, `String.reduceNe`, and `Sym.Simp` string equality simprocs to produce kernel-efficient proofs. Previously, these used `String.decEq` which forced the kernel to run UTF-8 encoding/decoding and byte array comparison, causing 86+ kernel unfoldings on short strings.

- [#12908](https://github.com/leanprover/lean4/pull/12908)
  makes `@[cbv_opaque]` unconditionally block all evaluation of a constant
  by `cbv`, including `@[cbv_eval]` rewrite rules. Previously, `@[cbv_eval]` could
  bypass `@[cbv_opaque]`, and for bare constants (not applications), `isOpaqueConst`
  could fall through to `handleConst` which would unfold the definition body.

- [#12888](https://github.com/leanprover/lean4/pull/12888)
  adds `String`-specific simprocs to `cbv` tactic.

- [#12882](https://github.com/leanprover/lean4/pull/12882)
  adds an `@[mvcgen_witness_type]` tag attribute, analogous to `@[mvcgen_invariant_type]`, that allows users to mark types as witness types. Goals whose type is an application of a tagged type are classified as witnesses rather than verification conditions, and appear in a new `witnesses` section in the `mvcgen` tactic syntax (before `invariants`).

- [#12875](https://github.com/leanprover/lean4/pull/12875)
  adds `cbv` simprocs for getting elements out of arrays.

- [#12597](https://github.com/leanprover/lean4/pull/12597)
  adds a `cbv_simproc` system for the `cbv` tactic, mirroring simp's `simproc` infrastructure but tailored to cbv's three-phase pipeline (`↓` pre, `cbv_eval` eval, `↑` post). User-defined simplification procedures are indexed by discrimination tree patterns and dispatched during cbv normalization.

- [#12851](https://github.com/leanprover/lean4/pull/12851)
  add support for erasing `@[cbv_eval]` annotations using `attribute [-cbv_eval]`, mirroring the existing `@[-simp]` mechanism for simp lemmas.

- [#12805](https://github.com/leanprover/lean4/pull/12805)
  adds a `set_option grind.unusedLemmaThreshold` that, when set to N > 0
  and `grind` succeeds, reports E-matching lemmas that were activated at least N
  times but do not appear in the final proof term. This helps identify `@[grind]`
  annotations that fire frequently without contributing to proofs.

- [#12563](https://github.com/leanprover/lean4/pull/12563)
  makes the `omit`, `unusedSectionVars` and `loopingSimpArgs` linters respect the `linter.all` option:
  when `linter.all` is set to false (and the respective linter option is unset), the linter should not report errors.

- [#12816](https://github.com/leanprover/lean4/pull/12816)
  solves three distinct issues with the handling of `ite`/`dite`,`decide`.

- [#12788](https://github.com/leanprover/lean4/pull/12788)
  adds a `set_option cbv.maxSteps N` option that controls the maximum
  number of simplification steps the `cbv` tactic performs. Previously the limit
  was hardcoded to the `Sym.Simp.Config` default of 100,000 with no way for
  users to override it. The option is threaded through `cbvCore`, `cbvEntry`,
  `cbvGoal`, and `cbvDecideGoal`.

- [#12782](https://github.com/leanprover/lean4/pull/12782)
  adds high priority to instances for `OfSemiring.Q` in the grind ring envelope. When Mathlib is imported, instance synthesis for types like `OfSemiring.Q Nat` becomes very expensive because the solver explores many irrelevant paths before finding the correct instances. By marking these instances as high priority and adding shortcut instances for basic operations (`Add`, `Sub`, `Mul`, `Neg`, `OfNat`, `NatCast`, `IntCast`, `HPow`), instance synthesis resolves quickly.

- [#12773](https://github.com/leanprover/lean4/pull/12773)
  adds `at` location syntax to the `cbv` tactic, matching the interface of `simp at`. Previously `cbv` could only reduce the goal target; now it supports `cbv at h`, `cbv at h |-`, and `cbv at *`.

- [#12766](https://github.com/leanprover/lean4/pull/12766)
  adds a dedicated cbv simproc for `Decidable.decide` that directly matches on `isTrue`/`isFalse` instances, producing simpler proof terms and avoiding unnecessary unfolding through `Decidable.rec`.

- [#12677](https://github.com/leanprover/lean4/pull/12677)
  changes the  approach in `simpIteCbv` and `simpDIteCbv`, by replacing call to `Decidable.decide`
  with reducing and direct pattern matching on the `Decidable` instance for `isTrue`/`isFalse`. This produces simpler proof terms.

- [#12763](https://github.com/leanprover/lean4/pull/12763)
  adds pre-pass simprocs `simpOr` and `simpAnd` to the `cbv` tactic that evaluate only the left argument of `Or`/`And` first, short-circuiting when the result is determined without evaluating the right side. Previously, `cbv` processed `Or`/`And` via congruence, which always evaluated both arguments. For expressions like `decide (m < n ∨ expensive)`, when `m < n` is true, the expensive right side is now skipped entirely.

- [#12607](https://github.com/leanprover/lean4/pull/12607)
  fixes an issue where `withLocation` wasn't saving the info context, which meant that tactics that use `at *` location syntax and do term elaboration would save infotrees but revert the metacontext, leading to Infoview messages like "Error updating: Error fetching goals: Rpc error: InternalError: unknown metavariable" if the tactic failed at some locations but succeeded at others.

```

# Compiler

```markdown

- [#13152](https://github.com/leanprover/lean4/pull/13152)
  informs the RC optimizer that tagged values can also be considered as "borrowed" in the sense that we do not need to consider them as owned values for the borrow analysis (they do of course not have an allocation they actually borrow from).

- [#13136](https://github.com/leanprover/lean4/pull/13136)
  introduces coalescing of RC operations to the RC optimizer. Whenever we perform multiple `inc`s for a single value within one basic block it is legal to instead perform all of these `inc`s at once at the first `inc` side. This is the case because the value will stay alive until at least the last `inc` and was thus never observable with `RC=1`. Hence, this change of `inc` location never destroys reuse opportunities.

- [#13147](https://github.com/leanprover/lean4/pull/13147)
  fixes theoretical leaks in the handling of `Array.get!Internal` in the code generator.
  Currently, the code generator assumes that the value returned by `get!Internal` is derived from the
  `Array` argument. However, this does not generally hold up as we might also return the `Inhabited`
  value in case of an out of bounds access (recall that we continue execution after panics by
  default). This means that we sometimes convert an `Array.get!Internal` to
  `Array.get!InternalBorrowed` when we are not allowed to do so because in the panic case the
  `Inhabited` instance can be returned and if it is an owned value it is going to leak.

- [#13138](https://github.com/leanprover/lean4/pull/13138)
  introduces the `weak_specialize` attribute. Unlike the `nospecialize` attribute it does not
  block specialization for parameters marked with this type completely. Instead, `weak_specialize`
  parameters are only specialized for if another parameter provokes specialization. If no such
  parameter exists, they are treated like `nospecialize`.

- [#13118](https://github.com/leanprover/lean4/pull/13118)
  fixes an incompatibility of `--load-dynlib` with the module system.

- [#13116](https://github.com/leanprover/lean4/pull/13116)
  ensures that reads from constants count as borrows in the eyes of the borrow inference analysis. This reduces RC pressure in the presence of constant reads.

- [#13094](https://github.com/leanprover/lean4/pull/13094)
  marks the `Inhabited` arguments of all functions in core marked as `extern` as borrowed
  (panicking array accessors and `panic!` itself). This in turn causes a transitive effect throughout
  the codebase and promotes most, if not all, `Inhabited` arguments to functions to borrowed.

- [#13097](https://github.com/leanprover/lean4/pull/13097)
  makes the compiler traces contain more information about the kind of `inc`/`dec` that are
  being conducted (`persistent`, `checked` etc.)

- [#13066](https://github.com/leanprover/lean4/pull/13066)
  changes the behavior of forward and backward projection propagation in the context of user defined borrows. The reason to have them be "forced" override (i.e. override user annotations as well) was that a user annotated borrowed value can potentially flow into a reset-reuse transitively through a projection and must thus have accurate reference count. The reasons that this is no longer necessary are:
  1. Forward never had to be forced anyways, it can only affect the `z` in `let z := oproj x i` which can't be annotated by a user
  2. Backward is no longer necessary as the forward propagator for user annotations prevents the reset-reuse insertion from working with values that have user defined borrow annotations entirely.

- [#13064](https://github.com/leanprover/lean4/pull/13064)
  informs the borrow inference that if an `Array` is borrowed and we index into it, the value we obtain is effectively a borrowed value as well. This helps improve the ABI of operations that recurse on linked structures containing arrays such as tries or persistent hash maps.

- [#12942](https://github.com/leanprover/lean4/pull/12942)
  marks the context argument of `ReaderT` as borrowed, causing a wide spread of useful borrow annotations throughout the entire meta stack which reduces RC pressure. This introduces a crucial new behavior: When modifying `ReaderT` context, e.g. through `withReader` this will almost always cause an allocation. Given that the `ReaderT` context is frequently used in a non-linear fashion anyways we think this is an acceptable behavior.

- [#13052](https://github.com/leanprover/lean4/pull/13052)
  fixes a bug in the borrow inference in connection with `export` annotations.

- [#13017](https://github.com/leanprover/lean4/pull/13017)
  ensures that when a declaration is marked with `@[export]`, the compiler throws an error if
  any of its arguments are marked as borrowed.

- [#12971](https://github.com/leanprover/lean4/pull/12971)
  increases Lean's default stack size, including for the main thread of Lean executables, to 1GB.

- [#12830](https://github.com/leanprover/lean4/pull/12830)
  enables support for respecting user provided borrow annotations. This allows user to mark arguments of their definitions or local functions with `(x : @&Ty)` and have the borrow inference try its best to preserve this annotation, thus potentially reducing RC pressure. Note that in some cases this might not be possible. For example, the compiler prioritizes preserving tail calls over preserving borrow annotations. A precise reasoning of why the compiler chose to make its inference decisions can be obtained with `trace.Compiler.inferBorrow`.

- [#12952](https://github.com/leanprover/lean4/pull/12952)
  ensures that when a function is marked `export` its borrow annotations (if present) are always ignored.

- [#12930](https://github.com/leanprover/lean4/pull/12930)
  places `set_option compiler.ignoreBorrowAnnotation true in` on to all `export`/`extern`
  pairs. This is necessary because `export` forces all arguments to be passed as owned while `extern`
  respects borrow annotations. The current approach to the `export`/`extern` trick was always broken
  but never surfaced. However, with upcoming changes many `export`/`extern` pairs are going to be
  affected by borrow annotations and would've broken without this.

- [#12886](https://github.com/leanprover/lean4/pull/12886)
  adds support for ignoring user defined borrow annotations. This can be useful when defining
  `extern`/`export` pairs as the `extern` might be infected by borrow annotations while in `export`
  they are already ignored.

- [#12781](https://github.com/leanprover/lean4/pull/12781)
  ports the C emission pass from IR to LCNF, marking the last step of the IR/LCNF conversion and thus enabling end-to-end code generation through the new compilation infrastructure.

- [#12850](https://github.com/leanprover/lean4/pull/12850)
  optimizes the handling of `match_same_ctor.het` to make it emit nice match trees as opposed to unoptimized CPS style code.

- [#12539](https://github.com/leanprover/lean4/pull/12539)
  replaces three independent name demangling implementations (Lean, C++, Python) with a single source of truth in `Lean.Compiler.NameDemangling`. The new module handles the full pipeline: prefix parsing (`l_`, `lp_`, `_init_`, `initialize_`, `lean_apply_N`, `_lean_main`), postprocessing (suffix flags, private name stripping, hygienic suffix stripping, specialization contexts), backtrace line parsing, and C exports via `@[export]`.

- [#12810](https://github.com/leanprover/lean4/pull/12810)
  adds tracing to the borrow inference to explain to the user why it got to its conclusions.

- [#12796](https://github.com/leanprover/lean4/pull/12796)
  fixes a deadlock when `uv_tcp_accept` is under contention from multiple threads.

- [#12795](https://github.com/leanprover/lean4/pull/12795)
  fixes a memory leak that gets triggered on the error path of `lean_uv_dns_get_name`

- [#12790](https://github.com/leanprover/lean4/pull/12790)
  makes the compiler removes arguments to join points that are void, avoiding a bunch of dead
  stores in the bytecode and the initial C (though LLVM was surely able to optimize these away further
  down the line already).

- [#12759](https://github.com/leanprover/lean4/pull/12759)
  replaces the `isImplicitReducible` check with `Meta.isInstance` in the `shouldInline` function within `inlineCandidate?`.

- [#12724](https://github.com/leanprover/lean4/pull/12724)
  implements support for extracting simple ground array literals into statically initialized data.

- [#12727](https://github.com/leanprover/lean4/pull/12727)
  implements simple ground literal extraction for boxed scalar values.

- [#12715](https://github.com/leanprover/lean4/pull/12715)
  ensures the compiler extracts `Array`/`ByteArray`/`FloatArray` literals as one big closed term to avoid quadratic overhead at closed term initialization time.

- [#12705](https://github.com/leanprover/lean4/pull/12705)
  ports the simple ground expression extraction pass from IR to LCNF.

- [#12665](https://github.com/leanprover/lean4/pull/12665)
  ports the expand reset/reuse pass from IR to LCNF. In addition it prevents exponential code generation unlike the old one. This results in a ~15% decrease in binary size and slight speedups across the board.

- [#12687](https://github.com/leanprover/lean4/pull/12687)
  implements the LCNF instructions required for the expand reset reuse pass.

- [#12663](https://github.com/leanprover/lean4/pull/12663)
  avoids false-positive error messages on specialization restrictions under the module system when the declaration is explicitly marked as not specializable. It could also provide some minor public size and rebuild savings.

```

# Pretty Printing

````markdown

- [#10384](https://github.com/leanprover/lean4/pull/10384)
  makes notations such as `∨`, `∧`, `≤`, and `≥` pretty print using ASCII versions when `pp.unicode` is false.

- [#12745](https://github.com/leanprover/lean4/pull/12745)
  fixes `pp.fvars.anonymous` to display loose free variables as `_fvar._` instead of `_` when the option is set to `false`. This was the intended behavior in https://github.com/leanprover/lean4/pull/12688 but the fix was committed locally and not pushed before that PR was merged.

- [#12688](https://github.com/leanprover/lean4/pull/12688)
  adds a `pp.fvars.anonymous` option (default `true`) that controls the display of loose free variables (fvars not in the local context).

- [#12654](https://github.com/leanprover/lean4/pull/12654)
  fixes two aspects of pretty printing of private names.
  1. Name unresolution. Now private names are not special cased: the private prefix is stripped off and the `_root_` prefix is added, then it tries resolving all suffixes of the result. This is sufficient to handle imported private names in the new module system. (Additionally, unresolution takes macro scopes into account now.)
  2. Delaboration. Inaccessible private names use a deterministic algorithm to convert private prefixes into macro scopes. The effect is that the same private name appearing in multiple times in the same delaborated expression will now have the same `✝` suffix each time. It used to use fresh macro scopes per occurrence.

- [#12606](https://github.com/leanprover/lean4/pull/12606)
  adds the pretty printer option `pp.mdata`, which causes the pretty printer to annotate terms with any metadata that is present. For example,
  ```lean
  set_option pp.mdata true
  /-- info: [mdata noindex:true] 2 : Nat -/
  #guard_msgs in #check no_index 2
  ```

````

# Documentation

```markdown

- [#13115](https://github.com/leanprover/lean4/pull/13115)
  updates the `inferInstanceAs` docstring to reflect current behavior: it requires an
  expected type from context and should not be used as a simple `inferInstance` synonym. The
  old example (`#check inferInstanceAs (Inhabited Nat)`) no longer works, so it's replaced
  with one demonstrating the intended transport use case.

- [#13065](https://github.com/leanprover/lean4/pull/13065)
  rewrites the docstring on `Lean.ReducibilityHints` to accurately describe the
  kernel's lazy delta reduction strategy: which side gets unfolded when comparing two
  definitions, how definitional height is computed, and how hints relate to the
  `@[reducible]`/`@[irreducible]` elaborator attributes.

- [#12959](https://github.com/leanprover/lean4/pull/12959)
  fixes a series of errors in docstrings.

```

# Server

```markdown

- [#12948](https://github.com/leanprover/lean4/pull/12948)
  moves `RequestCancellationToken` from `IO.Ref` to `IO.CancelToken`.

- [#12905](https://github.com/leanprover/lean4/pull/12905)
  adjusts the JSON encoding of RPC references from `{"p": "n"}` to `{"__rpcref": "n"}`. Existing clients will continue to work unchanged, but should eventually move to the new format by advertising the `rpcWireFormat` client capability.

```

# Lake

```markdown

- [#13164](https://github.com/leanprover/lean4/pull/13164)
  changes `lake cache get` to fetch artifact cloud storage URLs from Reservoir in a single bulk POST request rather than relying on per-artifact HTTP redirects. When downloading many artifacts, the redirect-based approach sends one request per artifact to the Reservoir web host (Netlify), which can be slow and risks hitting rate limits. The bulk endpoint returns all URLs at once, so curl only talks to the CDN after that.

- [#13151](https://github.com/leanprover/lean4/pull/13151)
  changes `Lake.proc` to always log process output as `info` if the process exits with a nonzero return code. This way it behaves the same as `captureProc` on errors.

- [#13144](https://github.com/leanprover/lean4/pull/13144)
  adds three new `lake cache` subcommands for staged cache uploads: `stage`, `unstage`, and `put-staged`. These are designed to function as parallels for the commands of the same name in Mathlib's `lake exe cache`.

- [#13141](https://github.com/leanprover/lean4/pull/13141)
  changes Lake's materialization process to run remove untracked files in tracked directories (via `git clean -xf`) when updating dependency repositories. This ensures stale leftovers in the source tree are removed.

- [#13110](https://github.com/leanprover/lean4/pull/13110)
  fixes a race condition in `Cache.saveArtifact` that caused intermittent "permission denied" errors when two library facets (e.g., `static` and `static.export`) produce artifacts with the same content hash and attempt to cache them concurrently.

- [#13028](https://github.com/leanprover/lean4/pull/13028)
  adds a check that rejects Lake configurations where multiple executables share the same root module name. Previously, Lake would silently compile the root module once and link it into all executables, producing identical binaries regardless of differing `srcDir` settings.

- [#13014](https://github.com/leanprover/lean4/pull/13014)
  makes errors in `lake cache get` / `lake cache put` artifact transfers more verbose, which helps with debugging. It also fixes an issue with error reporting when downloading artifacts on demand.

- [#12993](https://github.com/leanprover/lean4/pull/12993)
  fixes a bug with Lake where caching an `ltar` produced via `lake build -o` would fail if `restoreAllArtifacts` was also `true`.

- [#12974](https://github.com/leanprover/lean4/pull/12974)
  changes `lake cache get` and `lake cache put` to transfer artifacts in parallel (using `curl --parallel`) when uploading or eagerly downloading artifacts. Transfers are still recorded one-by-one in the output -- no progress meter yet.

- [#12957](https://github.com/leanprover/lean4/pull/12957)
  fixes a build failure on macOS introduced by #12540. macOS BSD `ar` does not support the `@file` response file syntax that #12540 enabled unconditionally. On macOS, when building core (i.e., `bootsrap := true`), `recBuildStatic` now uses `libtool -static -filelist`, which handles long argument lists natively.

- [#12954](https://github.com/leanprover/lean4/pull/12954)
  changes the Lake `CacheMap` data structure to track the platform-dependence of outputs. Platform-independent packages will no longer include platform-dependent mappings in the output files produced by `lake build -o`.

- [#12540](https://github.com/leanprover/lean4/pull/12540)
  extends Lake's use of response files (`@file`) from Windows-only to all platforms, avoiding `ARG_MAX` limits when invoking `clang`/`ar` with many object files.

- [#12935](https://github.com/leanprover/lean4/pull/12935)
  adds the `fixedToolchain` Lake package configuration option. Setting this to `true` informs Lake that the package is only expected to function on a single toolchain (like Mathlib). This causes Lake's toolchain update procedure to prioritize its toolchain and avoids the need to separate input-to-output mappings for the package by toolchain version in the Lake cache.

- [#12914](https://github.com/leanprover/lean4/pull/12914)
  adds packing and unpacking of module artifacts into `.ltar` archives using `leantar`.

- [#12927](https://github.com/leanprover/lean4/pull/12927)
  changes `lake cache get` to download artifacts by default. Artifacts can be downloaded on demand with the new `--mappings-only` option (`--download-arts` is now obsolete).

- [#12837](https://github.com/leanprover/lean4/pull/12837)
  changes the default behavior of the `restoreAllArtifacts` package configuration to mirror that of the workspace. If the workspace also has it unset, the default remains the same (`false`).

- [#12835](https://github.com/leanprover/lean4/pull/12835)
  changes Lake to only emit `.nobuild` traces (introduced in #12076) if the normal trace file already exists. This fixes an issue where a  `lake build --no-build` would create the build directory and thereby prevent a cloud release fetch in a future build.

- [#12799](https://github.com/leanprover/lean4/pull/12799)
  changes Lake to use the modification times of traces (where available) for artifact modification times.

- [#12634](https://github.com/leanprover/lean4/pull/12634)
  enables Lake to download artifacts from a remote cache service on demand as part of a `lake build`. It also refactors much of the cache API to be more type safe.

```

# Other

```markdown

- [#12865](https://github.com/leanprover/lean4/pull/12865)
  fixes a crash in release_checklist.py when a repository uses the
  `leanprover/lean4-nightly:` toolchain prefix (e.g. leansqlite). The
  `is_version_gte` function only checked for `leanprover/lean4:nightly-` but
  not `leanprover/lean4-nightly:`, causing a `ValueError: invalid literal for
  int() with base 10: 'nightly'` when trying to parse the version.

- [#12963](https://github.com/leanprover/lean4/pull/12963)
  fixes a panic in `lake shake` when applied to a header-only file without trailing newline

- [#12836](https://github.com/leanprover/lean4/pull/12836)
  adds a `lake-ci` label that enables the full Lake test suite in CI,
  avoiding the need to temporarily commit and revert changes to
  `tests/CMakeLists.txt`. The `lake-ci` label implies `release-ci` (check level
  3), so all release platforms are also tested.

- [#12822](https://github.com/leanprover/lean4/pull/12822)
  downloads a prebuilt release of `leantar` and bundles it with Lean as part of the core build.

- [#12700](https://github.com/leanprover/lean4/pull/12700)
  fixes a CMake scoping bug that made `-DLEAN_VERSION_*` overrides ineffective.

- [#12638](https://github.com/leanprover/lean4/pull/12638)
  switches four lightweight workflows from `pull_request` to
  `pull_request_target` to stop GitHub from requiring manual approval when the
  `mathlib-lean-pr-testing[bot]` app triggers label events (e.g. adding
  `builds-mathlib`). Since the bot never lands commits on master, it is
  perpetually treated as a "first-time contributor" and every `pull_request`
  event it triggers requires approval. `pull_request_target` events always run
  without approval because they execute trusted code from the base branch.

- [#12682](https://github.com/leanprover/lean4/pull/12682)
  extends `lake shake` with a flag for minimizing only a specific module

- [#12648](https://github.com/leanprover/lean4/pull/12648)
  adds the experimental `idbg e`, a new do-element (and term) syntax for live debugging between the language server and a running compiled Lean program.

```
