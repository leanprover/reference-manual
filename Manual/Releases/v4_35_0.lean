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

#doc (Manual) "Lean 4.35.0-rc2 (2026-09-16)" =>
%%%
tag := "release-v4.35.0"
file := "v4.35.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 206 changes landed.
In addition to the 76 feature additions
and 53 fixes listed below,
there were 18 refactoring changes,
7 documentation improvements,
21 performance improvements,
2 improvements to the test suite,
and 29 other changes.

# Language

````markdown

- [#15020](https://github.com/leanprover/lean4/pull/15020)
  removes the `Array Syntax` -> `SepArray sep` and `SepArray sep` -> `Array Syntax` coercions and adds a separator-`SourceInfo`-preserving `TSepArray ks sep` -> `SepArray sep` coercion instead. Fixes an issue where coercing from `TSepArray ks sep` to `SepArray sep` would lose the `SourceInfo` of the separators.

- [#15133](https://github.com/leanprover/lean4/pull/15133)
  moves InfoTree and SnapshotTree utilities from the server domain to the elab domain.

- [#15090](https://github.com/leanprover/lean4/pull/15090)
  adds erased state to `do` notation: `erased x := e`, `erased mut x := e`, and `erased x ← act` declare verification-only variables that loop `invariant` clauses and assertions can read while compiled code carries only a dummy in their place.

- [#15079](https://github.com/leanprover/lean4/pull/15079)
  makes `Array.modify` and `Array.modifyM` kernel-reducible across module boundaries.

- [#15078](https://github.com/leanprover/lean4/pull/15078)
  makes `Array.zipWith` and the corresponding `Vector.zipWith` operation kernel-reducible across module boundaries.

- [#14996](https://github.com/leanprover/lean4/pull/14996)
  lets `Array.map` and the delegating `Vector.map` reduce in the kernel across module boundaries.

- [#14989](https://github.com/leanprover/lean4/pull/14989)
  lets `Array.ofFn` and the delegating `Vector.ofFn` reduce in the kernel across module boundaries.

- [#14988](https://github.com/leanprover/lean4/pull/14988)
  lets the derived `Vector` `DecidableEq` instance reduce in the kernel across module boundaries.

- [#14270](https://github.com/leanprover/lean4/pull/14270)
  lets `decide` and `rfl` reduce nonempty `Array` equality in the kernel across module boundaries.

- [#15050](https://github.com/leanprover/lean4/pull/15050)
  adds and `--from-export file.ndjson` flag to `leanchecker`. This instructs it to load the provided ndjson export format file and run it through the kernel.

- [#15019](https://github.com/leanprover/lean4/pull/15019)
  removes the `withPosition` marker from the body of `macro` and `elab` declarations.

- [#14982](https://github.com/leanprover/lean4/pull/14982)
  introduces a new file `mimalloc.cpp` which contains our object allocation logic and includes the mimalloc implementation.

- [#14912](https://github.com/leanprover/lean4/pull/14912)
  adds an option to `TerminationHints` to disable warnings for redundant hints. This can be useful for generating declarations with termination hints using `addPreDefinitions`, avoiding warnings if these hints turn out to be redundant.

- [#13815](https://github.com/leanprover/lean4/pull/13815)
  fixes an issue where ambiguous syntax would have missing terminfo or missing context (such as the metavariable context), leading to errors in the infoview. Closes #8108.

- [#14960](https://github.com/leanprover/lean4/pull/14960)
  improves the way `#print` describes recursors. For example, `#print Nat.rec` now gives the following:
  ```
  recursor Nat.rec.{u} {motive : Nat → Sort u} (zero : motive Nat.zero) (succ : (n : Nat) → motive n → motive n.succ)
    (t : Nat) : motive t
  number of parameters: 0
  number of motives: 1 (position 1)
  number of minor premises: 2 (positions 2–3)
  number of indices: 0
  major premise position: 4
  rules:
    Nat.rec zero succ Nat.zero
      ==> zero
    Nat.rec zero succ n.succ
      ==> succ n (Nat.rec zero succ n)
  ```

- [#14940](https://github.com/leanprover/lean4/pull/14940)
  changes the behaviour of `deprecated_syntax` warnings for things that were generated via macro expansion. If a piece of syntax is a result of macro, but comes with `.original` source info, we focus the warning on that piece of syntax.

- [#14937](https://github.com/leanprover/lean4/pull/14937)
  redesigns the `rwa` tactic for consistency and user-friendliness.

- [#14554](https://github.com/leanprover/lean4/pull/14554)
  fixes #14540 by separating the type-theoretic and runtime implementations of `Fin.foldl`.

- [#14925](https://github.com/leanprover/lean4/pull/14925)
  makes `casesOn` and `recOn` of a proposition apply the minor premise to the projections of the major premise, instead of going through the recursor. A recursor only reduces once its major premise is a constructor application, which a proof may never become, so `And.casesOn` and friends no longer require the proof itself to reduce.

- [#14855](https://github.com/leanprover/lean4/pull/14855)
  adds strong (co)induction proof principles for lattice-theoretic (co)inductive predicates. For predicates defined by `coinductive_fixpoint`, the generated `strong_coinduct` principle strengthens `coinduct`: in the hypothesis, occurrences of the candidate predicate are joined by disjunction with the coinductive predicate itself, so a proof by coinduction may conclude as soon as it re-enters the predicate. Dually, `inductive_fixpoint` definitions receive a `strong_induct` principle whose induction hypothesis additionally provides membership in the predicate itself, and mutual (including mixed) definitions receive `strong_mutual_induct` with the connective chosen per component. The conclusions of the generated principles are now also beta-reduced, e.g. `star_ind tr q₁ q₂ → pred q₁` instead of `(fun q₁ => star_ind tr q₁ q₂) q₁ → pred q₁`.

- [#14909](https://github.com/leanprover/lean4/pull/14909)
  fixes elaboration of sort-polymorphic inductive types such as `inductive T : Sort u | a | b`, which previously failed with `` Unknown constant `T.ctorIdx` ``. It also fixes the same failure for `set_option genCtorIdx false`.

- [#14350](https://github.com/leanprover/lean4/pull/14350)
  enforces that elements of singleton notation need to indent e.g. nested application arguments, as otherwise the overlap with structure notation is simply too confusing for both humans and the upcoming formatter (would require blocking on elaboration).

- [#14861](https://github.com/leanprover/lean4/pull/14861)
  adds a `monotonicity_by` clause to `coinductive` and `inductive` predicate declarations, allowing users to prove monotonicity of the underlying fixpoint functor with an explicit tactic block when the automatic `monotonicity` proof search does not succeed. The clause enters tactic mode directly, analogously to `decreasing_by`, and may be attached to individual members of mutual cliques, including mixed `inductive`/`coinductive` ones:

  ```lean
  mutual
    coinductive tick : Prop where
      | mk : ¬tock → tick
    monotonicity_by repeat monotonicity

    inductive tock : Prop where
      | mk : ¬tick → tock
  end
  ```

- [#14899](https://github.com/leanprover/lean4/pull/14899)
  adds the built-in `recall` and `recall?` commands for checked expository restatements without requiring any imports.

- [#14834](https://github.com/leanprover/lean4/pull/14834)
  adds terminfo on `structure`/`class` fields so that "go to definition" on dependent usages of a field goes to the field's definition. This also helps with finding uses of a field in a `structure` definition. The PR additionally fixes a bug where terminfo and docstrings weren't applied to private fields of public structures when using the module system.

- [#14844](https://github.com/leanprover/lean4/pull/14844)
  ensures that `DiscrTree` operations collapse any trie nodes that end up empty.

- [#14860](https://github.com/leanprover/lean4/pull/14860)
  makes `invariant`, `decreasing`, and `assert` in a `do` block elaborate without `open Std.WP`, matching the `requires` and `ensures` clauses of a contract.

- [#14858](https://github.com/leanprover/lean4/pull/14858)
  removes the match-alternatives form of the `ensures` clause. Except for that, every clause of a contract (`requires`, `ensures`, `assert`, `invariant`, `decreasign`) elaborates like a `fun` telescope, including tuple patterns as in `ensures (lo, hi) => lo ≤ hi`.

- [#14854](https://github.com/leanprover/lean4/pull/14854)
  makes the `constructor` tactic emit a warning if multiple constructors match, and adds a `constructor!` tactic that has the previous behavior of silently applying the first matching constructor.

- [#14845](https://github.com/leanprover/lean4/pull/14845)
  gives the invariant of a `while` or `repeat` loop its own type, `def Std.WP.WhileInvariant α Pred := Bool → α → Pred`, a predicate over the loop's `exit` flag and the loop state. Previously, it reused `Std.WP.RepeatInvariant α α Pred = α ⊕ α → Pred`, a type which is awkward to use in practice.

- [#14590](https://github.com/leanprover/lean4/pull/14590)
  names the variables of a verification condition after the program, and makes those names accessible. Take

- [#14825](https://github.com/leanprover/lean4/pull/14825)
  adds a `given` clause to `def` contracts, written before `requires`. It binds the logical variables of the contract and scopes them over `requires` and `ensures`.

- [#14748](https://github.com/leanprover/lean4/pull/14748)
  adds the infrastructure to collect code quality metrics from linters. Entries logged during elaboration are saved in the `.olean` file for the module. Build tools can then collect these entries for each module without re-elaborating the code.

- [#14816](https://github.com/leanprover/lean4/pull/14816)
  makes the `@[deprecated]` attribute warn when the given replacement declaration is itself deprecated. When the replacement has a replacement of its own, the warning suggests deprecating directly in favor of that declaration instead. The check can be disabled with `set_option linter.deprecated.deprecatedTarget false`.

- [#14826](https://github.com/leanprover/lean4/pull/14826)
  reports the intrinsic verification syntax as experimental wherever it is used: the `requires` and `ensures` contract clauses of a `def`, the `assert` element, and the `invariant` and `decreasing` clauses of a loop each report at their keyword. Setting `experimental.intrinsic` to `true` acknowledges the experimental status and silences the reports.

- [#14821](https://github.com/leanprover/lean4/pull/14821)
  types the `fun` binders of a `do←` argument from the wrapper's signature, so field notation such as `bs.extract` resolves in the forwarded body. A binder with a type ascription is accepted as well, and a pattern binder gets a dedicated error message.

- [#14624](https://github.com/leanprover/lean4/pull/14624)
  fixes #9077 by ensuring that, during instance search, all metavariables for instance-implicit arguments are only assigned values of the expected type, up to instance transparency. The backward compatibility option `set_option backward.isDefEq.instanceTypes false` restores the old behavior. This is a breaking change that affects a few declarations in Mathlib. All of them have been fixed with a backward compatibility option, analyzed and extensively annotated with suggested actions. Note: This fix does *not* enforce the type of out-params at instance transparency; synthesis of `Class X`, where `X` is in an out-param position, can still yield a `Class Y` instance, as long as `X =?= Y` at a higher transparency. The latter phenomenon is of a somewhat different nature; it would be easy to enforce, but it would cause ~1000's of broken declarations in Mathlib, for unclear benefit.

- [#14705](https://github.com/leanprover/lean4/pull/14705)
  adds a clickable hint (and thus also a code action) to `deprecated` linter.

- [#14771](https://github.com/leanprover/lean4/pull/14771)
  fixes using `Environment.find?` and its variants on the result of `ofKernelEnv`.

- [#14583](https://github.com/leanprover/lean4/pull/14583)
  changes definitional equality and unification heuristics. Before `isDefEqApp`'s fallback throws a stuck exception, it tries the remaining few heuristics, and only if they don't succeed, the exception is thrown. This PR at the same time improves performance and robustness of unification and instance search. This change is a preparation for #14624. The backward compatibility flag `set_option backward.isDefEq.throwOnStuckAfterApp true` restores the old behavior.

- [#14703](https://github.com/leanprover/lean4/pull/14703)
  lets a `repeat` or `while` loop state the loop invariant and the termination measure that `vcgen` needs, so a loop inside a `def` with a contract verifies without manual proof steps:

  ```lean
  def countDown (n : Nat) : Id Nat
      ensures r => r = 0 := do
    let mut i := n
    while i > 0
        invariant exit => if exit then i = 0 else True
        decreasing i
      do
      i := i - 1
    return i
  ```

- [#14600](https://github.com/leanprover/lean4/pull/14600)
  adds a warning when deprecating a declaration in favor of another declaration that is not reducibly defeq.

````

# Library

````markdown

- [#13490](https://github.com/leanprover/lean4/pull/13490)
  adds `Nat.powMod b e m`, a modular exponentiation function provably equal to `b ^ e % m`, so large powers modulo a nonzero modulus can be evaluated without constructing the full power. It also makes exponentiation on `Fin n` use this operation.

- [#15024](https://github.com/leanprover/lean4/pull/15024)
  exposes the Fused Multiply-Add operation for `Float` and `Float32`along with a logical model.

- [#15144](https://github.com/leanprover/lean4/pull/15144)
  allows the RUP component of the LRAT checker to accept hint clauses that are themselves redundant.

- [#14796](https://github.com/leanprover/lean4/pull/14796)
  fixes reference count, mark_mt and error messages in libuv modules.

- [#15122](https://github.com/leanprover/lean4/pull/15122)
  adds the missing order instances on `UIntX` and `IntX`.

- [#15114](https://github.com/leanprover/lean4/pull/15114)
  exposes `Fin.addNat?`, so that it reduces across module boundaries. Ranges over `Fin n` are built from it via the `UpwardEnumerable (Fin n)` instance, so previously `cbv` and kernel reduction got stuck on `Fin.addNat?` applications in any file using the module system.

- [#15092](https://github.com/leanprover/lean4/pull/15092)
  adds a series of missing order instances on `Fin`, including `Min`, `Max`, `LawfulOrderOrd`, etc.

- [#15088](https://github.com/leanprover/lean4/pull/15088)
  provides `LinearOrderPackage Int`, which in turn provides the missing instance `LawfulOrderBEq Int`.

- [#15080](https://github.com/leanprover/lean4/pull/15080)
  deprecates `Lean.MVarId.liftReflToEq` and its helper theorem `Lean.Meta.Rfl.rel_of_eq_and_refl`. Neither is hooked up to a tactic in core, and downstream users should keep their own copies.

- [#15049](https://github.com/leanprover/lean4/pull/15049)
  introduces `markLinear` functions for hash maps, akin to `Array.markLinear`

- [#15071](https://github.com/leanprover/lean4/pull/15071)
  adds the missing instance `LawfulOrderBEq Nat`.

- [#15069](https://github.com/leanprover/lean4/pull/15069)
  introduces `Vector.markLinear` in a similar vein to `Array.markLinear`.

- [#15062](https://github.com/leanprover/lean4/pull/15062)
  registers `ext` and `ext_iff` theorems for `ULift`, `PULift`, `PLift`, and `MProd`, so the `ext` tactic applies to equalities of these structures.

- [#15043](https://github.com/leanprover/lean4/pull/15043)
  fixes `Std.Http.Server` stalls caused by idle connections retaining connection slots past the configured keep-alive timeout.

- [#15059](https://github.com/leanprover/lean4/pull/15059)
  annotates some `ForIn` and `ForIn'` instances with `default_instance`.

- [#15054](https://github.com/leanprover/lean4/pull/15054)
  adjusts the precedence of the range syntax so that `1 + 2...3` is `(1+2)...3` and `a...b |>.toList` is `(a...b).toList`.

- [#15018](https://github.com/leanprover/lean4/pull/15018)
  adds a missing `Decidable` instance for `bif` (`cond`) expressions, analogous to the existing instance for `if` (`ite`) expressions.

- [#14794](https://github.com/leanprover/lean4/pull/14794)
  adds `isEmpty_inter_comm` across the synchronized associative-container APIs, starting from associative lists and lifting the result through hash maps, tree maps, and sets. This makes it possible to prove symmetry of disjoint containers without unfolding membership.

- [#14995](https://github.com/leanprover/lean4/pull/14995)
  adds two lemmas exposing the recursion of `List.mergeSort` without reference to `MergeSort.Internal.splitInTwo`:

  - `mergeSort_append`: merging the sorted halves of any balanced split (`l₂.length ≤ l₁.length ≤ l₂.length + 1`) gives `(l₁ ++ l₂).mergeSort`. This is the primary statement: it has no index arithmetic, holds uniformly for every list length, and any specific unfolding (take/drop at the midpoint, cons-cons forms) is a two-line corollary.
  - `@[simp] mergeSort_pair`: `[a, b].mergeSort le = if le a b then [a, b] else [b, a]`, completing the `mergeSort_nil`/`mergeSort_singleton` progression. Unlike `mergeSort_append` it genuinely simplifies, so it is marked `@[simp]`.

- [#14890](https://github.com/leanprover/lean4/pull/14890)
  swaps the names of `Dyadic.not_lt` and `Dyadic.not_le`, so that `Dyadic.not_lt` reads `¬x < y ↔ y ≤ x` and `Dyadic.not_le` reads `¬x ≤ y ↔ y < x`. This is consistent with the corresponding lemmas for `Nat`, `Int`, `Rat`, and with `_root_.not_lt` and `_root_.not_le` in mathlib.

- [#8204](https://github.com/leanprover/lean4/pull/8204)
  adds the lemma `Int.tdiv_eq_zero_iff_natAbs_lt_or_eq_zero` which shows that T-division equals zero iff the absolute value of the numerator is less than the denominator, or the denominator equals zero:

  ```lean
  @[simp] theorem tdiv_eq_zero_iff_natAbs_lt_or_eq_zero {a : Int} {b : Int} :
      a.tdiv b = 0 ↔ (a.natAbs < b.natAbs ∨ b = 0):= by
  ```

- [#14545](https://github.com/leanprover/lean4/pull/14545)
  renders `Vector` values using `#v[...]` literal notation instead of exposing their underlying structure representation, making evaluated vectors more concise and readable. It replaces the derived `Repr` instance.

- [#14953](https://github.com/leanprover/lean4/pull/14953)
  removes `Lean.reduceBool`, `Lean.reduceNat`, `Lean.ofReduceBool`, `Lean.ofReduceNat` and `Lean.trustCompiler`, along with the kernel's support for reducing applications of the first two by running the compiler. They have been deprecated since 2026-02-01 in favour of asserting native evaluations with axioms, which is what `native_decide` and `bv_decide` already do through `Lean.Meta.nativeEqTrue`. Nothing in the toolchain used them any more.

- [#14842](https://github.com/leanprover/lean4/pull/14842)
  refactors the LRAT checker and massively extends the publicly available CNF API in doing so, in particular we:
  - formalize basic CNF properties like entailment, negation, unit clauses
  - formalize the RUP and RAT property
  - refactor the clause data structure to a more memory efficient one to support storing huge CNFs more efficiently
  - rewrite the LRAT checker from scratch on top of this new API. The new LRAT checker is both slightly faster and supports bounded variable addition.

- [#14916](https://github.com/leanprover/lean4/pull/14916)
  introduces `BitVec.ofNatClamp` as a generalization of the already existing `UIntX.ofNatClamped` family of functions.

- [#14915](https://github.com/leanprover/lean4/pull/14915)
  adds support for evaluating `Nat.log2` to the ground evaluators of `Sym.simp` and `Meta.simp`. Despite working by recursion, it still manages to evaluate efficiently by reduction because it only runs logarithmically many kernel-accelerated operations.

- [#14905](https://github.com/leanprover/lean4/pull/14905)
  makes `BitVec` e-matching annotations that convert "accidentally" from `getElem` to `getLsbD` less aggressive. This is done by instead encoding them into a dependent and + `getElem`.

- [#14903](https://github.com/leanprover/lean4/pull/14903)
  makes `List.Nodup.getElem_inj` only fire if we already see `Nodup xs` and indexing into `xs`.

- [#14895](https://github.com/leanprover/lean4/pull/14895)
  adds `ReflBEq` and `LawfulBEq` instances for `Sum` and exposes its derived `BEq`, so that `==` on sums reduces outside the module that defines it.

- [#14872](https://github.com/leanprover/lean4/pull/14872)
  removes the `⦃ P ⦄ c ⦃ v, Q ⦄` form of the Hoare triple notation. The `⦃ P ⦄ c ⦃ fun v => Q ⦄` expansion is easier to understand.

- [#14836](https://github.com/leanprover/lean4/pull/14836)
  replaces the exception postcondition types `EPost.Nil` and `EPost.Cons` with products. An exception postcondition stack is now `(ε₁ → Pred) × (ε₂ → Pred) × EStack⟨⟩`, so the `Prod` API applies to it. The base monads carry bare postconditions: `Except ε` uses `ε → Prop`, and `Option` uses `Unit → Prop`. The notation `EStack⟨A, B⟩` writes a stack type, and `estack⟨e₁, e₂⟩` writes a stack value. Both print back as written. `vcgen` splits `⊥` and `⊤` exception postconditions with the same cached backward rules as the other lattice connectives.

- [#8309](https://github.com/leanprover/lean4/pull/8309)
  changes the definition of `Decidable p` to a structure containing a `Bool` and a proof of either `p` or `¬p`.

- [#14824](https://github.com/leanprover/lean4/pull/14824)
  adds `apply` equations for the `PredTrans` operations that had none, so that `simp` reduces `get`, `set`, `modifyGet`, `read`, `throw` and `tryCatch` the way it already reduces `pure`, `bind` and the rest.

- [#14813](https://github.com/leanprover/lean4/pull/14813)
  adds `Triple.and`, `Triple.mp` and `Triple.observe` to `Std.WP`. Each combines two Hoare triple specifications for one program into one.

- [#14801](https://github.com/leanprover/lean4/pull/14801)
  ports the soundness class `WPSound` from `Std.Do` to `Std.WP`, where it is called `LawfulWPMonadAttach`.

- [#12330](https://github.com/leanprover/lean4/pull/12330)
  removes an Iff-True from two statements about arrays. This makes them harder to use, because you cannot use them directly to rewrite. Additionally, they are also not in simp formal form due to `iff_true`.

- [#14751](https://github.com/leanprover/lean4/pull/14751)
  gives a `repeat` or `while` loop one gadget per set of annotations it states, `forInLoopWithInvariant`, `forInLoopWithVariant` or `forInLoopWithInvariantAndVariant`, replacing a single gadget that carried both annotations in `Option` slots.

- [#14744](https://github.com/leanprover/lean4/pull/14744)
  lets `grind` discharge the verification conditions of a `repeat` or `while` loop that states a termination measure in a monad with state, where the proof had to evaluate the measure with `simp_all` first. `RepeatVariant.EvalsTo` and `RepeatVariant.EvalsBelow` gain the fixed-arity ground instances that `grind` can key on, at arities 1 through 5.

- [#14711](https://github.com/leanprover/lean4/pull/14711)
  corrects the three lemmas `contains_empty`, `not_mem_empty`, `singleton_eq_insert` in `Std.ExtDHashMap` that were accidentally about `Std.DHashMap`.

````

# Tactics

```markdown

- [#15161](https://github.com/leanprover/lean4/pull/15161)
  reduces module import overhead in Lean’s core builds by sharing the parsers for `grind` modifiers.

- [#15159](https://github.com/leanprover/lean4/pull/15159)
  avoids preparing and serializing premise-selection indexes during builds. Keep the selectors, but compute and cache their indexes on first use in each process.

- [#15124](https://github.com/leanprover/lean4/pull/15124)
  fixes a non-linearity in LRAT trimming which causes the original and the trimmed proof to stay alive at the same time instead of reusing the memory.

- [#15116](https://github.com/leanprover/lean4/pull/15116)
  lets `lia` and `grobner` take the same `[...]` parameter list as `grind`, so extra facts and lemmas can be supplied inline (e.g. `lia [foo n]` or `grobner [= sq_def]`) instead of first adding them to the local context with `have`.

- [#14688](https://github.com/leanprover/lean4/pull/14688)
  makes `vcgen` report `No spec found for program …` when the program head is one that no strategy steps and no spec keys on, such as the bare `fun s => …` left by unfolding a `liftM` of an anonymous state transformer. Previously this failed with `Failed to decompose weakest precondition … This should not happen`.

- [#14956](https://github.com/leanprover/lean4/pull/14956)
  introduces definitions for `min`/`max` on `BitVec` as well as support in `bv_decide` for `min`/`max` on `BitVec` and the `UIntX`/`IntX` family of functions.

- [#14928](https://github.com/leanprover/lean4/pull/14928)
  introduces support for symbolic `Nat` shifts and `extractLsb'`. This is done by re-interpreting `x >>> n` as `x >>> BitVec.ofNatClamped (log2 w + 1) n` and `extractLsb'` as a shift + `setWidth`. `bv_decide` will still not perform reasoning over the `n` itself but it will at least know that e.g. in `x >>> n` all output bits are `0` or some of the input bits of `x`. This is achieved by making the `BitVec.ofNatClamped` as an uninterpreted bitvec atom.

- [#14921](https://github.com/leanprover/lean4/pull/14921)
  fixes `simp` and `dsimp` panicking with `PANIC at Lean.Expr.appArg!` / `Lean.Expr.appFn!: application expected` when one simproc rewrites a term to one with fewer arguments. The panic is logged at `info` severity, so the build still exits successfully while emitting it.

- [#14922](https://github.com/leanprover/lean4/pull/14922)
  stops the simprocs `Lean.Elab.WF.paramProj`, `paramMatcher` and `paramLet` from taking part in every `simp` and `dsimp` call. They implement one step of the preprocessing of definitions by well-founded recursion and are of no use elsewhere.

- [#14883](https://github.com/leanprover/lean4/pull/14883)
  makes `vcgen` canonicalize `WP` instances, so monads may register a diamond `WP` instance in addition to the low priority `WP` instance synthesized from `WPMonad.toWP`.

- [#14874](https://github.com/leanprover/lean4/pull/14874)
  deprecates the `mvcgen` and `mvcgen?` tactics in favor of `vcgen` via `deprecated_syntax`, so each use reports a deprecation warning controlled by `linter.deprecated.syntax`.

- [#14870](https://github.com/leanprover/lean4/pull/14870)
  adds the `experimental.vcgen` option and makes `vcgen invariants?` warn that invariant suggestions have not been ported from `mvcgen` and that the feature is slated for removal.

- [#14857](https://github.com/leanprover/lean4/pull/14857)
  makes `vcgen` succeed on a goal whose local context is inconsistent. Previously it failed with `No goals to be solved`.

- [#14856](https://github.com/leanprover/lean4/pull/14856)
  moves the `vcgen frames` clause lookup from `applySpec` into `applySpecs`, so a matching clause is consumed once per goal instead of once per spec candidate. A candidate that fails to apply after the lookup, for example because one of its instance arguments cannot be synthesized, no longer retires the clause, and the next candidate still sees the same provided frame.

- [#14848](https://github.com/leanprover/lean4/pull/14848)
  fixes a bug in `sym =>` initialization. It now correctly handles the case the goal is closed during preprocessing.

- [#14828](https://github.com/leanprover/lean4/pull/14828)
  removes the `@id` hint in the proof term that `vcgen` generates whenever it replaces the target. Removing it speeds up kernel checking of the resulting proof.

- [#14829](https://github.com/leanprover/lean4/pull/14829)
  fixes literal canonicalization in `grind`.

- [#14823](https://github.com/leanprover/lean4/pull/14823)
  head-reduces every verification condition that `vcgen` emits, so a loop over two mutable variables states its entry condition as `0 ≤ 0` rather than `match (0, 0) with | (lo, hi) => lo ≤ hi`, and a condition that reduces to `rfl` closes on the spot instead of reaching the user.

- [#14819](https://github.com/leanprover/lean4/pull/14819)
  makes the conjunctive-precondition classification of `@[spec]` theorems look through `binderNameHint`.

- [#14820](https://github.com/leanprover/lean4/pull/14820)
  adds support for unfolding definitions in `Sym.simp` when a function symbol is provided as a parameter. `sym => simp [f]` now uses the equational theorems of `f`, like `Meta.simp` does, instead of failing.

- [#14814](https://github.com/leanprover/lean4/pull/14814)
  fixes an internal error (`unexpected bound variable #3`) when a declaration that is not a proposition is used as a `Sym.simp` theorem, as in `sym => simp [HAdd.hAdd]`. It now produces a proper error message.

- [#14802](https://github.com/leanprover/lean4/pull/14802)
  implements a `let_to_have` tactic to the interactive `sym =>` mode. It converts the nondependent `let` declarations of the goal target into `have` declarations, producing a definitionally equal goal. This unblocks the efficient `have`-telescope machinery of `Sym.simp` (`simpLet`), which does not process dependent `let`s.

- [#14799](https://github.com/leanprover/lean4/pull/14799)
  eliminates two sources of overhead that made case splits in `grind`/`sym` slow on goals containing large terms. On the new benchmark (a single `cases_next` on a goal with a chain of 6400 `BitVec` operations), the time drops from 5.9 s to 0.11 s.

- [#14787](https://github.com/leanprover/lean4/pull/14787)
  makes `mvcgen` and `vcgen` split programs headed by `cond` (`bif c then t else e`) into one verification condition per branch, with the hypothesis `c = true` or `c = false` in scope, matching the treatment of `if` and `match`.

- [#14118](https://github.com/leanprover/lean4/pull/14118)
  introduces new cost metrics for `grind`'s e-matching graph that can be optionally enabled in its diagnostics via `set_option grind.ematch.diagnostics true`. `grind` is now able to detect:
  - individual instances that have a lot of direct follow up children. Configurable via `grind.ematch.diagnostics.branchThreshold`
  - instances that participated in a large, transitive closure of follow up instances. For this `grind` computes a cost metric that is roughly equivalent to the size of the transitive closure but fairly distributed among multiple parents. Configurable via `grind.ematch.diagnostics.costThreshold`. The metric is based on the cost heuristic of https://github.com/viperproject/smt-scope.

- [#14785](https://github.com/leanprover/lean4/pull/14785)
  turns the fix latency of 50ms when waiting for the SAT solver into an exponential backoff starting at 1ms and going up to 64ms. This should lower the latency for en-mass solving of small SAT problems.

- [#14770](https://github.com/leanprover/lean4/pull/14770)
  fixes a performance issue where proof terms produced by `grind` could trigger kernel deterministic timeouts. `grind` canonicalizes nested `Decidable` instances under the identity wrapper `Grind.nestedDecidable`, leaving the kernel to check `t =?= Grind.nestedDecidable t`. The kernel does not see the `[reducible]` attribute, and its lazy-delta heuristic unfolded `t` instead of the wrapper. When `t` is an instance such as `UInt32.decLe` applied to a symbolic argument and a large literal (e.g., `97 ≤ c.val + 4294967264` coming from `Char`/`UInt32` wraparound), the check descended through `BitVec` and `Fin` into `Nat.ble` on a `2^32`-sized literal with a free variable inside, where the fast numeral path does not apply, and effectively never terminated. Marking `nestedDecidable` as an abbreviation stores the `abbrev` reducibility hint in the declaration itself, which the kernel does honor, so the wrapper side is unfolded first and the check succeeds immediately.

- [#14769](https://github.com/leanprover/lean4/pull/14769)
  fixes an internal `grind` error (`mkEqProof` invoked with terms of different types). An equivalence class can contain terms of different types when they are merged via `HEq` (e.g., `BitVec` terms of different widths related through `cast` terms). The `=`-injection performed by the `[grind hom]` hooks applies only to homogeneous equalities, so `processNewEq` and `processNewDiseq` now skip pairs whose types differ.

- [#14768](https://github.com/leanprover/lean4/pull/14768)
  adds a `lift_lets` tactic for `sym =>` mode. The tactic moves the `let`/`have` declarations of the goal target as far toward the root as their dependencies allow, flattening nested declarations and merging declarations with syntactically equal definitions. The new goal is definitionally equal to the original one. Declarations under `fun`/`∀` binders are not lifted, and hypotheses are never modified.

- [#14766](https://github.com/leanprover/lean4/pull/14766)
  makes `vcgen` keep the exception postcondition of a `@[spec]` theorem that states it as ``epost⟨E⟩`` with `E` schematic. Such a spec was applied with its exception postcondition weakened to `⊥`, leaving the verification condition `⊥`.

- [#14727](https://github.com/leanprover/lean4/pull/14727)
  implements homomorphism simplification sets for the `grind` tactic. Theorems tagged with the new `[grind hom]` attribute translate terms from a source type into a target type that has a dedicated solver (e.g., `Fin`, `BitVec`, and the fixed-width integer types into `Nat`/`Int` arithmetic), and `[grind hom_pred]` theorems supply the range facts for the injection functions (e.g., `Fin.isLt`). The translation is applied to fixpoint outside the E-graph during internalization, so only the final normal form is internalized. The feature is on by default and can be disabled with `grind -hom`.

- [#14763](https://github.com/leanprover/lean4/pull/14763)
  introduces a new `grind`/`sym` mode tactic called `bv_decide_push`. Users can call this tactic at arbitrary points in their proof and it will run pre-processing on everything that has been internalized into the `grind` state so far. `bv_decide_push` then stores the results of this pre-processing step in the goal state in order to speed up future invocations of `bv_decide` or `bv_decide_push`. On pre-processing heavy benchmarks where many subgoals share the same hypotheses, this can lead to 2x performance improvements and higher. Note that this does **not** yet implement incremental SAT solving.

- [#14765](https://github.com/leanprover/lean4/pull/14765)
  lets the `@[spec]`-annotated theorems of a file elaborate in parallel with one another. Previously, any such annotation would block elaboration waiting for the completion of the proof.

- [#14757](https://github.com/leanprover/lean4/pull/14757)
  changes two things about how `bv_decide` collects facts in grind mode:
  1. It will no longer even consider enum/structure/UIntX equivalence classes if the features are disabled
  2. It will not eagerly internalize the goal state on its own as this might be costly. Thus any facts that would be derived from grind internalizing the goal will not be used. However, the goal will still be used as part of bv_decide's contradiction proof.

- [#14747](https://github.com/leanprover/lean4/pull/14747)
  lets `vcgen` continue through a spec whose program applies a continuation variable under a binder, such as for `k` in `Lang.bnd (fun x => Lang.add (k x) (Lang.nat 0))`. First-order matching leaves `k` open and unification assigns it while the pending constraints are processed, which happens after the emitted goal's type has been built, so that goal's program is the metavariable standing for `k` applied to its arguments. `vcgen` used to give up on such a goal with "Failed to decompose weakest precondition … This should not happen". Now it instantiates in the right place.

- [#14745](https://github.com/leanprover/lean4/pull/14745)
  eagerly simplifies the state arguments of a `wp` goal as `vcgen` steps the program when `simplifying_assumptions` is present, so the VCs become cleaner and the simplification work isn't duplicated. On `tests/bench/vcgen/vcgen_get_throw_set_grind` this cuts kernel checking from 862ms to 291ms at n=300, and VC generation is slightly faster as well.

- [#13968](https://github.com/leanprover/lean4/pull/13968)
  adds detection and optimized lowering of if-then-else/XOR/XNOR gates to `bv_decide`'s AIG to CNF lowering. This detects `c ? t : f` gates of the form `(c → t) ∧ (¬c → f)` in the AIG, up to permutation/negation of inputs. This pattern also covers XOR/XNOR which are expressed as `a ? ¬b : b`/`a ? b : ¬b`. When a gate is lowered, if it matches these patterns it is lowered to a 4-clause encoding instead of the 12 clauses used by lowering as AND gates.

```

# Compiler

```markdown

- [#15107](https://github.com/leanprover/lean4/pull/15107)
  allows the `ReduceArity` pass to remove all parameters of a function. If this does happen, it places a `void` parameter to avoid promoting the value to a constant.

- [#15089](https://github.com/leanprover/lean4/pull/15089)
  makes `floatLetIn` pessimistic when considering whether to float things into `cases` that operate on `EST.Out` or `ST.Out`. These cases indicate the potential presence of side effects which, through `ST.Ref`, can cause non-linearities that are not easily predictable through static analysis. Thus we now refuse floating into the `cases` to preserve linearity for sure.

- [#15075](https://github.com/leanprover/lean4/pull/15075)
  fixes an off-by-one error in the max size computation for objects.

- [#15052](https://github.com/leanprover/lean4/pull/15052)
  introduces dynamic tracking primitives to detect non-linearity issues. Users can call `markLinear` on `String`,`ByteArray`, `FloatArray`, and `Array`, this has two effects. First, if they are not already unique they will be forcibly copied and thus made unique. Second, every further write access to them must occur linearly. If the access does not occur linearly and the environment variable `LEAN_ABORT_ON_NONLINEAR` is set, the program aborts. Users can attach a breakpoint on `lean_internal_panic` to figure out where precisely the program gets aborted to track down the linearity issue. Follow up PRs will add `markLinear` operations for other built-in linear data structures.

- [#14969](https://github.com/leanprover/lean4/pull/14969)
  fixes a crash when more than 16 arguments are applied at once to a closure whose arity is at most 16.

- [#14948](https://github.com/leanprover/lean4/pull/14948)
  builds mimalloc with `MI_MAX_ALIGN_SIZE=8`, which means that objects like `List.cons` take 24 bytes instead of 32, improving memory usage and cache efficiency.

- [#14531](https://github.com/leanprover/lean4/pull/14531)
  upgrades LLVM to 23.1.0. This brings slight improvements across the bank for Lean binaries as well as reduced C compilation time.

- [#14888](https://github.com/leanprover/lean4/pull/14888)
  fixes attribute/extern "C" ordering affecting builds with some versions of gcc.

- [#14811](https://github.com/leanprover/lean4/pull/14811)
  writes Lean's C output files atomically do their destination by first creating a temp file and then atomically moving it to the real destination. This is necessary as `clang` reads C files using `mmap` so concurrent writes to the same C file may cause issues. Most notably this should resolve the probabilistic clang lexer segfault we've been observing for a while.

- [#12814](https://github.com/leanprover/lean4/pull/12814)
  changes the handling of proof-over-applied cases expressions in `ToLCNF` to avoid generating function declarations that are called immediately. This is a less invasive version of #12284 (which has since been reverted) that only affects proof overapplications, not all overapplications. However, this is also the only case we really need for #8309 (and other occasions like `match h : _`).

- [#14775](https://github.com/leanprover/lean4/pull/14775)
  fixes the remaining issues with `ST.Ref`. We now enforce that `ST.Ref` acts truly like a spinlock by introducing two changes:
  1. `ST.Ref.set` is now just `discard <| ST.Ref.swap` and fulfills no special purpose for closing the critical section opened by `ST.Ref.take` anymore
  2. We introduce an `unsafe` function called `ST.Ref.put` which may only be called after a critical section has been opened using the `unsafe` `ST.Ref.take`. We then implement `modify` and friends using these operations.

- [#14773](https://github.com/leanprover/lean4/pull/14773)
  restores the interpreter's argument-passing path to the form it had before #14749, which regressed some benchmarks. A borrow annotation on a scalar parameter carries no information, and `Lean.IR.ToIR.lowerParam` now drops it. The interpreter can therefore assume that every borrowed parameter is a reference, and the test that #14749 added at each argument becomes a `lean_assert`.

- [#14749](https://github.com/leanprover/lean4/pull/14749)
  corrects a memory leak. The leak occurs when interpreted code calls a compiled function with a scalar parameter that is marked `@&`.

- [#14585](https://github.com/leanprover/lean4/pull/14585)
  fixes a bug with reference count corruption in `Ref.swap` when raced against `Ref.get`, by replacing the buggy atomic exchange operation with a CAS that prevent swapping with null pointers.

```

# Pretty Printing

```markdown

- [#14971](https://github.com/leanprover/lean4/pull/14971)
  adds completions to the `@[delab]` attribute for the `app` expression kind prefix.

```

# Lake

```markdown

- [#15153](https://github.com/leanprover/lean4/pull/15153)
  bundles the `con-ron` external checker with release toolchains, so it can be used as an independent checker without a separate install.

- [#14835](https://github.com/leanprover/lean4/pull/14835)
  makes job cancellation under `--fail-fast` a first-class notion: canceled jobs are reported as `⊘ Canceled` rather than as successes, and a canceled dependency is no longer misreported as a `bad import`.

- [#15157](https://github.com/leanprover/lean4/pull/15157)
  introduces the `--from-export` option for `lake check` and the `--solution-from-export` and `--challenge-from-export` flags for `lake comparator`. They allow loading export files from already existing NDJSON files instead of building them on the fly. This is useful for several scenarios:
    - Using export files built in virtual machines for extra isolation.
    - Using export files built by third parties, e.g. because they require
      extensive computational resources to generate.
    - Using export files generated through means other than a standard
      `lake build`.

- [#15156](https://github.com/leanprover/lean4/pull/15156)
  adds an expert user flag to comparator to disable its sandbox, this flag should not be used in usual production environments and is only useful if you do not expect the formalisation to not be maliciously trying to attack the system.

- [#15145](https://github.com/leanprover/lean4/pull/15145)
  adds a `--paranoid` flag to `lake check` and `lake comparator` that runs every checker bundled with release toolchains (`leanchecker-paranoid`, `lean4lean`, `nanoda` and `con-leche`) over the export in addition to Lean's own kernel, and accepts only if all of them do.

- [#15141](https://github.com/leanprover/lean4/pull/15141)
  adds a `--package` option to `lake build` and `lake cache put`. On `lake build`, `-o` with `--package` will track the specified package's build outputs instead of the root's. The outputs can then be uploaded via `lake cache put --package`.  Also, to minimize incorrect uploads, `lake cache put-staged`  now requires `--rev` to be manually set.

- [#15147](https://github.com/leanprover/lean4/pull/15147)
  introduces `comparator.json` as the default location for the config file of `lake comparator`.

- [#15146](https://github.com/leanprover/lean4/pull/15146)
   rename lake challenge to lake comparator

- [#15096](https://github.com/leanprover/lean4/pull/15096)
  ensures the output of `lean4export` is never fully materialized in comparator. Instead the output is spooled to a file and then exclusively read using streaming parsers.

- [#15005](https://github.com/leanprover/lean4/pull/15005)
  builds and exports the code `lake challenge` judges inside a further restricted`bubblewrap` sandbox rather than `landrun`, which stops that code from being able to access the invoking user's files and gives the steps that must not reach the network no network at all.

- [#14990](https://github.com/leanprover/lean4/pull/14990)
  adds `lake check`, a challenge-less variant of `lake challenge`, which builds the current project's default targets, exports them, replays the result through the kernel, and fails on any use of non-standard axioms.

- [#15015](https://github.com/leanprover/lean4/pull/15015)
  adds two new configuration options that are subsets of `precompileModules`: `precompileLibrary` for `lean_lib` targets and `precompileImports` for all Lean configurations (e.g., settable on `package`, `lean_lib`, or `lean_exe`). `precompileImports` compiles a module's imports but not the module itself. `precompileLibrary` compiles the whole library for importers, but the library's modules do not compile their own imports during elaboration.

- [#15042](https://github.com/leanprover/lean4/pull/15042)
  fixes a Lake bug where the `moreServerOptions` configuration was only applied to modules outside the package (e.g., when editing scratch fiiles) and not to modules within a package.

- [#14885](https://github.com/leanprover/lean4/pull/14885)
  ships `lake challenge` as a frontend to `comparator`, significantly simplifying its setup. `landrun` remains a hard requirement with no unsandboxed mode, so the command is available on Linux only for now.

- [#14933](https://github.com/leanprover/lean4/pull/14933)
  makes `lake lint --code-quality` emit the code quality entries that linters record during elaboration. Entries logged via `Lean.Linter.logCodeQualityEntryIf` are attributed to the producing linter's option name and are filtered by `--lint-only`; entries logged via `Lean.Linter.logCodeQualityEntry` carry no attribution and are always emitted, so no linter selection flag can suppress them. Disabling a recording linter (e.g. `--linters=-linter.foo`) suppresses its attributed entries at elaboration time, and a module shared between several lint targets contributes its entries only once.

- [#14902](https://github.com/leanprover/lean4/pull/14902)
  fixes Lake omitting imports from a module's setup when one of its imports is both an `import all` and reached transitively through a `meta import`. The `import all` suppressed the later `meta import`, so modules reachable only through the latter were left out of the setup passed to lean.

- [#14797](https://github.com/leanprover/lean4/pull/14797)
  adds a `--fail-fast` option to `lake build` that stops scheduling new build jobs as soon as the first required target fails, letting already-running jobs drain to completion before reporting failures and exiting. Previously Lake always ran every scheduled job to the end, so a build with an early error still paid for the whole workspace.

- [#14853](https://github.com/leanprover/lean4/pull/14853)
  includes `lean.h` (and its transitive includes) from an overridden Lean include directory in the trace of built object files, ensuring they are rebuilt if the header changes (e.g., when bootstrapping). To avoid such changes affecting the public API in the future, `leanIncludeDir?` has been removed from the public API `buildLeanO` and moved to an internal `buildLeanO`.

- [#14716](https://github.com/leanprover/lean4/pull/14716)
  makes `lake lint --code-quality` run the package code quality checks registered with the `@[package_code_quality_check]` attribute. The checks are discovered in each lint target's import closure and run once per target, and their results are emitted as JSON entries alongside the linter-derived ones. Additional modules providing checks can be supplied with the new `--checks` CLI option (which implies `--code-quality`) or the new `checks` package configuration option; these modules are built and then imported alongside each linted module, so checks can be used without adding them to the package's own imports.

- [#14782](https://github.com/leanprover/lean4/pull/14782)
  overhauls the way Lake clones dependencies. Dependencies are now fetched as treeless partial Git clones of a single revision, minimizing the amount of data downloaded. In addition, switching between branches will now avoid a fetch if the new revision (and its trees and blobs) are already present in the repository. Lake also now reuses the repository directory if the dependency URL changes, avoiding file system churn and the potential loss of the dependency on a failed fetch. To further minimize disk usage, Lake will prune remote references and perform Git garbage collection on a dependency repository after fetching a new version.

```

# Other

```markdown

- [#15130](https://github.com/leanprover/lean4/pull/15130)
  bundles the `con-leche` external checker with release toolchains, so it can be used as an independent checker without a separate install.

- [#15099](https://github.com/leanprover/lean4/pull/15099)
  bundles the `nanoda` external checker with release toolchains, so it can be used as an independent checker without a separate install.

- [#15048](https://github.com/leanprover/lean4/pull/15048)
  bundles the `lean4lean` external checker with release toolchains, so it can be used as an independent checker without a separate install.

- [#15055](https://github.com/leanprover/lean4/pull/15055)
  runs the default kernel in a privilege separated process in `lake check` and `lake
  challenge`. This does not fix any concrete security issues but merely serves as an additional hardening measure.

- [#14884](https://github.com/leanprover/lean4/pull/14884)
  adds `bin/leanchecker-paranoid`, a variant of `leanchecker` built with allocator hardening.

```
