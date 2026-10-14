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

#doc (Manual) "Lean 4.36.0-rc1 (2026-10-14)" =>
%%%
tag := "release-v4.36.0"
file := "v4.36.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 216 changes landed.
In addition to the 64 feature additions
and 81 fixes listed below,
there were 11 refactoring changes,
1 documentation improvement,
30 performance improvements,
3 improvements to the test suite,
and 26 other changes.

# Language

```markdown

- [#15572](https://github.com/leanprover/lean4/pull/15572)
  adds a hint/code action the the "[deprecated]` attribute should specify the date or library version at which the deprecation was introduced" warning.

- [#15499](https://github.com/leanprover/lean4/pull/15499)
  makes the statements of generated equation lemmas (`f.eq_1`, `f.eq_2`, …) independent of the options where the equations are first requested. A local `set_option` on the first proof that used the equations could change their statements. Proofs elaborate in parallel, so the statements could differ between builds of the same file, and a proof could compile with some thread counts and fail with others.

- [#15485](https://github.com/leanprover/lean4/pull/15485)
  skips running non-stateful linters if the command has a syntax error and `showPartialSyntaxErrors` is disabled.

- [#14316](https://github.com/leanprover/lean4/pull/14316)
  makes the type class resolution cache persist across commands: a result whose query contains no metavariables, local instances or free variables and which is itself closed is kept for later commands, so identical queries there are served from the cache instead of being searched again. Such an entry is only served while the dependencies it recorded are unchanged, so new instances, unification hints and reducibility changes invalidate exactly the affected entries. On the build of the standard library this reduces type class resolution time by about 14% and total instructions by 1.2%; Mathlib gains 0.2% overall, as most of its queries involve local instances, which are not (yet) persisted.

- [#15399](https://github.com/leanprover/lean4/pull/15399)
  fixes the type class resolution cache serving a result after a declaration it could have observed changed, most notably through a later `attribute [reducible]` or a scoped or local reducibility attribute coming into or going out of effect. As the cache currently lives within a single command, this is rarely visible yet, but it is a necessary prerequisite for sharing the cache across commands, where such changes are routine.

- [#15319](https://github.com/leanprover/lean4/pull/15319)
  adds `Expr.hasAnyMVar` and `Expr.containsMVar` functions analogous to the existing `Expr.hasAnyFVar` and `Expr.containsFVar` functions.

- [#15355](https://github.com/leanprover/lean4/pull/15355)
  makes `SavedState.restore` drop the type class resolution cache entries that were recorded after a tracked environment change it rolls back. The generations validating an entry roll back with the environment while `Meta.Cache` survives the restore, so a different change made afterwards could bring the recorded generations back and let a stale entry be served; for example, an instance added and rolled back in a failed attempt could still be returned after a different instance was added. Apart from closing such edge cases, this is a necessary prerequisite for cross-command caching, whose entries must survive backtracking without being revalidated against a rolled-back state.

- [#15354](https://github.com/leanprover/lean4/pull/15354)
  makes a type class resolution cache entry record the state of the instances and unification hints its search consulted, so that the entry is no longer served once they change, even through environment changes that do not clear the cache. For example, an instance added by a command run through `liftCommandElabM` is now found by later queries in the same computation, and so are scoped instances and unification hints activated at `CoreM` level. Apart from closing such edge cases, this is a necessary prerequisite for cross-command caching.

- [#15325](https://github.com/leanprover/lean4/pull/15325)
  makes type class resolution cache results depend on the options the search read. Previously a cached result was reused regardless of options within a command, so a result obtained under a term-level `set_option`, for example of `synthInstance.maxSize`, could be served where the option had a different value. Options the search never reads still do not partition the cache. Apart from fixing such in-command edge cases, this is a prerequisite to caching across commands.

- [#15313](https://github.com/leanprover/lean4/pull/15313)
  makes realizing the equation lemmas of large mutual `partial_fixpoint` blocks much faster (about 13× for a block of 200 functions), by no longer re-deriving and re-checking the fixpoint equation of the whole block for every function.

- [#11386](https://github.com/leanprover/lean4/pull/11386)
  adds theorems tagged with `wf_preprocess` for making it possible to conveniently write functions over nested inductive types such as trees that use `List.any`, in the same way that they're currently able to use `List.map` and other common list functions.

- [#15286](https://github.com/leanprover/lean4/pull/15286)
  makes a tactic marked by `deprecated_syntax` warn no more than once per call. The tactics that its expansion uses no longer warn again. For example, if `mintro` is deprecated, `mintro a b c` expands to `mintro a; mintro b c` and printed five warnings; now it prints one.

- [#15216](https://github.com/leanprover/lean4/pull/15216)
  makes `inferInstanceAs` reuse the existing instances of a non-exposed definition. This is done by checking the reusability of an instance in the private scope, as neither the auxiliary definitions being generated nor the ones in the existing instance are exposed in this case.

- [#15204](https://github.com/leanprover/lean4/pull/15204)
  rejects the `←` simp-argument modifier when the argument is a simproc or a simp extension, instead of silently ignoring it.

- [#15237](https://github.com/leanprover/lean4/pull/15237)
  adds `Environment.realizationEnvContains forConst c`, which reports whether `realizeConst forConst` callbacks can access `c`. This is the criterion for choosing `forConst` when a realization depends on multiple constants: the target must be one whose realization environment contains all others.

- [#14537](https://github.com/leanprover/lean4/pull/14537)
  improves on the error messages of `rfl` and a few other tactics that fail due to a failed definitional-equality check. There was already a mechanism that analyzed what parts of the term need to be shown explicitly so that the mismatch becomes visible, but it sometimes ran with the wrong configuration. This change fixes these problems.

- [#15242](https://github.com/leanprover/lean4/pull/15242)
  speeds up the elaboration of structurally recursive definitions by removing work from the construction of the `brecOn` application that has no effect on the result.

- [#15240](https://github.com/leanprover/lean4/pull/15240)
  makes `Meta.isProofQuick` return a definite answer for applications such as `match` auxiliary functions, `casesOn`, `brecOn`, and recursors, whose type is a `motive` variable applied to arguments. Previously these fell through to `isProof`'s slow path, which infers the type and reduces it to a sort.

- [#15239](https://github.com/leanprover/lean4/pull/15239)
  removes a redundant `abstractNestedProofs` pass when elaborating structurally recursive definitions, which reduces elaboration time for files with many such definitions.

- [#15238](https://github.com/leanprover/lean4/pull/15238)
  removes the per-declaration overhead #15232 introduced in the LCNF declaration extensions, which cost about 1% of instructions when compiling modules with many declarations, while keeping the linear-time replay of realized constants.

- [#15232](https://github.com/leanprover/lean4/pull/15232)
  makes the cost of realizing a constant (e.g. the equation lemmas needed by `simp only [f]`) independent of the size of the current file. Previously, files with many such realizations slowed down quadratically: on a file with 4,000 definition/theorem pairs elaboration time drops from 99 s to 32 s, and the time per pair is now constant.

- [#15230](https://github.com/leanprover/lean4/pull/15230)
  speeds up the elaboration of definitions using `match`, and of other auxiliary definitions created with `mkAuxDefinition` and `mkAuxTheorem` with `zetaDelta := false`. On a file with 12,800 small pattern-matching definitions, cumulative elaboration time drops from about 19s to about 17s.

- [#15228](https://github.com/leanprover/lean4/pull/15228)
  fixes a per-command overhead in the frontend that grew linearly with the position of the command in the file, making files with many commands quadratic.

- [#15223](https://github.com/leanprover/lean4/pull/15223)
  fixes a quadratic slowdown when elaborating files with many recursive definitions. The `share common exprs` step of definition elaboration hashed the whole input file once per recursive call, so a file with thousands of structurally or well-founded recursive definitions could spend most of its elaboration time there.

- [#15091](https://github.com/leanprover/lean4/pull/15091)
  adds `throws e => R` clauses to `def` contracts, after `ensures`, stating the exception postcondition of the generated specification theorem. A clause binds the raised exception and, in a state monad, the state at the throw. An ascription `throws (e : ε) s => R` selects the exception layer of type `ε`, and an unascribed binder selects the outermost layer. Every unmentioned exception layer keeps the postcondition `⊥`, so the specification still rules out its exceptions, while an omitted `ensures` keeps the postcondition `⊤`.

- [#15064](https://github.com/leanprover/lean4/pull/15064)
  replaces the parser used for Verso docstrings with one that correctly tracks all details of the underlying concrete syntax. Along the way, the API for docstring extensions was improved and parser error messages were made much more actionable. This unblocks automatically formatting Verso docstring syntax.

- [#15199](https://github.com/leanprover/lean4/pull/15199)
  removes the `internal.parseQuotWithCurrentStage` options from `Lean.Elab.BuiltinDo.Let` and `Lean.Elab.Do.InferControlInfo` that were introduced for bootstrapping reasons, recovering the build-instruction regression that #15090 introduced.

```

# Library

```markdown

- [#15654](https://github.com/leanprover/lean4/pull/15654)
  fixes a memory leak in `String.toByteArray` and `String.toUTF8` that has been present for a long time but was uncovered by a recently added test.

- [#15581](https://github.com/leanprover/lean4/pull/15581)
  redefines the order on `String` to be the lexicographic order of the UTF-8 encoding, not of the character list.

- [#15659](https://github.com/leanprover/lean4/pull/15659)
  exports the lemmas declared in `Init.Data.Int.DivMod.Pow`.

- [#15651](https://github.com/leanprover/lean4/pull/15651)
  adds `String.fromUTF8Lossy`, a function that attempts to parse a `ByteArray` into a `String`, replacing invalid UTF-8 with the Unicode replacement character in a certain well-defined way.

- [#15647](https://github.com/leanprover/lean4/pull/15647)
  adds missing simprocs for bitgwise operations on `UIntX`/`IntX`.

- [#15628](https://github.com/leanprover/lean4/pull/15628)
  makes `Lean.Json.parse` reject JSON objects that contain the same key twice (compared after unescaping), instead of silently keeping the last value.

- [#15594](https://github.com/leanprover/lean4/pull/15594)
  renames error function names and other helper functions.

- [#15547](https://github.com/leanprover/lean4/pull/15547)
  add RAII-based scoped lock guard

- [#15545](https://github.com/leanprover/lean4/pull/15545)
  removes the allocation of the libuv handle in uv sockets, timer and signal objects.

- [#15571](https://github.com/leanprover/lean4/pull/15571)
  fixes how `0` is handled in the `LT JsonNumber` instance. Before the fix, `(0 : JsonNumber) < 5e-2` would evaluate to `false`.

- [#15523](https://github.com/leanprover/lean4/pull/15523)
  fixes crashes in libuv timers and signals:

  * One shot timer and signal callbacks resolved their promise before releasing the event loop's reference to the handle (sync := true) caused this.
  * libuv treats a repeat period of 0 as a oneshot timer, so a repeating `Timer` with a 0 ms period fired once and every later promise stayed pending. It now ticks every millisecond.
  * `Signal.cancel` only drops the pending promise and keeps the handler listening, and a signal that arrives with no promise pending resolves the promise of the next `next`.
  * Signal waiters resolve with the number from `Signal.toInt32` on every platform, instead of the operating system's number for that signal.

- [#15469](https://github.com/leanprover/lean4/pull/15469)
  makes the `Std.Http` server generate its `Date` header in the HTTP-date format of RFC 9110 §5.6.7, for example `Sun, 06 Nov 1994 08:49:37 GMT`, instead of with a numeric offset (`+0000`). Clients that parse HTTP dates strictly, such as Apache HttpClient's cache, Go's `http.ParseTime` and Rust's `httpdate`, did not accept the previous form.

- [#15533](https://github.com/leanprover/lean4/pull/15533)
  reimplements `String.toList` in Lean. In doing so it also removes all hints that
  `String.data` ever existed as it has now almost been a year since its deprecation.

- [#15443](https://github.com/leanprover/lean4/pull/15443)
  makes the `Std.Http` server send responses on systems without a timezone database (for example the `ubuntu:24.04` Docker image, which does not ship `tzdata`). Previously the server closed every connection without a response, because generating the `Date` header looked up `UTC` in the zoneinfo files.

- [#15517](https://github.com/leanprover/lean4/pull/15517)
  changes the index of `Lean.Order.iSup` and `Lean.Order.iInf` to `{ι : Sort v}`, so `⨆ h : P, f h` over a proposition `P` elaborates. The lemmas `le_iSup`, `iSup_le`, `iInf_le`, `le_iInf`, `iSup_apply` and `iInf_apply` take the same `Sort` index.

- [#15175](https://github.com/leanprover/lean4/pull/15175)
  stops `Loop.configure` from leaking and rejects `System.random` values above 2^31-1 before allocating a huge array.

- [#15329](https://github.com/leanprover/lean4/pull/15329)
  adds efficient `LE` and `Ord` instances for `ByteArray` and deduces all other order instances from that.

- [#15316](https://github.com/leanprover/lean4/pull/15316)
  removes the duplicate `BEq (Option a)` instance derived in `Init.Data.Option.Basic` and instead makes the one derived in `Init.Core` exposed.

- [#15315](https://github.com/leanprover/lean4/pull/15315)
  changes the attributes at `Array.compareLex` and `Vector.compareLex` to make sure that they actually get specialized. Previously, the comparison function was just passed by closure.

- [#15304](https://github.com/leanprover/lean4/pull/15304)
  adds the missing order instances for `List`, `Array` and `Vector`.

- [#15299](https://github.com/leanprover/lean4/pull/15299)
  makes `grind`, and with it `vcgen … with finish`, prove goals about assertions that use lattice operations more reliably. For example, the `nodup` proof of the `vcgen` tutorial now closes with `vcgen … with finish`, as it used to with `mvgen`.

- [#15414](https://github.com/leanprover/lean4/pull/15414)
  tunes down some overeager grind e-matching annotations that would over-eagerly trigger cross-theory reasoning.

- [#15387](https://github.com/leanprover/lean4/pull/15387)
  adds lemmas to the lattice theory in `Std.Internal.Order` and computation rules for predicate transformers.

- [#15192](https://github.com/leanprover/lean4/pull/15192)
  fixes `ContextAsync.race` and `ContextAsync.raceAll`,`ContextAsync.run` and `ContextAsync.background` cancellations and `Notify.notifyOne` no longer spends its wakeup on a waiter whose select was already decided.

- [#15274](https://github.com/leanprover/lean4/pull/15274)
  adds the missing order instances on `BitVec`.

- [#15174](https://github.com/leanprover/lean4/pull/15174)
  solves multiple issues in the TCP and UDP modules.

- [#15266](https://github.com/leanprover/lean4/pull/15266)
  adds logical models for the `Float.minimum` and `Float.minimumNumber` operations that were added in #15257.

- [#15257](https://github.com/leanprover/lean4/pull/15257)
  defines `Float.minimum` and `Float.minimumNumber`, which correspond to the IEEE-754-2019 operations of the same name. It redefines `Min Float` to mean `Float.minimum`.

- [#15115](https://github.com/leanprover/lean4/pull/15115)
  exposes `Char.ordinal`, `Char.ofOrdinal`, `Char.succ?` and `Char.succMany?`, so that they reduce across module boundaries. Ranges over `Char` are built from `Char.succ?` and `Char.succMany?` via the `UpwardEnumerable Char` instance, so previously `cbv` and kernel reduction got stuck on these in any file using the module system.

- [#15247](https://github.com/leanprover/lean4/pull/15247)
  introduces a basic FFI module for CaDiCaL as well as a small wrapper around it to interact with our `Std.Sat` API.

- [#15252](https://github.com/leanprover/lean4/pull/15252)
  removes the `withPtrEq` function.

- [#15217](https://github.com/leanprover/lean4/pull/15217)
  renames the `EPred` type variable to `EPosts` and the `epost` value variable to `eposts`, since they denote a bundle of exception postconditions rather than a single predicate, and adds deprecated_arg aliases so code passing `EPred` by name keeps compiling.

- [#15171](https://github.com/leanprover/lean4/pull/15171)
  renames several `Std.WP` names for consistency and deprecates the old ones. The `WP.wpTrans` projection becomes `WP.trans`, its monotonicity field `WP.wp_trans_monotone` becomes `WP.trans_monotone`, and the `wpTrans_apply_eq` lemma becomes `trans_apply_eq`. The weakest-precondition monotonicity lemmas `WP.wp_consequence`/`wp_econs` become a uniform `wp_monotone` family: `wp_monotone` for both channels, `wp_monotone_post` and `wp_monotone_epost` for one channel, `wp_monotone_bot` for the empty exception postcondition, and the `_le` transitivity variants.

- [#15201](https://github.com/leanprover/lean4/pull/15201)
  refactors the AIG to CNF transformation from only acting on `AIG Nat` to acting on generic `AIG` types. This has two advantages:
  1. We don't have to perform the `relabelNat` step anymore and the CNF representation gets slightly more efficient. This is because instead of using the `Nat` from the `AIG` atom as the identifier we now use the indices into the AIG as an identifier and thus avoid producing one tseitin atom per AIG atom.
  2. In the future we will be able to use the AIG to CNF API in an incremental fashion across multiple runs. Towards this we also already introduce the `State.cast` API for reusing a cache state across runs.

- [#15067](https://github.com/leanprover/lean4/pull/15067)
  extends the frame mechanism to the exception channel of `Std.WP`. For example, a program logic whose exceptional exits carry state now supports a frame rule such as `⦃P⦄ x ⦃Q; E⦄ → ⦃F ⋆ P⦄ x ⦃F ⋆ Q; F ⋆ E⦄`. The frame closure, the frame condition, and the frame rule gain a companion operator `opE : R → EPred → EPred` for the exception postcondition that defaults to ignoring the frame.

- [#14793](https://github.com/leanprover/lean4/pull/14793)
  fixes #14776

- [#14795](https://github.com/leanprover/lean4/pull/14795)
  fixes two issues in recv functions of the UDP and TCP modules.

```

# Tactics

```markdown

- [#15678](https://github.com/leanprover/lean4/pull/15678)
  fixes `grind` failing to prove goals such as `c = b → a ≤ b + c + d → a ≤ b + b + d` in an ordered ring when the `Sym.simp` normalizer is enabled (`set_option backward.grind.normalizer false`). The normalizer rewrites `b + b + d` to `2 * b + d`, so the two inequalities are no longer congruent after `c = b`, and no module related the two sums.

- [#15675](https://github.com/leanprover/lean4/pull/15675)
  fixes `grind` failing with the internal error "structure does not have a lawful LT instance" (or "structure does not support LT") when `linarith` has to reason about `<` on a type without a `LawfulOrderLT` instance. For example, `[IntModule α] [LE α] [LT α] [IsLinearOrder α] [OrderedAdd α] (a b c : α) : a < b → b < c → a < c` now fails with a regular `grind failed` message.

- [#15672](https://github.com/leanprover/lean4/pull/15672)
  fixes `grind` failing to use `k⁻¹` for a numeral `k` in a field when the `Sym.simp` normalizer is enabled (`set_option backward.grind.normalizer false`). For example, `[Field R] [IsCharP R 0] (h : f (a * 2⁻¹) = 1) (h2 : a = 2 * b) : f b = 1` was not proved.

- [#15642](https://github.com/leanprover/lean4/pull/15642)
  adds the option `Grind.Config.distrib` (default `false`) to the `Sym.simp`-based `grind` normalizer. By default, a product of two non-constant polynomials such as `x * (y + 1)`, a power of a sum, and the inverse of a product are kept as atoms whose factors are normalized, as the legacy normalizer does; `grind +distrib` expands them into polynomial normal form. Linear arithmetic procedures treat nonlinear terms as atoms, so keeping them unexpanded preserves facts such as `x * (y + 1) = x * z` after `y + 1 = z` is derived.

- [#15624](https://github.com/leanprover/lean4/pull/15624)
  makes `grind` put `k#w` literals with a symbolic width `w` in the `OfNat.ofNat` form it uses for `BitVec` literals, so with the `Sym.simp`-based normalizer theorems such as `BitVec.sdiv_zero` apply to `x.sdiv 0` as they do with the legacy normalizer.

- [#15623](https://github.com/leanprover/lean4/pull/15623)
  makes the `Sym.simp`-based `grind` normalizer rewrite dependent propositional binder domains, so `∀ h : i < a.size, q h` becomes `∀ h : i + 1 ≤ a.size, ...` as with the legacy normalizer.

- [#15619](https://github.com/leanprover/lean4/pull/15619)
  fixes a panic in the `Sym.simp`-based `grind` normalizer on `match` equations whose patterns contain arithmetic, e.g. `grind [h.eq_def]` for a function matching on `Vec α (n + 1 + 1)`.

- [#15618](https://github.com/leanprover/lean4/pull/15618)
  fixes spurious `ring term with unexpected instance` issues in `grind` for casts over abstract rings, e.g. `(m + n) • a = m • a + n • a` with `[CommRing R]`, and the corresponding failures of the `Sym.simp`-based normalizer.

- [#15616](https://github.com/leanprover/lean4/pull/15616)
  adds `BitVec.zero`, `BitVec.ofNat _ (Bool.toNat _)`, and `BitVec.carry` to the list of supported terms by `bv_decide`

- [#15612](https://github.com/leanprover/lean4/pull/15612)
  fixes `grind` losing a hypothesis whose type is marked `[grind cases eager]` when the hypothesis is introduced by `intros` or asserted as a parameter fact. Only the constructor fields survived in each branch, so `example : P → ¬P → False := by grind` and `grind [(mkP)]` on the goal `P` failed for a predicate `P` with field-less constructors.

- [#15611](https://github.com/leanprover/lean4/pull/15611)
  fixes `grind?` failing with "proof contains unresolved internal metavariable" when a parameter fact has a type marked `[grind cases eager]`. Asserting such a fact splits the goal during initialization, and `grind?` only produced a script for the first goal. It now handles every goal, and the suggested script carries one `·` block per goal.

- [#15609](https://github.com/leanprover/lean4/pull/15609)
  makes `grind [mkP]` accept a theorem whose statement is not a `∀` and is not indexable, e.g., `theorem mkP : P` for a nullary inductive predicate `P`. The parameter is asserted as a fact, so the workaround `grind [(mkP)]` is no longer needed. `grind?` and `finish?` keep such identifiers in their suggestions.

- [#15606](https://github.com/leanprover/lean4/pull/15606)
  fixes a spurious "generated tactic cannot close the goal" warning from `finish?` when its parameters alone close the goal, e.g. `grind => finish? [inj f_inj]`.

- [#15602](https://github.com/leanprover/lean4/pull/15602)
  fixes `grind?` and `finish?` dropping parameters such as `inj f_inj` and `funCC q` from their suggestions, which then failed when pasted.

- [#15600](https://github.com/leanprover/lean4/pull/15600)
  fixes `grind` failing on instances wrapped in `@[implicit_reducible]` definitions.

- [#15599](https://github.com/leanprover/lean4/pull/15599)
  fixes a `grind` internal error, `ring term has not been internalized`, triggered when the ring solver learned a disequality such as `a ≠ b` while a term containing `a - b` was still being internalized. The Rabinowitsch step then built `(a - b) * (a - b)⁻¹` and internalized it before `(a - b)⁻¹` had an `ENode`. Closes #15590.

- [#15589](https://github.com/leanprover/lean4/pull/15589)
  fixes a panic in `grind ring` when propagating implied equalities in rings without `NoNatZeroDivisors`, such as `BitVec n`.

- [#15588](https://github.com/leanprover/lean4/pull/15588)
  fixes a `grind` internal error (`ring term has not been internalized`) triggered when a user-defined `Pow Int Nat` instance with higher priority is in scope. Mathlib's `Monoid.npow` instance on `Int` hits this case after #15506.

- [#15555](https://github.com/leanprover/lean4/pull/15555)
  makes `vcgen` take the program type and the `WP` instance from the goal's `wp` application when it applies a spec. Thus `vcgen` works on a goal whose program is not of the instance's program type, for example a program `e : Exp` in a goal `wp (Prog := Tagged n Exp) e Q E` for `def Tagged (n : Nat) (α : Type) := α`.

- [#15582](https://github.com/leanprover/lean4/pull/15582)
  makes `cbv` evaluate `cond` (`bif c then a else b`) lazily, like `ite` and `dite`. Before this change, `cbv` evaluated both branches of `cond`, even when the condition was the literal `true`. An expensive or non-terminating branch that the condition does not select cost time or exhausted `cbv.maxSteps`. The fix gives the `cond` simproc pattern all four arguments of `cond`.

- [#15497](https://github.com/leanprover/lean4/pull/15497)
  adds a guard to `WP.Frames`, so that `vcgen` can frame a resource across a program whose footprint depends on the state.

- [#15526](https://github.com/leanprover/lean4/pull/15526)
  fixes a kernel error when `sym => simp` rewrites inside a non-dependent arrow (e.g. `x + 0 = y → p`) in a file using `module`.

- [#15515](https://github.com/leanprover/lean4/pull/15515)
  makes `vcgen` split a spec precondition `fun _ => ∃ h : i < xs.size, Q () xs[i]` into the VC `i < xs.size` and the entailment for `Q () xs[i]` under a hypothesis `h`, so that the `wp` of the program tail in the body is stepped. The precondition `fun _ => ⨆ h : i < xs.size, Q () xs[i]` splits the same way.

- [#15524](https://github.com/leanprover/lean4/pull/15524)
  fixes a `grind` internal error (`unknown free variable`) on hints such as `grind [h _ _ pf]` whose only hole is a proof. It broke `List.pairwise_iff_forall_infix` in Mathlib after #15506.

- [#15506](https://github.com/leanprover/lean4/pull/15506)
  fixes a `grind` internal error (`semiring term has not been internalized`) triggered when power propagation rebuilds a term whose arguments are still being internalized (#15479).

- [#15503](https://github.com/leanprover/lean4/pull/15503)
  fixes `sym` with `arith` and `grind` with the `Sym.simp`-based normalizer on goals whose equations are over a type in `Sort u`, such as `{α : Sort u} (a b : α)`. The ring classifier computed the universe level of the carrier with `getDecLevel`, which fails with "invalid universe level, u is not greater than 0" for such types; it now uses `getDecLevel?` and reports that the type has no ring structure, as the order classifier already did.

- [#15491](https://github.com/leanprover/lean4/pull/15491)
  makes `vcgen` recognize more `@[spec]` preconditions as conjunctive in the schematic postcondition `Q`/`E`. `vcgen` applies such a spec directly and runs no frame inference for it.

- [#15487](https://github.com/leanprover/lean4/pull/15487)
  makes `vcgen` split a pointwise `∧` in a spec's precondition like a lattice meet `⊓`.

- [#15483](https://github.com/leanprover/lean4/pull/15483)
  makes `Sym.simp` rewrite a raw `Nat` literal that is not the argument of a numeral into the `OfNat.ofNat` form, as `Meta.simp` does. Rewrite rules whose pattern variable binds the raw literal of a numeral, such as the `[grind hom]` rule `(OfNat.ofNat a : Fin n).val = a % n`, produced terms like `nat_lit 0 % (p + 1)` that no later step recognized as a numeral, so `grind` with the `Sym.simp`-based normalizer failed on goals over `Fin (p + 1)` and `BitVec n`.

- [#15482](https://github.com/leanprover/lean4/pull/15482)
  makes `grind` prove goals over `UIntN` and `BitVec` that multiply by a numeral close to the modulus, such as `-1 * a` or `4294967295 * a` over `UInt32`; these previously exhausted the `lia` step budget. The `[grind hom]` injection into `Nat` turned `(c * a).toNat` into `c * a.toNat % 2^w`, and `cutsat` splits on the coefficient `c` when it has to eliminate `a.toNat` exactly, while `(-a).toNat` is `(2^w - a.toNat) % 2^w`, with coefficient `1`.

- [#15478](https://github.com/leanprover/lean4/pull/15478)
  fixes a kernel-rejected proof in `grind`'s ring module. For an inverse `a⁻¹` with a numeral `a`, `processInv` asserts `a * a⁻¹ = 1` or `a⁻¹ = 0` with theorems whose numeral is `denoteInt k`, i.e. an `OfNat` numeral or its negation, but the recognizer also accepted `↑(0 : Nat)`, `↑(3 : Int)`, `-0`, and `- -3`, which are only propositionally equal to `denoteInt k`; `Field.inv_zero : 0⁻¹ = 0` was then pushed as a proof of `(↑0)⁻¹ = ↑0`.

- [#15476](https://github.com/leanprover/lean4/pull/15476)
  makes the `Sym` arithmetic normalizer rewrite a cast of a numeral (`↑(0 : Nat)`, `↑(-2 : Int)`) to the numeral of the carrier wherever it occurs, as the legacy `grind` normalizer does. Casts were interpreted only inside `+`, `*`, ...; a cast standing alone, as a function argument or under `⁻¹`, was kept, so `(↑0)⁻¹` reached the ring solver of `grind`, which applied `Field.inv_zero` to it and produced a proof rejected by the kernel (`grind_9321` with `backward.grind.normalizer := false`).

- [#15475](https://github.com/leanprover/lean4/pull/15475)
  makes the `Sym.simp`-based `grind` normalizer rewrite every `Fin` literal to its canonical form. A literal such as `@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat`, with a nested numeral as value and a ground type index, was left as is, and `grind` treated it as a literal distinct from `(0 : Fin 2)`, producing proofs rejected by the kernel (`grind_canon_ofnat`).

- [#15473](https://github.com/leanprover/lean4/pull/15473)
  adds a `Sym.dsimp` pass after `Sym.simp` in the `Sym.simp`-based `grind` normalizer, so that beta-redexes and projections of structure instances in the fixed arguments of an application are reduced, as the legacy normalizer does with `Simp.Config.dsimp`. `Sym.simp` does not visit these arguments, and a redex left in the implicit objects of a morphism composition made the goals of `Functor.flip` in `grind_cat.lean` miss `NatTrans.naturality`.

- [#15467](https://github.com/leanprover/lean4/pull/15467)
  makes the projection reduction of `Sym` (`Sym.reduceProjApp?`, used by `Sym.simp`, `Sym.dsimp`, and the canonicalizer) expose the structure argument at `.reducible` transparency, as `simp` does, instead of the ambient one. With the `Sym.simp`-based `grind` normalizer, E-matching patterns are normalized at attribute time at `.default` transparency, so a pattern such as `(asIso f).hom` unfolded `asIso` and collapsed to a variable, and the theorem was rejected with `invalid pattern`.

- [#15466](https://github.com/leanprover/lean4/pull/15466)
  fixes two ways a `grind` congruence table entry could go stale, which made `grind.debug` fail nondeterministically on goals with `match` conditions, and adds a deterministic invariant check for the table.

- [#15465](https://github.com/leanprover/lean4/pull/15465)
  makes the `Sym.simp`-based `grind` normalizer respect the annotations on `match` equations: `Grind.simpMatchDiscrsOnly` (only the discriminants of the `match` are simplified) and `Grind.PreMatchCond` (the condition is left as is). E-matching instances of match equations, e.g. from `f.eq_def`, now work with `backward.grind.normalizer := false`, where they used to fail or produce proofs rejected by the kernel.

- [#15464](https://github.com/leanprover/lean4/pull/15464)
  adds the option `backward.grind.normalizer`. It defaults to `true`, which selects the legacy `simp`-based `grind` normalizer; with `false`, `grind` normalizes hypotheses, the target, E-matching instances, generalized patterns, and E-matching patterns at attribute time with the `Sym.simp`-based normalizer developed with `grind_norm`. The default behavior is unchanged.

- [#15463](https://github.com/leanprover/lean4/pull/15463)
  extends `Sym.Simp.evalGround` to evaluate `Int.toNat`, `Int.natAbs`, and `toNat` on `UInt8`, `UInt16`, `UInt32`, and `UInt64` literals, e.g. `(-7 : Int).natAbs` becomes `7`. `grind` is affected too, since the `[grind hom]` rewriter uses `evalGround`.

- [#15461](https://github.com/leanprover/lean4/pull/15461)
  makes the realized constants required by `bv_decide` private to avoid name clashes while
  importing multiple modules that realized them.

- [#15460](https://github.com/leanprover/lean4/pull/15460)
  extends `Sym.Simp.evalGround` to evaluate `String.push` and `String.singleton` on literals, e.g. `"abc".push 'd'` becomes `"abcd"`. `grind` is affected too, since the `[grind hom]` rewriter uses `evalGround`.

- [#15458](https://github.com/leanprover/lean4/pull/15458)
  makes the `Sym.simp`-based `grind` normalizer produce bit-vector literals in `OfNat.ofNat` form, the form `grind` keeps, instead of `BitVec.ofNat`. Ground bit-vector terms such as `3#8 + 5#8`, `3 &&& 5`, `(3#8).zeroExtend 16`, and `300#8` are now evaluated to the same literals as the legacy normalizer.

- [#15448](https://github.com/leanprover/lean4/pull/15448)
  fixes a kernel error in `grind` on goals mentioning both `Char.ofNat 97` and `'a'`, and makes `grind` evaluate `Char.toNat`, `Char.val`, and `Char.ofNat` when the argument is equal to a literal, e.g. `y = 'a' → y.toNat = 97` and `n = 97 → Char.ofNat n = 'a'`.

- [#15445](https://github.com/leanprover/lean4/pull/15445)
  makes `grind` prove goals about `Fin.log2` and about the scoped `Nat` and `Int` casts into `Fin n` through their `val` interpretation, such as `(x.log2).val = Nat.log2 x.val`, `((i : Int) : Fin n).val = (i % n).toNat`, and `((k : Nat) : Fin n).val = k % n`.

- [#15434](https://github.com/leanprover/lean4/pull/15434)
  makes the `Sym.Arith` normalizer solve equations over commutative rings with a nonzero characteristic, such as `Fin n`, `UInt8`, and `BitVec w`, when it runs in the mode used by the `grind` normalizer. An equation `k * m + k' = 0` or `k * m₁ = k * m₂` whose coefficient `k` is invertible modulo the characteristic is solved for the monomial: in `Fin 5`, `4 * x + 2 = 0` becomes `x = 2`, as `2 * x = 6` already becomes `x = 3` over `Int`.

- [#15433](https://github.com/leanprover/lean4/pull/15433)
  extends `Sym.Simp.evalGround` to evaluate the `Fin` functions on literals: `succ`, `castSucc`, `rev`, `last`, `val`, `pred`, `castAdd`, `addNat`, `natAdd`, `castLT`, `castLE`, `subNat`, `mk`, and `ofNat`. It also normalizes `Fin` literals: `(7 : Fin 5)` becomes `2`, and a type index that is not a numeral, as in `(4 : Fin (5 + 1))`, is evaluated. `Fin` arithmetic and comparisons were already supported.

- [#15398](https://github.com/leanprover/lean4/pull/15398)
  introduces a CEGAR/Lemmas on Demand procedure into bv_decide for supporting uninterpreted functions even without interacting with `grind` mode. Towards this it refactors the solving pipeline to be fully incremental and makes use of incremental SAT solving. The congruence feature is available behind `bv_decide +uf`, it is currently limited to:
  1. Only functions that return Bool/BitVec
  2. Only performing congruence reasoning on non-dependent Bool/BitVec arguments (see the bv_uf test for examples of what this entails)

- [#15420](https://github.com/leanprover/lean4/pull/15420)
  fixes a `grind` regression introduced by #15378: a goal such as `Imp (∀ i, i < n → ∃ j, j = i + 1 ∧ p j) (p 4)`, where `Imp a b` unfolds to `a → b` through a `[grind norm]` rule, was no longer proved, while the same goal written with a syntactic `→` still was. `grind` now normalizes the goal before negating it, and the normalizer no longer rewrites `(∀ x, p x) → q` into `(∃ x, ¬p x) ∨ q`.

- [#15419](https://github.com/leanprover/lean4/pull/15419)
  extends `Sym.Simp.evalGround` to evaluate `Char.val` on character literals, e.g. `'a'.val` becomes `97`. It complements #15411, which added the other `Char` operations.

- [#15417](https://github.com/leanprover/lean4/pull/15417)
  fixes an `Application type mismatch` error in `grind` when the homomorphism rewriter translates an equality whose hypothesis mentions a `let`-bound literal, e.g. `b = m.cpop` with `let m : BitVec 2 := 1#2`. Closes #15388.

- [#15411](https://github.com/leanprover/lean4/pull/15411)
  extends `Sym.Simp.evalGround` to evaluate `Char` operations on character literals: `toNat`, `toLower`, `toUpper`, `toString`, `isWhitespace`, `isUpper`, `isLower`, `isAlpha`, `isDigit`, `isAlphanum`, `==`, and `!=`. It also converts `Char.ofNat n` into a character literal when `n` is a numeral, so that a character has a single representation.

- [#15409](https://github.com/leanprover/lean4/pull/15409)
  adds `Sym.Simp.reduceControl`, a variant of `simpControl` that does not block the simplifier: it simplifies the condition of `ite`/`dite`/`cond` and the discriminants of `match`, reduces the term when they are decided, and otherwise lets the simplifier visit the branches. The `Sym.simp`-based `grind` normalizer uses it in place of `reduceMatcher`.

- [#15405](https://github.com/leanprover/lean4/pull/15405)
  fixes a sharing violation in the `arith` simproc of `Sym.simp`, e.g., on `a + f (b + 0)`. With `sym.debug` enabled, it surfaced as a panic in `assertShared`.

- [#15322](https://github.com/leanprover/lean4/pull/15322)
  makes `Sym.intros` introduce a binder whose name starts with `__` as an implementation-detail local, as the elaborator does for such binders. `vcgen` introduces the join point `__do_jp` of a `do` block with `Sym.intros`, so its verification conditions no longer show the join point and its body in the local context.

- [#15389](https://github.com/leanprover/lean4/pull/15389)
  fixes a sharing violation in `Sym.dsimp` when it descends into a `fun`, `∀`, or `let` binder whose bound variable occurs in the body or in a later binder type. With `sym.debug` enabled, the violation surfaced as a panic in `assertShared`.

- [#15383](https://github.com/leanprover/lean4/pull/15383)
  adds the `fallback` modifier to the `[grind hom]` attribute. A fallback rule is applied to a term only when no other homomorphism rule matches it, using the second tier `Sym.simp` already has for `eq_def` unfolding.

- [#15378](https://github.com/leanprover/lean4/pull/15378)
  fixes the `pushNot` simproc of the `grind` normalizer so that `¬(p → q)` becomes `p ∧ ¬q` and `¬∀ x, p x` becomes `∃ x, ¬p x`. These rewrites have been dead code since #9271: the simproc matched the `forallE` case against the whole `¬p` instead of `p`, and checked the domain with the syntactic `Expr.isProp`, which is false for a proposition variable. The same `isProp` check is fixed in the `Sym.simp`-based normalizer.

- [#15377](https://github.com/leanprover/lean4/pull/15377)
  removes the `grind =` attribute from the lemmas that are already `[grind hom]` rules, so that `grind` derives the `toNat`, `toInt` and `val` image of a term once, through the homomorphism rewriter, instead of twice.

- [#15370](https://github.com/leanprover/lean4/pull/15370)
  makes `grind` prove goals that mention the `Bool`-valued signed comparisons `BitVec.slt` and `BitVec.sle`, such as `(x < y) ↔ (x.toBitVec.slt y.toBitVec = true)` for `Int64`, `x.slt y = true ↔ x.toInt < y.toInt`, `x.slt y → y.sle z → x.slt z` and `x.slt y = !(y.sle x)`.

- [#15369](https://github.com/leanprover/lean4/pull/15369)
  makes `grind` prove goals about the signed value of a bitwise complement, such as `(~~~x).toInt = (~~~x.toInt).bmod (2 ^ 16)` for `BitVec 16` and the corresponding goals for the fixed-width signed integer types, as well as plain `Int` facts such as `~~~a = -a - 1`.

- [#15367](https://github.com/leanprover/lean4/pull/15367)
  makes `grind` prove goals about the signed value of a bit vector shifted left by a variable amount, such as `(x <<< n).toInt = (x.toInt <<< n).bmod (2 ^ 16)`, and lets nested signed results compose, such as `((x <<< m) <<< n).toInt = (x.toInt * 2 ^ m * 2 ^ n).bmod (2 ^ 16)`, `((x + y) <<< n).toInt = ((x.toInt + y.toInt) * 2 ^ n).bmod (2 ^ 16)` and `((x * y) * z).toInt = (x.toInt * y.toInt * z.toInt).bmod (2 ^ 16)`.

- [#15366](https://github.com/leanprover/lean4/pull/15366)
  makes `simp [f]` and `dsimp [f]` in `sym =>` mode behave like the default simplifier when `f` is a definition or a conditional theorem. Side conditions of conditional theorems, such as the equational theorems of definitions with overlapping patterns, are now discharged using `grind`. Non-recursive definitions are unfolded when no equational theorem applies. `dsimp` accepts definitions and `rfl`-theorems. Reducible definitions are ignored with a warning instead of failing.

- [#15363](https://github.com/leanprover/lean4/pull/15363)
  fixes a `grind` failure on goals containing `-0 : Int`, such as `f (-((0 : Nat) : Int)) = f 0`, where `grind` produced a proof rejected by the kernel. `-0` is now normalized to `0`.

- [#15365](https://github.com/leanprover/lean4/pull/15365)
  makes `grind` relate the unsigned value of an arithmetic shift to the signed value of its operand: goals such as `((x.sshiftRight n).toNat : Int) = (x.toInt / 2 ^ n) % 2 ^ 16` over `BitVec 16` are now proved.

- [#15364](https://github.com/leanprover/lean4/pull/15364)
  makes `grind` reason about bit-vector rotations through its `[grind hom]` injection into `Nat`: goals such as `(x.rotateLeft n).toNat = (x.toNat * 2 ^ (n % 16) + x.toNat / 2 ^ (16 - n % 16)) % 2 ^ 16` over `BitVec 16`, and the `rotateRight` counterpart, are now proved.

- [#15362](https://github.com/leanprover/lean4/pull/15362)
  fixes `Sym.DSimp.zetaDelta` and `Sym.DSimp.zetaDeltaAll` so that they unfold a let-bound variable that appears as the head of an application. Previously, `dsimp [foo]` and `dsimp [*]` in `grind`/`sym`, and the `bv_decide` normalization passes, left terms such as `foo a b` untouched when `foo := fun x y => x + y` was a local definition, while `Meta.DSimp` reduces them to `a + b`.

- [#15350](https://github.com/leanprover/lean4/pull/15350)
  makes `grind` reason about bit-vector exponentiation through its `[grind hom]` injections: goals such as `(x.pow z).toNat = x.toNat ^ z % 2 ^ 16` and `(x.pow z).toInt = (x.toInt ^ z).bmod (2 ^ 16)` over `BitVec 16` are now proved.

- [#15348](https://github.com/leanprover/lean4/pull/15348)
  makes `grind` reason about bit-vector concatenation through its `[grind hom]` injection into `Nat`: goals such as `(x ++ y).toNat = x.toNat * 2 ^ 8 + y.toNat` over `BitVec 8` are now proved. It also fixes `Sym.simp` rules whose left-hand side has `Nat` arithmetic in a type index, such as the width `m + n` of `(x ++ y).toNat`, which never fired on terms whose width had been normalized to a numeral.

- [#15347](https://github.com/leanprover/lean4/pull/15347)
  lets the `cutsat` solver in `grind` reorder its variables more than once during a proof search. Variables created after the first model search, e.g. by later E-matching rounds, were appended to the variable order; when such a variable has a large coefficient in its bound constraints, the Cooper case split that eliminates it enumerated that coefficient and exhausted `liaSteps`. For example, `(x <<< 1).toInt = (x.toInt <<< 1).bmod (2 ^ 16)` over `BitVec 16` failed because the quotient `x.toNat / 2 ^ 16`, introduced by the instance of `BitVec.toInt_eq_toNat_bmod`, ended up last in the order with a coefficient of `2 ^ 16`. Such goals are now proved.

- [#15345](https://github.com/leanprover/lean4/pull/15345)
  adds support for `&&&` with a constant mask to `grind`, for masks of the form `1…10…0` (a run of ones followed by a run of zeros), over `Nat` and, through the `[grind hom]` injections, `BitVec` and the fixed-width integer types. The mask is rewritten into `%`, `/`, and `*` by literals, which `cutsat` supports: `x &&& (2^n - 1)` becomes `x % 2^n`, and `x &&& ((2^n - 1) * 2^k)` becomes `x / 2^k % 2^n * 2^k`. For example, `(x &&& 0xe0).toNat = x.toNat / 32 % 8 * 32` over `BitVec 8` and `x &&& 0xC0 = 0 → x &&& 0x40 = 0` over `UInt8` are now proved by `grind`. Masks with holes (e.g. `0b101`) and `Int` are not handled yet.

- [#15344](https://github.com/leanprover/lean4/pull/15344)
  makes `Sym.Arith.normalize?` (and hence the `arith` simproc of `Sym.simp`) cancel `x * x⁻¹` for an atom `x` when a discharger proves `x ≠ 0`, in any field. `a * b / a` becomes `b`, `a ^ 3 / a` becomes `a ^ 2`, and `a / (2 * a)` becomes `2⁻¹`. The simproc DSL accepts `arith with d`, so `arith with grind` uses the goal's hypotheses. A result that asked for a side condition is context-dependent.

- [#15343](https://github.com/leanprover/lean4/pull/15343)
  makes numeral inverses rational coefficients in `Sym.Arith.normalize?` (and hence in the `arith` simproc of `Sym.simp`) for fields of characteristic zero. `a / 2 + a / 2` now normalizes to `a`, `a / 2 + b / 3` to `(3 * a + 2 * b) * 6⁻¹`, and relations become denominator-free: `a / 2 + b / 3 = 1` becomes `3 * a + 2 * b = 6`. Without an `IsCharP _ 0` instance, numeral inverses remain atoms.

- [#15259](https://github.com/leanprover/lean4/pull/15259)
  registers `BitVec.toNat_ofInt` as a `[grind hom]` rule, so `grind` can reason about the unsigned value of `BitVec.ofInt`. In particular, `cutsat` can now follow carries computed through `BitVec.ofInt`.

- [#15262](https://github.com/leanprover/lean4/pull/15262)
  registers `BitVec.toInt_signExtend` as a `[grind hom]` rule, so `grind` can reason about the signed value of `BitVec.signExtend`: narrowing reduces `toInt` modulo `2 ^ v`, and widening leaves it unchanged.

- [#15311](https://github.com/leanprover/lean4/pull/15311)
  fixes `grind` never activating E-matching theorems whose ground pattern contains a lambda, a dependent `∀`, or a nonparametric literal such as a `Char` or a negative `Int`. For example, `@[grind .] theorem myPred_of_true : myPred (fun _ => True)` was never used even when the goal contained `myPred mySet` and `mySet = fun _ => True`, and `@[grind =] theorem fc_a : fc 'a' = 1` could not prove `fc 'a' = 1`. Passing such theorems explicitly with `grind [myPred_of_true]` worked, since explicit parameters bypass symbol indexing.

- [#15310](https://github.com/leanprover/lean4/pull/15310)
  fixes `Sym.dsimp` producing terms with dangling free variables when a binder type depends on an earlier binder, e.g. `∀ k : Nat, k < 32 → ...`. This caused `bv_decide` to fail with `unknown free variable`. Closes #15195.

- [#15046](https://github.com/leanprover/lean4/pull/15046)
  fixes `Lean.Meta.Sym.Simp.toHave`, which passed the dependencies of a `have` to `Expr.betaRev` in forward order even though `betaRev` expects them reversed. Any `have` whose value depended on two or more earlier `have`s of the same telescope was rebuilt with its dependencies swapped, producing an ill-typed proof term that the kernel rejects with an application type mismatch.

- [#14827](https://github.com/leanprover/lean4/pull/14827)
  makes `vcgen` state exception postcondition verification conditions pointwise for more exception postcondition types, and makes `throws` clauses work for custom types. For `Except ε`, a spec with the exception postcondition `fun e => e = "x"` now yields `∀ e, e = "x" → …` in place of an entailment between two functions. A custom type such as `structure Thrown where onThrow : String → Prop` gets the same pointwise verification conditions from a `ToEStack` instance, which converts it to an exception postcondition stack. With an `EPostSlot` instance, the type also supports `throws` clauses of `def` contracts.

- [#15290](https://github.com/leanprover/lean4/pull/15290)
  moves the syntax of the `vcgen` tactic to the new module `Std.WP.Tactic` and deprecates the tactics of the `Std.Do` proof mode. `import Std.WP` now provides `vcgen`. Each call of a proof mode tactic, such as `mintro` or `mspec`, reports one deprecation warning that points to `vcgen`. The option `mvcgen.warning` is deprecated because it has no effect.

- [#15298](https://github.com/leanprover/lean4/pull/15298)
  teaches `Sym.Arith.normalize?` (and hence the `arith` simproc of `Sym.simp`) the field rewrites that need no side conditions. In a `Field`, `a / b` becomes `a * b⁻¹`, and inverses are pushed down to the atoms: `(a * b)⁻¹ ↦ a⁻¹ * b⁻¹`, `(-a)⁻¹ ↦ -a⁻¹`, `a⁻¹⁻¹ ↦ a`, `0⁻¹ ↦ 0`, `1⁻¹ ↦ 1`, after normalizing the term under the inverse. `x⁻¹` for an atom or numeral `x` is then an atom of the polynomial, so `a / b + a / b` normalizes to `2 * (a * b⁻¹)`.

- [#15297](https://github.com/leanprover/lean4/pull/15297)
  extends `Sym.Arith.normalize?` (and hence the `arith` simproc of `Sym.simp`) to non-commutative `Ring` and `Semiring` structures. Monomials keep the order of their factors, so `a * b` and `b * a` stay distinct and `(a + b)^2` normalizes to `a^2 + a*b + b*a + b^2`. Terms, relations, and the characteristic are supported as for the commutative case.

- [#15296](https://github.com/leanprover/lean4/pull/15296)
  fixes the `arith` simproc of `Sym.simp` so that reflexive relations between atoms are closed: `x ≤ x` and `x = x` now normalize to `0 ≤ 0` and `0 = 0` and are closed by `post`, like `x + 0 ≤ x` already was.

- [#15295](https://github.com/leanprover/lean4/pull/15295)
  makes the relation normalizer of `Sym.Arith` (and hence the `arith` simproc of `Sym.simp`) use the characteristic of the ring, so that `256 * u + v = v` on `UInt8` normalizes to `0 = 0` and `u + 2 = v` is recognized as already normal. Previously only terms were reduced modulo the characteristic.

- [#15293](https://github.com/leanprover/lean4/pull/15293)
  extends `Sym.Arith.normalize?` (and hence the `arith` simproc of `Sym.simp`) to relations `lhs = rhs`, `lhs ≤ rhs`, and `lhs < rhs` over a `CommRing` or `CommSemiring`. Everything is moved to one side and split by sign, so `x + y = z + 2 * x` becomes `y = x + z`, and `a ≤ b + a` becomes `0 ≤ b`; when both sides normalize to the same polynomial, the goal is closed.

- [#15292](https://github.com/leanprover/lean4/pull/15292)
  adds the `arith` simproc to `Sym.simp`, which normalizes ring and semiring terms into polynomial normal form using `Sym.Arith.normalize?`. It is opt-in through `register_sym_simp` and intended as a `pre` simproc: it sees the maximal arithmetic subtree first, simplifies its atoms with the full simplifier, and reifies it once. Normal forms are final (`done := true`) and cached.

- [#15280](https://github.com/leanprover/lean4/pull/15280)
  makes `Expr.toPolyS` and `Expr.toPolyS_nc` handle a zero exponent like `Expr.toPoly` does, so `x ^ 0` in a semiring normalizes to `1` instead of a monomial with exponent `0`. The `Sym.Arith` normalizer now rewrites `x ^ 0 : Nat` to `1`.

- [#15279](https://github.com/leanprover/lean4/pull/15279)
  adds `Sym.Arith.normalize?`, which rewrites a term of a `CommRing` or `CommSemiring` into polynomial normal form with a proof by reflection. It is the normalizer that `Sym.simp` will use for arithmetic; this PR provides the `SymM`-level API and its tests, not the simplifier integration.

- [#15267](https://github.com/leanprover/lean4/pull/15267)
  fixes regressions in bv_decide around projection and match reduction.

- [#15263](https://github.com/leanprover/lean4/pull/15263)
  moves the classification of order structures (`LE`, `IsPreorder`, `LT`, `LawfulOrderLT`, `IsPartialOrder`, `IsLinearPreorder`, `OrderedRing`) from `grind`'s order module into `Sym.Arith`, so other `Sym` components can reuse it. No user-visible change.

- [#15190](https://github.com/leanprover/lean4/pull/15190)
  makes the `grind` ring solver use the ring classification, operator caches, reification, and denotation from `Sym.Arith`, and deletes the copies it kept under `Grind/Arith/CommRing`. A type is now classified once per `SymM` run instead of once per goal, so every goal of a `grind` run and every tactic of a `sym` block share the result. Code that drives `grind` programmatically sees the new layout: the per-goal ring state holds solver data only, `Result` carries the `Sym.Arith` ring records, and `goalToMessageData` and `evalCheck` take them.

```

# Compiler

```markdown

- [#15516](https://github.com/leanprover/lean4/pull/15516)
  removes the limit of 255 object fields per constructor, and thus per structure.

- [#15539](https://github.com/leanprover/lean4/pull/15539)
  fixes an RC race condition that occurs exclusively in debug code associated with the IR
  interpreter by marking some global objects as persistent. Additionally, it marks one other global
  object as persistent that is currently not used in a multi threaded way but might be in the future
  for hardening purposes.

- [#15520](https://github.com/leanprover/lean4/pull/15520)
  makes the symbol cache return references instead of copying the cache contents out. In addition, it removes uses of references after potential recursive calls into the interpreter. While this is not necessary with the current bucket-based `std::unordered_map` a future `flat_map` design might invalidate these references due to re-hashing which we want to avoid.

- [#15131](https://github.com/leanprover/lean4/pull/15131)
  introduces new fast paths to high arity closure applications. Previously, they would always maintain ownership of their arguments as they pass them to their underlying function pointer, causing non-linearities. This PR introduces the same fast paths as with the other low arity closures for passing the arguments linearly if the closure is passed linearly. Furthermore, closures *may* now tail call, exact behavior is platform and compiler dependent at this point in time and should not be relied upon.

- [#15493](https://github.com/leanprover/lean4/pull/15493)
  makes the IR interpreter resize its stack frames correctly upon function entry instead of dynamically on variable access. This ensure that variable access remains branch free.

- [#15486](https://github.com/leanprover/lean4/pull/15486)
  pre-computes some information about IR decls, to be used in future work.

- [#15407](https://github.com/leanprover/lean4/pull/15407)
  makes `ctorIdx` just read the constructor tag in almost all cases. There are a few notable exceptions to be had here:
  - types with only one ctor may end up being unwrapped to other types if they turn out to be trivial so we want to statically return `1`
  - built-ins like `Nat` and `Int`

- [#15277](https://github.com/leanprover/lean4/pull/15277)
  makes constant folding on `USize` slightly smarter by relaxing the forced equivalence between the `UInt32` and `UInt64` result of the same operation. Previously we required the `UInt32` output and the `UInt64` output to be literally the same. However, in order for a `USize` literal to be interpreted the same on both platform widths, we only need the `UInt32` truncated version of the `UInt64` output to be the same as the `UInt32` output.

- [#15276](https://github.com/leanprover/lean4/pull/15276)
  changes the heuristic for the "equivalent case" folder in LCNF simp. Previously it
  compared every alternative with every other alternative in a cases up to alpha equivalence, causing
  O(n^2) alpha equivalence queries per cases. The new heuristic is inspired by GHC and instead takes
  either:
  - the default or
  - the first alternative with all of its parameters unused

- [#15275](https://github.com/leanprover/lean4/pull/15275)
  introduces constant folders in a more systematic fashion that attempt to cover all interesting and simple connections for `Nat`, `UInt`, and a few special cases in other types.

- [#15256](https://github.com/leanprover/lean4/pull/15256)
  extends the derived values analysis by allowing the compiler to take any form of potentially relevant allocation as a parent for a derived value.

- [#15251](https://github.com/leanprover/lean4/pull/15251)
  changes the way that ExplicitRC determines derived borrows. Previously it would eagerly compute the entire derived values tree for the entire program. This would mean that a single variable `s` would always have all derived values possible in all control flow branches as its children. As all of these children are walked upon use of the value, this causes a lot of excess work. The new pass avoids this by only keeping the derived values in the current program scope around in the tree.

```

# Server

```markdown

- [#15331](https://github.com/leanprover/lean4/pull/15331)
  fixes the goal view showing "no goals" instead of the goal state after an empty `grind =>`, `sym =>` or `impossible by` block, e.g. right after the token or on the following indented line where the next tactic is about to be typed.

```

# Lake

```markdown

- [#15630](https://github.com/leanprover/lean4/pull/15630)
  adds the options `--add-downstream <MODULE>` and `--add-public-downstream <MODULE>` to `lake shake`, which ensure that the given module is imported, directly or transitively, in every checked module where that does not create an import cycle. This gives projects a built-in way to check and enforce that a module providing e.g. linters or code actions, such as a project's `Init` module, is in effect everywhere.

- [#15474](https://github.com/leanprover/lean4/pull/15474)
  makes Lake fetch facets named by partial target keys under their resolved keys, so package-elided, package-named and module requests share the same build-store entries as direct target requests.

- [#15231](https://github.com/leanprover/lean4/pull/15231)
  fixes an issue where Lake would not reuse the cached `.ltar` of a module for `-o` if its contents where not already cached and/or the package was platform independent.

- [#14906](https://github.com/leanprover/lean4/pull/14906)
  splits `leanir` code generation into a separate Lake job and target . The `leanArts` facet on modules and libraries id deprecated and replaced with two distinct facets: `elabArts` and `irArts`. For backwards compatibility, uses of `leanArts` delegate to `irArts`.

- [#12545](https://github.com/leanprover/lean4/pull/12545)
  adds a `lake samply` command that records a CPU profile of a Lean
  executable using [samply](https://github.com/mstange/samply), symbolicates
  addresses, demangles Lean compiler names, and serves the result to
  [Firefox Profiler](https://profiler.firefox.com).

```

# Other

```markdown

- [#15559](https://github.com/leanprover/lean4/pull/15559)
  stops a `module` from exporting constants such as `foo.eq_1` when they were realized only inside a proof, so that such proofs no longer trigger downstream rebuilds. Importing modules realize these constants again on demand.

- [#15558](https://github.com/leanprover/lean4/pull/15558)
  stops a `module` from exporting the entries of declaration-keyed environment extensions, such as projection function info, that belong to private declarations, so that changes to them no longer trigger downstream rebuilds.

- [#15565](https://github.com/leanprover/lean4/pull/15565)
  fixes a panic in `leanir` and three smaller issues found while enabling `compiler.postponeCompile` for core.

- [#15512](https://github.com/leanprover/lean4/pull/15512)
  speeds up module system imports outside the language server and reduces their memory use by no longer building a redundant copy of the imported environment extension entries. Mathlib import time is reduced by ~6%.

- [#15150](https://github.com/leanprover/lean4/pull/15150)
  ensures that `Lean.toolchain` includes a `v` for release versions, e.g. `"leanprover/lean4:v4.34.0-rc2"`, to match the standard format of toolchains in `lean-toolchain` files. (This also enables `ToolchainVer.ofString` to succeed on `Lean.toolchain`.)

```

# Uncategorised

```markdown

- [#15002](https://github.com/leanprover/lean4/pull/15002)
  adds HTML-like syntax to `Lean.Data.Html.Syntax`, together with an elaborator from the syntax into `Lean.Data.Html`.

- [#14935](https://github.com/leanprover/lean4/pull/14935)
  adds a type `Lean.Data.Html` of HTML forests — aimed primarily at authoring HTML (as opposed to internal representation in a web server, etc) — as well as a renderer that produces a `String` object.

```
