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

#doc (Manual) "Lean 4.34.0-rc1 (2026-08-10)" =>
%%%
tag := "release-v4.34.0"
file := "v4.34.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 144 changes landed.
In addition to the 52 feature additions
and 53 fixes listed below,
there were 5 refactoring changes,
5 documentation improvements,
6 performance improvements,
1 improvement to the test suite,
and 22 other changes.

# Language

````markdown

- [#14701](https://github.com/leanprover/lean4/pull/14701)
  lets the `ensures` clause of a `def` contract be written like a `fun`, so a postcondition may be stated per shape of the result: `ensures | none => False | some v => 2 * v ≤ n`. A contract clause now also starts on its own line when pretty printed, as it is written in source.

- [#14686](https://github.com/leanprover/lean4/pull/14686)
  makes the `requires`, `ensures` and `invariant` clauses accept a type ascription on their binders, as `fun` does: `requires s : Nat => s = 0` now elaborates as a binder form instead of being read as a term. An ascription covering all binders of an `invariant` clause is reported as an error, since its first two binders are the loop's consumed prefix and remaining suffix.

- [#14682](https://github.com/leanprover/lean4/pull/14682)
  lets a `for` loop that destructures its binder carry an `invariant` clause, so a loop over a map may bind `(k, v)` and still state its invariant. A container that the clause cannot verify is reported where the clause appears, naming the `PureForIn` instance it lacks, instead of surfacing later as a `vcgen` gadget with no applicable specification.

- [#14596](https://github.com/leanprover/lean4/pull/14596)
  makes `vcgen`'s loop invariants available for every container whose iteration produces its elements without effects. Hash maps, tree maps, their sets, the polymorphic ranges, slices and iterators now support `for … invariant`, including containers whose element type is universe-polymorphic, which previously had no loop specification at all. A new container is supported by declaring that its loop is effect-free, rather than by adding a loop specification for it.

- [#14604](https://github.com/leanprover/lean4/pull/14604)
  adds `cbv at` feature to run `cbv` on local hypotheses, but now it is safe with respect to `SymM` invariants, namely, each `cbv` call (to a local hypothesis) is contained within a single `SymM` context, which remains incremental

- [#14602](https://github.com/leanprover/lean4/pull/14602)
  adds an `assert` element to `do` notation for intrinsic verification. `assert P` states that `P` holds at that point in the program; `assert s => P s` binds the arguments of the assertion itself, such as the state of a state monad, using the same binders `fun` accepts. `vcgen` reads the assertion from the program and proves it as a verification condition; at runtime the element does nothing.

- [#14603](https://github.com/leanprover/lean4/pull/14603)
  lets the `requires` and `invariant` clauses bind the arguments of the assertion itself, so a monad whose assertions are functions no longer needs an explicit `fun`. For a state monad, the state can be named directly:

  ```lean
  def sumIntoState (xs : List Nat) : StateM Nat Unit
      requires s => s = 0
      ensures _ s => s = xs.sum
    := do
    for x in xs invariant pref _ s => s = pref.sum do
      modify (· + x)
  ```

- [#14601](https://github.com/leanprover/lean4/pull/14601)
  makes the loop invariant of `Std.Internal.Do` a plain function of the elements consumed so far and the elements remaining, rather than a cursor indexed by the list being iterated. The `for … invariant` clause binds two lists, `invariant pref suff => …`, and verification conditions mention them directly instead of `{ prefix := …, suffix := …, property := ⋯ }.prefix`.

- [#14589](https://github.com/leanprover/lean4/pull/14589)
  spells the precondition clause of a `def` contract `requires`, pairing with `ensures`.

- [#14586](https://github.com/leanprover/lean4/pull/14586)
  warns about `public/private` visibility modifiers on unnamed `initialize` blocks - they do not do anything which can be confusing.

- [#14581](https://github.com/leanprover/lean4/pull/14581)
  generalizes `withSetOptionIn` over the result type of the wrapped function. The previous signature only accepted a `CommandElab`, which returns `Unit`. The phases of a stateful linter (#14357) return values, so they could not use the helper (see for example leanprover-community/mathlib4#42186). All existing call sites instantiate the result type with `Unit` and do not change.

- [#14579](https://github.com/leanprover/lean4/pull/14579)
  lets a `def` contract discharge the verification conditions `vcgen` cannot prove on its own, in a `spec` section of `where … finally`. The section is an ordinary tactic block, run on whatever `vcgen` leaves open, so the conditions are addressed by their case names and their binders name the variables the condition speaks about:

  ```lean
  def sumEvens (xs : List Nat) : Id Nat
      ensures r => ∃ k, r = 2 * k
    := do
    let mut acc := 0
    for x in xs invariant _cur => acc % 2 = 0 do
      acc := acc + 2 * x
    return acc
  where finally
    | spec =>
      case vc1 acc h => exact ⟨acc / 2, by omega⟩
  ```

- [#14567](https://github.com/leanprover/lean4/pull/14567)
  allows `cbv` to handle stacks of dependent projections, whose composite is non-dependent.

- [#14533](https://github.com/leanprover/lean4/pull/14533)
  changes the way deprecates syntax warnings are displayed. Inside of definitions, which are themselves deprecated, deprecated syntax warnings are silenced.

- [#14564](https://github.com/leanprover/lean4/pull/14564)
  changes the handling of deprecated module warnings. Previously, deprecation warnings were displayed at the syntax ref corresponding to the first command of the file. Now, headers are re-parsed and used to extract correct position for displaying the deprecation warning.

- [#14389](https://github.com/leanprover/lean4/pull/14389)
  adds intrinsic verification syntax for `Std.Internal.Do` do-notation: loop invariants and function contracts that `vcgen` discharges automatically.

- [#14402](https://github.com/leanprover/lean4/pull/14402)
  adds the support for code actions to linters.  When `Elab.async` is enabled, before a linter task is dispatched, we create a promise for the info tree node. Then, we accumulate newly added info trees through the linter execution and we resolve the promise inside of the linter task. Finally, on the main task, we modify the info tree (wrapped in command context) and add a new leaf, with an mvar id, that will eventually be filled with a promise value.

- [#14520](https://github.com/leanprover/lean4/pull/14520)
  fixes an exponential blowup (time and memory, typically surfacing as an out-of-memory failure) in `instantiateMVars` on proof terms that repeatedly reference hypotheses introduced via `MVarId.assert`/`intro` — as done by `MVarId.note`, `replaceLocalDecl`, `simp at h`, and, per step, by LNSym's `sym_n` tactic. Fixes #14329.

- [#14478](https://github.com/leanprover/lean4/pull/14478)
  changes the way we deprecate user-registered options (added via `register_option`). To ensure we get warnings both when interacting with option using `set_option` and in meta code, we require the deprecation to happen via `@[deprecated]` attribute, and we populate the internal `deprecation?` field using the information from that attribute.

- [#7577](https://github.com/leanprover/lean4/pull/7577)
  generalizes the `conv` and `simp` tactics to apply `pi_congr` instead of `forall_congr`. The test case for #7507 has examples that work now, but only worked at universe `v=0` before.

- [#14391](https://github.com/leanprover/lean4/pull/14391)
  refactors `Lean.Environment.replay` to `Lean.Kernel.Environment.replay`, so that environment replays work on `Kernel.Environment` instead of `Environment`, avoiding using the unstable `Environment.ofKernelEnv`. See #13783 for more context.

- [#14357](https://github.com/leanprover/lean4/pull/14357)
  introduces stateful linters, which allow linters to persist and share state across command elaboration.

- [#14418](https://github.com/leanprover/lean4/pull/14418)
  changes the behaviour of `checkUnivs` linter to take all declarations and constructors (if dealing with an inductive type) when calculating universes that do not appear on their own.

- [#14437](https://github.com/leanprover/lean4/pull/14437)
  fixes `inferInstanceAs` marking its wrapper auxiliary definitions `@[expose]` even when their bodies are well-typed only in the private scope, which made instances defined via `inferInstanceAs` for types without an exposed body publicly ill-typed.

- [#14386](https://github.com/leanprover/lean4/pull/14386)
  is a follow-up to #14352 (introducing `postprocess_traces`). It provides a new command `store_traces_as myTraces in cmd` that runs the command `cmd` and stores its traces in-memory under the name `name`. The stored traces can be transformed and viewed using `#postprocess_traces tracePostprocessor myTraces`.

- [#14397](https://github.com/leanprover/lean4/pull/14397)
  makes the `set_option ... in` tactic support incremental elaboration, so edits inside its tactic block reuse the results of unchanged leading tactics instead of re-running the whole block.

- [#14387](https://github.com/leanprover/lean4/pull/14387)
  changes the level at which `logLintExt` data is persisted to `server`. Previously, it was all persisted at `public` level, thus causing negative performance regression.

````

# Library

````markdown

- [#14728](https://github.com/leanprover/lean4/pull/14728)
  makes `Expr.getUsedConstants` collect the `typeName` field of `Expr.proj` so we get a full list of constants that are directly used.

- [#14699](https://github.com/leanprover/lean4/pull/14699)
  changes the statement of the theorem `Nat.div_lt_div_right`, whose conclusion is `b / a < c / a ↔ b < c`, to not require `a ∣ b` as an assumption.

- [#14726](https://github.com/leanprover/lean4/pull/14726)
  weakens the hypothesis of `List.dropLast_take` from `i < l.length` to `i ≤ l.length`.

- [#14507](https://github.com/leanprover/lean4/pull/14507)
  generalizes the termination measures of `vcgen`'s `while` loop specifications. A measure may map into any type with a `WellFoundedRelation` instance and may read monadic state:

  ```lean
  case inv2 => exact .ofMeasure fun i => i            -- Nat measure
  case inv2 => exact .ofMeasure fun (i, j) => (i, j)  -- lexicographic
  case inv2 => exact .ofMeasure fun _ s => n - s      -- reads the monadic state
  ```

- [#14707](https://github.com/leanprover/lean4/pull/14707)
  adds missing `cbv_eval` annotations to `ofList`/`ofArray`, `get!`, `getD`, `insert` operations on `HashMap`/`HashSet`.

- [#14687](https://github.com/leanprover/lean4/pull/14687)
  fixes a use after free in `String.Pos.Raw.extract` when calling it with gigantic slice
  limits.

- [#14623](https://github.com/leanprover/lean4/pull/14623)
  generalizes the `MonadTail (StateT σ m)` instance to work without needing `Nonempty σ`. This means that proving specifications about `while` with a `StateT` monad now works even if there is no `Nonempty` instance for the state type.

- [#14268](https://github.com/leanprover/lean4/pull/14268)
  adds a HTTP Server benchmark

- [#14541](https://github.com/leanprover/lean4/pull/14541)
  fixes a possible time-sensitive overwrite of the known size by the `Builder.stream` functions.

- [#14571](https://github.com/leanprover/lean4/pull/14571)
  deflakes an HTTP unknown-size stream test. In some specific scenarios, it can fail because `tryRecv?` runs in the interval between sending the response header and when `"aaa"` is sent.

- [#14588](https://github.com/leanprover/lean4/pull/14588)
  turns `cond_eq_ite` into a `simp` lemma.

- [#14538](https://github.com/leanprover/lean4/pull/14538)
  moves `eq_false_of_ne_true` into the `Bool` namespace to be consistent with all other `Bool` functions, and moves `Bool.and'` (a `grind` helper function) to `Internal.Bool.and'`.

- [#14501](https://github.com/leanprover/lean4/pull/14501)
  establishes `dite` and `ite` as the recommended spelling for the `dif` and `if` syntax.

- [#14168](https://github.com/leanprover/lean4/pull/14168)
  lets a Hoare `Triple` use an assertion type `Pred` at a universe independent of the program's value type, so specifications can quantify over assertions like `σ → Prop` while values stay at `Type 0`, and `vcgen` reasons over such specifications directly.

- [#14523](https://github.com/leanprover/lean4/pull/14523)
  deprecates the `letFun` function, which went out of use in #9086 a year ago.

- [#14062](https://github.com/leanprover/lean4/pull/14062)
  makes the HTTP/1.1 client correctly finish reading responses that carry no body (head responses)

- [#14059](https://github.com/leanprover/lean4/pull/14059)
  adds `closeWithError` that enables the body stream to fail.

- [#13901](https://github.com/leanprover/lean4/pull/13901)
  adds a `RedirectPlan` type that uses the RFC9110 logic to validate redirect responses and automatically redirect.

- [#14253](https://github.com/leanprover/lean4/pull/14253)
  makes `Selectable.one` and other related functions handle errors and simplify them by using a `Selector` on `one` and `combine`.

- [#14502](https://github.com/leanprover/lean4/pull/14502)
  scopes `Lean.Order.instCCPO_std` into `Std.Internal.Do` so Hoare triple notation (which defaults the exception postcondition to `⊥`) elaborates after `open Std.Internal.Do` without also requiring `open Lean.Order`.

- [#12166](https://github.com/leanprover/lean4/pull/12166)
  removes the dependency of `pairwise_iff_getElem` on `Init.Data.List.Nat.TakeDrop` and implements `nodup_iff_getElem_inj`.

- [#14495](https://github.com/leanprover/lean4/pull/14495)
  redefines `IntN.toFloat` and `Float.ofIntN` (and the corresponding `Float32` and `ISize` functions) in terms of `Float.Model` and `Float32.Model`. The model already existed but was not used because of an oversight.

- [#13900](https://github.com/leanprover/lean4/pull/13900)
  adds a `Replayable` type class that is useful for checking if some `Body` can be replayed in a redirect request.

- [#14481](https://github.com/leanprover/lean4/pull/14481)
  improves the API surrounding `Float` / `Float.Model` / `Float32` / `Float32.Model` / `UnpackedFloat` in the following ways:
  - The declarations `Float.nan` / `Float.inf` / `Float32.nan` / `Float32.inf` and their corresponding models `Float.Model.nan` / `Float.Model.inf` / `Float32.Model.nan` / `Float32.Model.inf` are added (upstreamed from batteries, if you will).
  - The abbreviations `Int.toFloat` and `Int.toFloat32` are added, analogous to the existing `Nat.toFloat` and `Nat.toFloat32`.
  - `Float.Model.Format` now requires `2 ≤ exponentBits` instead of just `0 < exponentBits`; which is a necessary condition for `pack` and `unpack` to behave correctly
  - The definitions `Float.ofNat` / `Float.ofInt` / `Float32.ofNat` / `Float32.ofInt` are now exposed.
  - The type `Float.Model.UnpackedFloat.Sign` now has `deriving DecidableEq` instead of just `deriving BEq`.
  - The definitions for `unpackMantissa` / `unpackExponent` / `unpackSign` now use `BitVec.extractLsb'` instead of `BitVec.extractLsb`

- [#14462](https://github.com/leanprover/lean4/pull/14462)
  renames `Nat.div_eq` to `Nat.div_eq_ite` and `Nat.mod_eq` to `Nat.mod_eq_ite`.

- [#14458](https://github.com/leanprover/lean4/pull/14458)
  adds somme lemmas about `Nat.nextPowerOfTwo`.

- [#14412](https://github.com/leanprover/lean4/pull/14412)
  deprecates and removes the unused parameter `s : ε` from `ExceptCpsT.runK`.

- [#14294](https://github.com/leanprover/lean4/pull/14294)
  makes `String.toList` semireducible because unfolding it throws the definitional equality checker deep into the weeds of its internal implementation.

````

# Tactics

```markdown

- [#14713](https://github.com/leanprover/lean4/pull/14713)
  adds support for `bv_decide` to make use of the `grind` state when used in `sym`/`grind` interactive mode. `bv_decide` now picks up on the (relevant) equivalence classes, encodes them into the SAT problem and then handles the problem as normally.

- [#14709](https://github.com/leanprover/lean4/pull/14709)
  ensures beta-reduction is applied when canonicalizing types in `grind`.

- [#14694](https://github.com/leanprover/lean4/pull/14694)
  ensures assigned metavariables are properly handled in the `SymM` discrimination tree module.

- [#14691](https://github.com/leanprover/lean4/pull/14691)
  ensures that the `SymM` matcher/unifier does not get confused by `Expr.mdata`.

- [#14683](https://github.com/leanprover/lean4/pull/14683)
  makes `bv_decide`'s embedded constraints pass understand both `a = true` and `(!a) = true` correctly. This allows us to solve slightly more problems in pre-processing.

- [#14681](https://github.com/leanprover/lean4/pull/14681)
  adds support for restricting the set of complex types that `bv_decide` is going to analyze as a user. By default `bv_decide` guesses that enums and structures in its context might be relevant and tries to incorporate them into the solving process. Now users can supply a restricted set of types via `bv_decide types [MyEnum, MyStruct]`. `bv_decide` is only going to work these types and disable automated discovery once this option is passed.

- [#14672](https://github.com/leanprover/lean4/pull/14672)
  makes `bv_decide` available from within `sym =>` mode.

- [#14669](https://github.com/leanprover/lean4/pull/14669)
  makes `vcgen` try the `@[spec]` theorems matching a program in priority order and apply the first one that fits the goal, so a spec whose instance argument the call site cannot synthesize no longer shadows a more specific one.

- [#14215](https://github.com/leanprover/lean4/pull/14215)
  ports `bv_decide`'s pre-processor to `SymM`. For large, rewriting heavy problems we observe a performance win of up to 6x. Furthermore, it fixes the asymptotics of embedded constraint substitution to be linear in the size of all hypotheses. There are also some breaking changes included:
  - `bv_normalize`'s proving power got slightly changed (both positively and negatively)
  - `@[bv_normalize]` is now a `Sym.simp` set which comes with some differences in terms of pattern matching power and required shape of the theorem.

- [#14664](https://github.com/leanprover/lean4/pull/14664)
  fixes a bug in `mkTheoremFromDecl` in `SymM`. It did not correctly handled polymorphic theorems that require adapters.

- [#14529](https://github.com/leanprover/lean4/pull/14529)
  reworks how a `@[frameproc]` procedure discharges its split verification condition so that frame inference scales to operators whose residual the built-in lattice split cannot decompose. A procedure for separating conjunction `∗` used to leave behind a `∗` that no split rule could discharge, halting `vcgen`; a procedure may now discharge its split VC however it wants, so separation-logic framing closes with `vcgen … with finish`.

- [#14535](https://github.com/leanprover/lean4/pull/14535)
  fixes `vcgen [f, h, …]` reporting `No spec found` for a sibling call inside a self-recursive `f` when the list both brackets `f` to unfold and supplies a spec `h` for `f`, whether `h` is named or pulled by `*`. A bracketed definition's unfoldings now rank below both a named spec and a `*` hypothesis for the same program, so at a recursive call `vcgen` applies that spec and stops rather than unfolding `f` again into a branch whose sibling call has no matching spec. The regression came from #14528, which had raised these unfoldings to the named-spec priority.

- [#14530](https://github.com/leanprover/lean4/pull/14530)
  fixes a panic in `vcgen` when an equation or unfold spec supplied via `vcgen [someDef]` is used for a program in a deep embedding, i.e. a program type with a bare `Std.Internal.Do.WP` instance rather than a monadic one.

- [#14528](https://github.com/leanprover/lean4/pull/14528)
  makes every `vcgen [f]` argument enter the spec database at the call-site priority band, so a definition to unfold or a spec supplied as a term outranks an ambient `@[spec]` on the same program.

- [#14524](https://github.com/leanprover/lean4/pull/14524)
  fixes `vcgen … with finish` on a provably unreachable `match` branch: it no longer reports success while leaving an unassigned metavariable that the kernel rejects (`declaration has metavariables`), nor fails with `finish failed` on a verification condition whose proof needs a lifted precondition.

- [#14492](https://github.com/leanprover/lean4/pull/14492)
  makes `vcgen` prefer a spec named in a `vcgen [...]` argument over one collected from an ambient local hypothesis, and prefer `foo` over a hypothesis pulled in by `*` in `vcgen [foo, *]`, so the spec you supply at a call site wins when several match.

- [#14497](https://github.com/leanprover/lean4/pull/14497)
  teaches `vcgen` to decompose a raw `∀`/`→` on the RHS of a `Prop` entailment and an `iInf` on any `Pi` assertion lattice.

- [#14490](https://github.com/leanprover/lean4/pull/14490)
  makes `vcgen` report a clean missing-spec error when the spec it selects for a program turns out not to unify with it, instead of dumping the internal backward rule and its type.

- [#14487](https://github.com/leanprover/lean4/pull/14487)
  lets `vcgen [...]` accept arbitrary term arguments, not just bare identifiers, mirroring `simp [...]`. A term that proves a Hoare-triple or `⊑ wp` specification is registered as a spec, and any other term proof is handled as a simp lemma, so forms like `vcgen [show l = r from h]`, `vcgen [foo x]`, and `vcgen [@foo]` now work.

- [#14429](https://github.com/leanprover/lean4/pull/14429)
  makes `vcgen [f]` handle a definition `f` whose body is a `match` on its arguments like `simp [f]` does. A call with an opaque discriminant now rewrites through the unfold theorem `f.eq_def` and splits the exposed `match`, instead of reporting a missing spec.

- [#14475](https://github.com/leanprover/lean4/pull/14475)
  fixes a spurious "Too many variable names provided" error from `fun_induction` (and `induction`/`cases`) when an alternative had a `let`-bound field, so that all hypotheses of such an alternative can now be named.

- [#14469](https://github.com/leanprover/lean4/pull/14469)
  makes `vcgen` work after a preceding tactic `have`, `let`, or `suffices`, which previously failed with "vcgen: could not determine the program type of the goal".

- [#14468](https://github.com/leanprover/lean4/pull/14468)
  migrates the standard library to the `[grind hom]` and `[grind hom_pred]` attribute modifiers and removes the deprecated `[grind homo]` and `[grind homo_pred]` spellings.

- [#14460](https://github.com/leanprover/lean4/pull/14460)
  adds additional `BitVec` operations to the set of operations supported by `Simp.Simp.evalGround` and `Sym.DSimp.evalGround`.

- [#14459](https://github.com/leanprover/lean4/pull/14459)
  adds an option for `Sym.dsimp` to rewrite in instances. This is usually not desirable as it can lead to non-standard instances. However, we might for example want to rewrite ground terms in instances to make more terms syntactically equal.

- [#14464](https://github.com/leanprover/lean4/pull/14464)
  renames the `[grind homo]` and `[grind homo_pred]` attribute modifiers to `[grind hom]` and `[grind hom_pred]`. The previous spellings remain as deprecated aliases with identical behavior, and will be removed once the standard library migrates to the new spellings in a follow-up PR.

- [#14457](https://github.com/leanprover/lean4/pull/14457)
  records the homomorphism source types of a `[grind homo]` theorem set: when an `=`-injection rule (a rule translating `Eq τ`) is registered, the head constant of `τ` is added to a new environment extension, and rules whose source type is not headed by a constant are rejected. The source types identify the terms the `grind` homomorphism engine must track in the E-graph. The `reset_grind_attrs%` command clears the new extension.

- [#14454](https://github.com/leanprover/lean4/pull/14454)
  annotates theorems for `BitVec`, `Fin`, and fixed (signed and unsigned) integers using then new  `[grind homo]` and `[grind homo_pred]` attributes. This PR is based on the prototype implemented by Andres Erbsen at https://github.com/AeneasVerif/kraken/pull/122

- [#14452](https://github.com/leanprover/lean4/pull/14452)
  rejects `[grind homo]` theorems that are conditional rewriting rules. Conditional theorems are rejected with an error pointing to the E-matching attributes. The `reset_grind_attrs%` command now also clears the `[grind homo]` and `[grind homo_pred]` extensions.

- [#14451](https://github.com/leanprover/lean4/pull/14451)
  adds the attribute `[grind homo_pred]`. This attribute is used for a separate mechanism which complements `[grind homo]`. It is not a rewrite set but an eager fact injector keyed by head symbol. Where `[grind homo]`` rules translate terms, `[grind homo_pred]` theorems generate new facts about terms the moment they enter the E-graph.

- [#14446](https://github.com/leanprover/lean4/pull/14446)
  adds the attribute `[grind homo]`. This is just the first step. We are going to use it to implement the approach described at
  https://hackmd.io/Qd0nkWdzQImVe7TDGSAGbA

- [#14444](https://github.com/leanprover/lean4/pull/14444)
  ensures `grind` doesn't timeout checking for definitionally equality while trying to propagate `match`-expressions conditions.

- [#14439](https://github.com/leanprover/lean4/pull/14439)
  fixes a `grind` bug where the canonicalizer could resynthesize a propositional instance (e.g. `Nonempty α`) occurring in a binder body skipped by preprocessing, producing a closed nested proof lacking the `Grind.nestedProof` wrapper. Congruence closure then treated the term as distinct from correctly wrapped occurrences of the same application, and `grind` missed valid contradictions. Closes #13655.

- [#14431](https://github.com/leanprover/lean4/pull/14431)
  fixes `vcgen` failing with `Failed to apply rule` when the same equality spec matches two different programs within one run, e.g. the equations of a recursive function registered via `vcgen [f]`: the cached backward rule was specialized to the first matched program and could not be applied to the next one.

- [#14428](https://github.com/leanprover/lean4/pull/14428)
  fixes the `grind` filter syntax. It prevented `grind =>` from being used nested in `match` expressions.

- [#14426](https://github.com/leanprover/lean4/pull/14426)
  fixes `grind` dropping E-matching theorems from custom `grind` attributes when a partially activated theorem was reinserted under the same symbol.

- [#14425](https://github.com/leanprover/lean4/pull/14425)
  implements support for using `grind` to discharge hypotheses in conditional `Sym.simp` theorems.

- [#14424](https://github.com/leanprover/lean4/pull/14424)
  fixes a maximal-sharing violation in `Sym.simp`: when a conditional rewrite discharged a hypothesis that occurs in the theorem's right-hand side., the discharger-provided proof was spliced into the resulting term without restoring maximal sharing, violating the `SymM` sharing invariant (detected by `sym.debug`). Dischargers are not required to return maximally shared proofs. This issue was reported by @hargoniX

- [#14416](https://github.com/leanprover/lean4/pull/14416)
  fixes `vcgen` and `mvcgen` failing to split `match h : e with ...` expressions, whose alternatives bind an equality `h : e = pattern`. Fixes #12275.

- [#14405](https://github.com/leanprover/lean4/pull/14405)
  improves the support for offsets in `SymM` matcher/unifier. See new test for example that could not be handled.

- [#13587](https://github.com/leanprover/lean4/pull/13587)
  fixes a kernel type mismatch raised by `lia`/`grind` when internalizing an integer expression whose syntactic structure differs from the structure of its polynomial representation. The mismatch occurred because the `eq_def` proof term bridged `x.denote ctx = e.denote ctx` to `Poly.denote' ctx p = 0` via a plain `Eq.refl e`, but `Poly.denote'` collapses sub-structure such as a trailing `+ 0` (the `(.num 0)` monomial is dropped) while `e` keeps it. The kernel then rejected the application because the equality between `x.denote` and `Poly.denote' p` did not hold definitionally.

- [#14404](https://github.com/leanprover/lean4/pull/14404)
  fixes `Sym.simp` failing to rewrite terms containing unassigned metavariables, and prevents the matcher from unsoundly unifying such metavariables when matching nonlinear patterns.

- [#14401](https://github.com/leanprover/lean4/pull/14401)
  fixes `preprocessType` in `SymM`. It must not perform `zetaDelta` by default.

```

# Compiler

```markdown

- [#14717](https://github.com/leanprover/lean4/pull/14717)
  the model/runtime mismatch in `String.Pos.Raw.extract` and adds a faster variant (`lean_string_utf8_extract_fast`) for `String.extract` that assumes that the positions are valid positions.

- [#14505](https://github.com/leanprover/lean4/pull/14505)
  fixes a compiler issue where private imports of the `Lean` library could lead to segfaults by ensuring the necessary call to `lean_initialize` happens in each module's initializer when necessary. As a follow-up clean up, the call to `lean_initialize_runtime_module` is made implicit as well, meaning users of Lean as an FFI library do not need to call these functions themselves anymore.

- [#14332](https://github.com/leanprover/lean4/pull/14332)
  adds `DT_SONAME` entries to the shared libraries `libInit_shared, libleanshared*, libLake_shared` on Linux. This is analogous to `LC_ID_DYLIB` on Mac which we already set via `-install_name`. Fixes #9420.

- [#14479](https://github.com/leanprover/lean4/pull/14479)
  prevents possible corruption if two threads simultaneously call `lean_decode_io_error`. It also changes the semantics of `osCode` in `IO.Error`, such that it emulates posix `errno` rather than forwarding uv error codes cast to unsigned integers.

- [#14471](https://github.com/leanprover/lean4/pull/14471)
  fixes a sanitizer warning where `initialize` functions were passed uninitialized memory as their `world` argument, by failing to call `io_mk_world`.

- [#14463](https://github.com/leanprover/lean4/pull/14463)
  reverts #14423 until we can get the situation on Windows figured out.

- [#14423](https://github.com/leanprover/lean4/pull/14423)
  prevents possible corruption if two threads simultaneously call `lean_decode_io_error`. It also changes the semantics of `osCode` in `IO.Error`, such that it emulates posix `errno` rather than forwarding uv error codes cast to unsigned integers.

- [#14204](https://github.com/leanprover/lean4/pull/14204)
  prevents silent olean truncation when disk space is exhausted.

```

# Pretty Printing

```markdown

- [#14512](https://github.com/leanprover/lean4/pull/14512)
  makes a `for` do-element pretty-print with a space before `do`. The do-element `for` parser emitted `"do "` with no leading space, so reformatting a `for … do` block glued the range to the keyword (`for x in xs do` printed as `for x in xsdo`). Every sibling do-keyword (`while`, `unless`, term-level `for`) already emits ` do `; this aligns `for`.

- [#14367](https://github.com/leanprover/lean4/pull/14367)
  fixes an issue where the `@[simp ←]` attribute would pretty-print as `@[simp← ]`, along with analogous issues with `@[grind norm ←]`, `@[wf_preprocess ←]`, `@[bv_normalize ←]`, etc. See also discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Whitespace.20linter.20interaction.20with.20reverse.20simp.20attributes/near/590971428).

```

# Documentation

```markdown

- [#14436](https://github.com/leanprover/lean4/pull/14436)
  removes references to the unfolding lemma from the `repeatM` docstrings and moves that lemma into the `repeatM.Internal` namespace.

```

# Lake

```markdown

- [#14723](https://github.com/leanprover/lean4/pull/14723)
  makes the `MACOSX_DEPLOYMENT_TARGET` configurable via the Lake API -- both across a build and for custom builds of shared libraries or executables.  It also includes the target in traces, ensuring a rebuilding if the value changes (e.g., if the environment variable `MACOSX_DEPLOYMENT_TARGET` is set).

- [#14724](https://github.com/leanprover/lean4/pull/14724)
  adds the `--package` option for `lake cache get`, which fetches outputs for a specific package in the workspace (not just the root). This is particularly useful for downloading dependency outputs from a custom service. In addition, the undocumented `--rev` support has been removed from `put` and documented for `put-staged`.

- [#14720](https://github.com/leanprover/lean4/pull/14720)
  demotes all cache-related failures during a build to `trace`-level messages. This ensures that builds run with `--wfail` or `--iofail` do not fail solely due to the cache.

- [#14622](https://github.com/leanprover/lean4/pull/14622)
  adds a `--code-quality` option to `lake lint` that emits builtin linter results as machine-readable JSON entries instead of human-readable diagnostics. Text-linter warnings are aggregated per module and linter into one entry holding the warning count, and environment-linter findings are reported per flagged declaration; both are keyed by the linter's option name. The option implies `--builtin-lint` and `--builtin-only`.

- [#14617](https://github.com/leanprover/lean4/pull/14617)
  refactors `lake lint --builtin-lint` internals so that it has a `Mode` flag (reporting vs recording exceptions) in the anticipation of the third mode of running upcoming code quality checks.

- [#14629](https://github.com/leanprover/lean4/pull/14629)
  suppresses Lake's wrapper line `error: Lean exited with code 1` when `lean` has already emitted error-level diagnostics and exited with code 1, which is the usual type-error path and was pure noise next to the real errors.

- [#14625](https://github.com/leanprover/lean4/pull/14625)
  makes Lake report the underlying file error when a `lean_lib` root module has no source file, instead of only reporting that some modules have bad imports.

- [#14651](https://github.com/leanprover/lean4/pull/14651)
  fixes a number of ways a failed artifact transfer in `lake cache get` / `lake cache put` could fail to be recorded or could lead to an early abort of the entire transfer batch. Sometimes this would leave a corrupted artifact in the local Lake cache, which could break downstream builds.

- [#14630](https://github.com/leanprover/lean4/pull/14630)
  makes `lake update <pkg>...` fail with a clear error when a specified package name is not known to the current dependency manifest. Previously, unknown or misspelled names (including case mismatches) were silently ignored, which was confusing.

```

# Other

```markdown

- [#14161](https://github.com/leanprover/lean4/pull/14161)
  adds support for compiling with thread sanitizer. This both increases memory consumption and slows lean down massively so we only run a very small subset of tests to remain in a reasonable time. Developers need to add additional tests to the set themselves.

```
