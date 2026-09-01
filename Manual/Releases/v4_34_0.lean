/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Lean.MessageSeverity

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.34.0-rc2 (2026-08-21)" =>
%%%
tag := "release-v4.34.0"
file := "v4.34.0"
%%%

:::warn
These release notes describe a _release candidate_, not the final release.
They may be incomplete and are subject to change.
:::

For this release, 156 changes landed.
In addition to the 55 feature additions
and 61 fixes listed below,
there were 5 refactoring changes,
5 documentation improvements,
6 performance improvements,
2 improvements to the test suite,
and 22 other changes.

# Highlights

The kernel is the headline of this release: three routes to a proof of `False`, all surfaced by adversarial testing with AI systems, are closed, and a round of defensive checks and resource bounds follows them.
In the automation, {tactic}`bv_decide` gets a preprocessor that is up to six times faster and can now be run inside {tactic}`grind`'s interactive mode, where it inherits everything {tactic}`grind` has already learned.
Linters can carry state across commands and attach code actions to their warnings, and Lake improves its linting, caching, and error reporting.

`vcgen` also saw substantial work and is slated for release in v4.35.0, with the new *intrinsic verification* feature it underpins, where a `def` carries its own contract, following in some future release.

_This highlights section was contributed by Juanjo Madrigal._

## Kernel Soundness and Hardening

Continuing the kernel work of v4.33.0, this release closes three routes to a proof of `False` — two in the kernel proper and one in the runtime's reference counting — and adds a round of defensive checks on top.
All three were reported by Daniel Selsam (OpenAI) using their internal models, and all three need a deliberately constructed input rather than ordinary source code: they matter when checking proofs that arrive from an untrusted source, not for a development that only elaborates its own code.

* [#14806](https://github.com/leanprover/lean4/pull/14806) makes `is_def_eq` caching order-independent.
  The kernel cached successful queries in a union-find structure; since the implemented test is sound but incomplete, and therefore not transitive, the transitive closure that union-find computes made a query's answer depend on which queries had been asked before.
  A crafted input used this to build a recursor whose type and computation rule disagreed, and derive `False`.
  The union-find is replaced by a plain cache keyed on the query pair, so the answer is again a function of the two arguments.
  An OpenAI agent went on to produce two distinct exploits from the issue; both are caught by `nanoda` and by the new `lean-inductive-models`.

* [#14807](https://github.com/leanprover/lean4/pull/14807) makes the kernel's `is_prop` require a sort.
  When a term's inferred type was stuck rather than reducible to a sort, `is_prop` answered `false` instead of rejecting the term, which skipped the proof-irrelevance guard on projections and allowed a data field to be projected out of a value used as a `Prop`.
  The bogus proof was also accepted by `nanoda`; `lean4lean` is believed not to have the bug.
  [#14843](https://github.com/leanprover/lean4/pull/14843) applies the same fix to a copy of the old check inlined in `inductive.h`.

* [#14838](https://github.com/leanprover/lean4/pull/14838) freezes objects whose 32-bit reference count overflows, following the sticky-counter approach used by Koka.
  Forcing the counter to wrap corrupted the object's state, and on machines with at least 18GB of free RAM this could be turned into a use-after-free in the official kernel and extended into a proof of `False`.
  Kernels not built on the Lean runtime were unaffected.

The rest of the section is hardening rather than bug fixing:

* [#14808](https://github.com/leanprover/lean4/pull/14808) type-checks the recursors the kernel generates for an inductive type, and checks that each computation rule is type-preserving rather than merely well-typed.
  A minor premise that expects an induction hypothesis the rule does not supply reduces to an under-applied function, which is still well-typed but no longer has the recursor's result type — so checking that the right-hand side has *some* type would not catch it.
  This is defense in depth: it rejects only declarations that were already malformed.

* [#14582](https://github.com/leanprover/lean4/pull/14582) makes the kernel reject inductive declarations in which a datatype being declared occurs applied to anything other than the declaration's parameters and universe levels.
  The frontend already enforced this, so only declarations built with `addDecl` directly are affected.

* [#14849](https://github.com/leanprover/lean4/pull/14849) bounds the size of `Nat` numerals the kernel computes at 128 MB, so a compact proof can no longer direct it to evaluate a numeral of many gigabytes.
  Workloads that legitimately need larger numerals can raise the limit with the `LEAN_NAT_MAX_SIZE` environment variable.

* [#14833](https://github.com/leanprover/lean4/pull/14833) makes Lean require GMP 6.3.0 or newer, since earlier versions contain bugs that can make Lean produce unsound results in corner cases.
  Building against an older GMP now fails at configuration time; `-DUSE_GMP=OFF` (Lean's own bignum implementation) and `-DFORCE_GMP=ON` are the two escape hatches.

## `bv_decide` Is Faster and Cooperates with `grind`

### Bit-blasting Inside `grind =>`

[#14672](https://github.com/leanprover/lean4/pull/14672) makes {tactic}`bv_decide` available from within `sym =>` mode, and [#14713](https://github.com/leanprover/lean4/pull/14713) connects it to the {tactic}`grind` state: the relevant equivalence classes are encoded into the SAT problem alongside the goal, as are facts learned by theory solvers and by E-matching.

```imports -show
import Std.Tactic.BVDecide
```

```lean
opaque g : UInt8 → UInt8

example (a b d : UInt8) (h0 : d = a ||| b)
    (h1 : g d &&& 0xC0 = 0) :
    g (a ||| b) &&& 0x40 = 0 := by
  grind =>
    bv_decide
```

On its own, {tactic}`bv_decide` abstracts `g d` and `g (a ||| b)` as two unrelated opaque variables and reports a spurious counterexample.
Inside `grind =>`, congruence closure has already merged them using `h0`, so the SAT problem it hands to the solver is the one that actually needs solving.

### Choosing Which Types Get Analyzed

By default {tactic}`bv_decide` guesses which structures and enum inductives in the context might matter and tries to incorporate them.
[#14681](https://github.com/leanprover/lean4/pull/14681) adds a `types [...]` clause that names them explicitly and turns the automatic discovery off, which keeps preprocessing tractable on goals mentioning many types of which only a few are relevant:

```lean
inductive Color where
  | red | green | blue

@[ext] structure Pair where
  x : BitVec 8
  y : BitVec 8

example (a b : Pair) (c d : Color) (h1 : a = b) (h2 : c = d) :
    a.x = b.x ∧ d = c := by
  bv_decide types [Pair, Color]
```

Pinning is a restriction rather than a hint: everything not listed is treated as an opaque variable, so naming the wrong type leaves the goal outside the supported fragment.
A type that is neither a non-recursive structure nor an enum inductive is rejected outright.
The clause is accepted by {tactic}`bv_normalize`, `bv_decide?`, and `bv_check` as well, and inside `sym =>`.

Note the `@[ext]` above: {tactic}`bv_decide` takes a structure equality apart through the structure's extensionality lemma, so a structure without one stays opaque whether or not it is listed.

### A Faster Preprocessor

[#14215](https://github.com/leanprover/lean4/pull/14215) ports {tactic}`bv_decide`'s preprocessor to `SymM`, the rewriting engine shared with {tactic}`grind` and {tactic}`cbv`.
On large, rewriting-heavy problems this is a speedup of up to 6x, and substitution of embedded constraints becomes linear in the total size of the hypotheses.
*Breaking change:* `@[bv_normalize]` is now a `Sym.simp` set, which differs in pattern-matching power and in the shape it requires of a theorem, and {tactic}`bv_normalize`'s proving power shifts slightly in both directions.

Smaller improvements round this out: [#14683](https://github.com/leanprover/lean4/pull/14683) teaches the embedded-constraints pass to read both `a = true` and `(!a) = true`, and [#14460](https://github.com/leanprover/lean4/pull/14460) extends ground evaluation to more {name}`BitVec` operations.
Elsewhere in the same engine, [#14425](https://github.com/leanprover/lean4/pull/14425) lets {tactic}`grind` discharge the side conditions of conditional `Sym.simp` theorems, and [#14459](https://github.com/leanprover/lean4/pull/14459) adds an option for `Sym.dsimp` to rewrite inside instances, which can make more ground terms syntactically equal.

`SymM` also collects a batch of correctness fixes: the matcher no longer unifies metavariables unsoundly when matching nonlinear patterns ([#14404](https://github.com/leanprover/lean4/pull/14404)), {tactic}`grind` no longer drops E-matching theorems from custom attributes ([#14426](https://github.com/leanprover/lean4/pull/14426)) or misses a valid contradiction because the canonicalizer resynthesized an instance inside a skipped binder ([#14439](https://github.com/leanprover/lean4/pull/14439)), and `lia`/{tactic}`grind` no longer emit a proof the kernel rejects when an integer expression's structure differs from that of its polynomial representation ([#13587](https://github.com/leanprover/lean4/pull/13587)).
Further fixes: [#14401](https://github.com/leanprover/lean4/pull/14401), [#14405](https://github.com/leanprover/lean4/pull/14405), [#14424](https://github.com/leanprover/lean4/pull/14424), [#14428](https://github.com/leanprover/lean4/pull/14428), [#14444](https://github.com/leanprover/lean4/pull/14444), [#14664](https://github.com/leanprover/lean4/pull/14664), [#14691](https://github.com/leanprover/lean4/pull/14691), [#14694](https://github.com/leanprover/lean4/pull/14694), [#14709](https://github.com/leanprover/lean4/pull/14709).

## Linters and Deprecation Warnings

Two changes extend what a linter can do.
[#14357](https://github.com/leanprover/lean4/pull/14357) introduces *stateful* linters, which persist state across command elaboration and can read the state of other linters, in an early/late two-phase architecture registered from an `initialize` block.
[#14402](https://github.com/leanprover/lean4/pull/14402) lets linters produce code actions, so a linter warning can now carry a fix that is one click away in the editor.

Deprecation reporting, introduced in v4.31.0, got a round of polish.
[#14478](https://github.com/leanprover/lean4/pull/14478) moves option deprecation onto the `@[deprecated]` attribute, so a deprecated option warns both when it is used with `set_option` and when it is read from meta code:

```lean
open Lean in
@[deprecated "use `demo.newOpt` instead" (since := "2026-08-21")]
register_option demo.oldOpt : Bool :=
  { defValue := true, descr := "an old option" }
```

```lean (name := depOpt)
open Lean in
def readsOldOpt (o : Options) : Bool := demo.oldOpt.get o
```
```leanOutput depOpt (severity := warning)
`demo.oldOpt` has been deprecated: use `demo.newOpt` instead
```

[#14564](https://github.com/leanprover/lean4/pull/14564) re-parses the header so that each deprecated-module warning points at the `import` that actually pulls that module in, instead of collapsing every one of them onto the start of the header, and [#14533](https://github.com/leanprover/lean4/pull/14533) silences deprecated-syntax warnings inside definitions that are themselves deprecated — the same rule that already applied to deprecated constants:

```lean
syntax "oldThing" : term
macro_rules | `(oldThing) => `(42)
deprecated_syntax termOldThing "use `42` instead"
  (since := "2026-08-21")
```

```lean (name := depSyn)
def fresh : Nat := oldThing
```
```leanOutput depSyn (severity := warning)
syntax 'termOldThing' has been deprecated: use `42` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
```

A definition that is on its way out, though, is allowed to keep using the syntax that is on its way out with it, and stays quiet:

```lean
@[deprecated "use `fresh` instead" (since := "2026-08-21")]
def stale : Nat := oldThing
```

## Lake

[#14622](https://github.com/leanprover/lean4/pull/14622) adds a `--code-quality` mode to `lake lint` that emits builtin linter results as machine-readable JSON entries instead of human-readable diagnostics, each keyed by the linter's option name.
Text-linter warnings are aggregated per module and linter into a single entry holding the count; environment-linter findings are reported per flagged declaration.
The entries are data rather than failures, so `lake lint --code-quality` succeeds even when violations are found.
Two entries — one aggregated from a text linter, one from an environment linter (a fixture from Lake's own test suite) — look like this:

```
{"value":{"scalar":{"value":2}},
 "source":{"module":{"name":"Violations"}},
 "name":"linter.unusedVariables"}

{"value":{"scalar":{"value":1}},
 "source":{"declaration":{"name":"fooDummyMarker",
                          "module":"Violations"}},
 "name":"linter.dummyMarker"}
```

On the caching side, [#14720](https://github.com/leanprover/lean4/pull/14720) demotes cache failures during a build to `trace`-level messages, so a build run with `--wfail` or `--iofail` no longer fails because of the cache alone, and [#14651](https://github.com/leanprover/lean4/pull/14651) fixes several ways a failed artifact transfer could go unrecorded, abort a whole transfer batch, or leave a corrupted artifact behind.
[#14724](https://github.com/leanprover/lean4/pull/14724) adds `lake cache get --package`, which fetches the outputs of a specific package in the workspace rather than only the root.

Error reporting improves in three places: `error: Lean exited with code 1` is elided when `lean` has already printed the real diagnostics ([#14629](https://github.com/leanprover/lean4/pull/14629)), a `lean_lib` root module with no source file reports the underlying file error instead of a vague bad-imports message ([#14625](https://github.com/leanprover/lean4/pull/14625)), and `lake update <pkg>` now fails on a package name the manifest does not know instead of silently ignoring it ([#14630](https://github.com/leanprover/lean4/pull/14630)).
Finally, [#14723](https://github.com/leanprover/lean4/pull/14723) makes `MACOSX_DEPLOYMENT_TARGET` configurable through the Lake API and includes it in build traces.

## Performance and Robustness

[#14520](https://github.com/leanprover/lean4/pull/14520) fixes an exponential blowup in `instantiateMVars` on proof terms that repeatedly reference hypotheses introduced by `MVarId.assert`/`intro` — as `MVarId.note`, `replaceLocalDecl`, and `simp at h` do.
Lifting substituted values is now memoized and canonicalized across a whole pass, restoring linear behavior: the reproduction from [#14329](https://github.com/leanprover/lean4/issues/14329) went from exceeding 41GB to elaborating in about 1.2 seconds, and one Mathlib module dropped 26G instructions (-55%).

[#14397](https://github.com/leanprover/lean4/pull/14397) makes the `set_option ... in` tactic elaborate incrementally, so editing inside such a block reuses the results of the unchanged leading tactics instead of re-running the whole block.
For diagnosing where the time goes, [#14386](https://github.com/leanprover/lean4/pull/14386) adds `store_traces_as name in cmd`, which runs `cmd`, reports its trace as usual, and additionally keeps the trace tree in memory under `name`, together with `#postprocess_traces name post` for re-viewing that tree through any postprocessor.
Where `postprocess_traces` from v4.33.0 transformed a trace as it was produced, this separates producing from viewing — which matters when the command took a minute to run.

Two robustness fixes are worth knowing about: [#14204](https://github.com/leanprover/lean4/pull/14204) detects failures when flushing a module's `.olean`, so an exhausted disk no longer leaves a silently truncated file behind, and [#14687](https://github.com/leanprover/lean4/pull/14687) fixes a use-after-free in `String.Pos.Raw.extract` when it is called with gigantic slice limits.
[#14717](https://github.com/leanprover/lean4/pull/14717) fixes the same function's model/runtime mismatch and adds a fast path for {name}`String.extract` when the positions are known to be valid.

On the FFI side, [#14505](https://github.com/leanprover/lean4/pull/14505) fixes segfaults caused by private imports of the `Lean` library by making each module's initializer call `lean_initialize` when it needs to.
The call to `lean_initialize_runtime_module` became implicit in the same cleanup, so users of Lean as an FFI library no longer need to call either function themselves.

## Library Highlights

The floating-point work that landed in v4.33.0 continues.
[#14481](https://github.com/leanprover/lean4/pull/14481) upstreams {name}`Float.nan` and {name}`Float.inf` (with their `Float32` and model counterparts), adds {name}`Int.toFloat` and `Int.toFloat32` alongside the existing {name}`Nat.toFloat`, and exposes `Float.ofNat`/`Float.ofInt`; [#14495](https://github.com/leanprover/lean4/pull/14495) redefines the conversions between {name}`Float` and the fixed-width signed integers in terms of the logical model, which had been written but not connected.

```lean
/-- info: 42.000000 -/
#guard_msgs in
#eval (42 : Int).toFloat

/-- info: true -/
#guard_msgs in
#eval (1.0 / 0.0) == Float.inf
```

[#14788](https://github.com/leanprover/lean4/pull/14788) redefines {name}`Bool.and`, {name}`Bool.or`, and {name}`Bool.not` directly in terms of {name}`Bool.rec`, which the kernel reduces much faster than a `match`; the compiler, which does not support `Bool.rec`, is pointed back at the old definitions with `@[csimp]`, so generated code is unchanged.
The new shape is visible if you print one of them:

```lean (name := boolAnd)
#print Bool.and
```
```leanOutput boolAnd
@[implicit_reducible] def Bool.and : Bool → Bool → Bool :=
fun x y => Bool.rec false y x
```

It also retires the kernel-friendly duplicates {tactic}`grind` had been carrying for exactly this reason: `Bool.and'`, `Bool.or'`, and `Bool.not'` are now deprecated abbreviations for the real operations.

The HTTP client gains redirect support: [#13901](https://github.com/leanprover/lean4/pull/13901) adds `Std.Http.Protocol.H1.RedirectPlan`, which validates redirect responses following RFC 9110 and follows them automatically, and [#13900](https://github.com/leanprover/lean4/pull/13900) adds `Std.Http.Body.Replayable` for deciding whether a body can be replayed in the redirected request.
[#14062](https://github.com/leanprover/lean4/pull/14062) makes the HTTP/1.1 client finish reading responses that carry no body, and [#14059](https://github.com/leanprover/lean4/pull/14059) adds `closeWithError` so a body stream can fail.

Beyond that, the release is mostly incremental lemma work and naming cleanups; the naming changes are collected below.

## Breaking Changes

- [#14501](https://github.com/leanprover/lean4/pull/14501) establishes {name}`ite` and {name}`dite` as the spelling for the `if` and `dif` syntax in identifiers, and `left`/`right` as the markers for the two branches.
  Many lemmas are renamed accordingly; most visibly, `if_pos` and `if_neg` are now {name}`ite_eq_left` and {name}`ite_eq_right`, and `dif_pos`/`dif_neg` are {name}`dite_eq_left`/{name}`dite_eq_right`.
  *Migration:* the old names remain as deprecated aliases, so existing proofs keep working and the warnings point at the replacement.

- [#14462](https://github.com/leanprover/lean4/pull/14462) renames {name}`Nat.div_eq` to {name}`Nat.div_eq_ite` and {name}`Nat.mod_eq` to {name}`Nat.mod_eq_ite`, freeing `Nat.div_eq` for a lemma analogous to `Nat.add_eq`.
  Deprecated aliases are in place here too.

- [#14215](https://github.com/leanprover/lean4/pull/14215) turns `@[bv_normalize]` into a `Sym.simp` set, as described above.

- [#14391](https://github.com/leanprover/lean4/pull/14391) moves `Lean.Environment.replay` to `Lean.Kernel.Environment.replay`, so that replaying an environment produces a {name}`Lean.Kernel.Environment` and no longer goes through the unstable `Environment.ofKernelEnv`.
  Tools that replay environments — proof checkers and similar — need to follow the rename.
  *Migration:* the old name survives as a deprecated alias, and its warning spells out both the changed type and the fact that dot notation has to become `Kernel.Environment.replay x`.

- [#14523](https://github.com/leanprover/lean4/pull/14523) deprecates `letFun`, which went out of use a year ago; use `have` instead.

- [#14479](https://github.com/leanprover/lean4/pull/14479) changes the meaning of `osCode` in {name}`IO.Error` so that it emulates POSIX `errno` rather than forwarding libuv error codes cast to unsigned integers, while fixing a thread-safety bug in `lean_decode_io_error`.

- [#14538](https://github.com/leanprover/lean4/pull/14538) moves `eq_false_of_ne_true` into the {name}`Bool` namespace as {name}`Bool.eq_false_of_ne_true`, leaving a deprecated alias behind.

- [#14412](https://github.com/leanprover/lean4/pull/14412) removes the unused `s : ε` parameter from `ExceptCpsT.runK`.
  There is no alias for this one: call sites that passed the argument have to drop it.

- [#14294](https://github.com/leanprover/lean4/pull/14294) drops `@[implicit_reducible]` from {name}`String.toList`, making it semireducible, since unfolding it dragged the definitional equality checker deep into its internal implementation.
  Code that relied on {name}`String.toList` unfolding at implicit or reducible transparency — a defeq check, an instance, a {tactic}`simp` lemma whose statement is only well-typed after unfolding — now has to go through an explicit rewrite instead.

- [#14833](https://github.com/leanprover/lean4/pull/14833) and [#14849](https://github.com/leanprover/lean4/pull/14849), described above, affect anyone building Lean from source or computing very large numerals in the kernel.

# Language

````markdown

- [#14582](https://github.com/leanprover/lean4/pull/14582)
  makes the kernel reject inductive declarations in which a datatype being declared occurs applied to anything other than the parameters and universe levels of the declaration. Such non-uniform occurrences could previously hide in positions that escape the kernel's checks: behind a reduction that erases them, or in the parametric arguments of a nested occurrence, which are dropped from the auxiliary declaration the kernel generates and were therefore only checked for well-typedness.

- [#14826](https://github.com/leanprover/lean4/pull/14826)
  reports the intrinsic verification syntax as experimental wherever it is used: the `requires` and `ensures` contract clauses of a `def`, the `assert` element, and the `invariant` clause of a loop each report at their keyword. Setting `experimental.intrinsic` to `true` acknowledges the experimental status and silences the reports.

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

- [#14788](https://github.com/leanprover/lean4/pull/14788)
  changes `Bool.and`, `Bool.or`, `Bool.not` so that they are defined directly in terms of `Bool.rec` for better kernel performance.

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

````markdown

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

````

# Compiler

````markdown

- [#14838](https://github.com/leanprover/lean4/pull/14838)
  prevents memory corruption when an object's 32-bit reference count overflows. On machines with at least 18GB of free RAM, it could be used to trigger use-after-free in the official kernel, which could be extended into a proof of False. Other kernels such as nanoda not based on the Lean runtime were not affected.

- [#14791](https://github.com/leanprover/lean4/pull/14791)
  makes the compiler `macro_inline` results of `csimp` lemmas.

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

````

# Pretty Printing

````markdown

- [#14512](https://github.com/leanprover/lean4/pull/14512)
  makes a `for` do-element pretty-print with a space before `do`. The do-element `for` parser emitted `"do "` with no leading space, so reformatting a `for … do` block glued the range to the keyword (`for x in xs do` printed as `for x in xsdo`). Every sibling do-keyword (`while`, `unless`, term-level `for`) already emits ` do `; this aligns `for`.

- [#14367](https://github.com/leanprover/lean4/pull/14367)
  fixes an issue where the `@[simp ←]` attribute would pretty-print as `@[simp← ]`, along with analogous issues with `@[grind norm ←]`, `@[wf_preprocess ←]`, `@[bv_normalize ←]`, etc. See also discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Whitespace.20linter.20interaction.20with.20reverse.20simp.20attributes/near/590971428).

````

# Documentation

````markdown

- [#14436](https://github.com/leanprover/lean4/pull/14436)
  removes references to the unfolding lemma from the `repeatM` docstrings and moves that lemma into the `repeatM.Internal` namespace.

````

# Lake

````markdown

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

````

# Other

````markdown

- [#14833](https://github.com/leanprover/lean4/pull/14833)
  makes Lean require GMP 6.3.0 or newer and builds the official releases against GMP 6.3.0. Earlier GMP versions contain bugs that can cause Lean to produce unsound (i.e., incorrect) results in corner cases; independent kernels that do not depend on GMP will catch such unsoundness. The portable Linux releases were previously linked against GMP 6.1.2 (inherited from the old glibc nixpkgs used for portability).

- [#14849](https://github.com/leanprover/lean4/pull/14849)
  makes the kernel reject `Nat` literals and computations whose representation would exceed a configurable size limit (128 MB by default). This prevents pathological or adversarial inputs from driving the kernel to spend unbounded memory and time constructing enormous numerals, and keeps the kernel's arithmetic comfortably within the range where its arbitrary-precision integer backend is well exercised. The limit can be raised with the `LEAN_NAT_MAX_SIZE` environment variable for the rare workloads that legitimately compute very large numerals in the kernel.

- [#14847](https://github.com/leanprover/lean4/pull/14847)
  adds another test for the `is_prop` bug in the kernel.
  The exploit was submitted by Daniel Selsam (OpenAI) and was generated using OpenAI's internal models.

- [#14843](https://github.com/leanprover/lean4/pull/14843)
  applies the fix from #14807 to `inductive.h`. As the comment in `inductive.h` points out, the code should check whether `e_type` is a proposition using `is_prop`, but it was still inlining the old, buggy version of `is_prop`.

- [#14808](https://github.com/leanprover/lean4/pull/14808)
  adds a new defensive check to the kernel. When the kernel generates a recursor for an inductive type, it installs the recursor and its computation rules with `add_core`, which does not re-check them. It adds a verification pass that (1) type-checks each generated recursor's type and (2) checks that each computation rule is type-preserving: reducing the recursor applied to a constructor yields a term whose type is the recursor's declared result type. This catches a recursor whose minor-premise type and reduction rule disagree, for example a minor premise that expects an induction hypothesis while the rule omits it. Checking only that a rule's right-hand side has some type is not enough, because an under-applied minor premise is still a well-typed (function) term. The check is defense-in-depth: it does not change what the kernel accepts for well-formed inductives, and only rejects declarations that were already malformed.

- [#14807](https://github.com/leanprover/lean4/pull/14807)
  fixes a soundness issue. The kernel's `is_prop` decided whether a term is a proposition by taking the weak head normal form of its inferred type and checking that the result is syntactically `Sort 0`. When the inferred type did not reduce to a sort but was left as a stuck term, `is_prop` returned `false` instead of treating the term as ill-formed. This let the proof-irrelevance guard in projection inference be skipped, so a non-proof field could be projected out of a value used as a `Prop`, and `False` derived. The fix computes the inferred type with `ensure_sort`, which reduces it and requires the result to be a sort, raising `(kernel) type expected` otherwise. The bogus proof was also accepted by nanoda, an independent implementation of the Lean kernel. We believe the lean4lean external kernel does not have this bug.

- [#14806](https://github.com/leanprover/lean4/pull/14806)
  fixes a soundness issue in the kernel. The kernel cached successful `is_def_eq` queries in a union-find structure. Because the implemented `is_def_eq` is sound but incomplete, and therefore not transitive, the transitive closure computed by the union-find made a query's result depend on the order of earlier queries: `is_def_eq(v0, v2)` could return `false` on its own but `true` after `is_def_eq(v0, v1)` and `is_def_eq(v1, v2)` had succeeded. A crafted input used this to build a recursor whose type and computation rule disagreed, and derive `False`. The fix replaces the union-find with a plain cache keyed on the query pair, so `is_def_eq` is again a function of its two arguments. The issue was reported by Daniel Selsam (OpenAI) using their internal models. An OpenAI agent then produced two distinct exploits based on it. Both exploits are also caught by nanoda, and both are caught by the new lean-inductive-models developed by Joachim Breitner.

- [#14161](https://github.com/leanprover/lean4/pull/14161)
  adds support for compiling with thread sanitizer. This both increases memory consumption and slows lean down massively so we only run a very small subset of tests to remain in a reasonable time. Developers need to add additional tests to the set themselves.

````
