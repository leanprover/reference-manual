/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.16.0 (2025-02-03)" =>
%%%
tag := "release-v4.16.0"
file := "v4.16.0"
%%%

````markdown
## Highlights

### Unique `sorry`s

[#5757](https://github.com/leanprover/lean4/pull/5757) makes it harder to create "fake" theorems about definitions that
are stubbed-out with `sorry` by ensuring that each `sorry` is not
definitionally equal to any other. For example, this now fails:
```lean
example : (sorry : Nat) = sorry := rfl -- fails
```
However, this still succeeds, since the `sorry` is a single
indeterminate `Nat`:
```lean
def f (n : Nat) : Nat := sorry
example : f 0 = f 1 := rfl -- succeeds
```
One can be more careful by putting parameters to the right of the colon:
```lean
def f : (n : Nat) → Nat := sorry
example : f 0 = f 1 := rfl -- fails
```
Most sources of synthetic sorries (recall: a sorry that originates from
the elaborator) are now unique, except for elaboration errors, since
making these unique tends to cause a confusing cascade of errors. In
general, however, such sorries are labeled. This enables "go to
definition" on `sorry` in the Infoview, which brings you to its origin.
The option `set_option pp.sorrySource true` causes the pretty printer to
show source position information on sorries.

### Separators in numeric literals

[#6204](https://github.com/leanprover/lean4/pull/6204) lets `_` be used in numeric literals as a separator. For
example, `1_000_000`, `0xff_ff` or `0b_10_11_01_00`. New lexical syntax:
```text
numeral10 : [0-9]+ ("_"+ [0-9]+)*
numeral2  : "0" [bB] ("_"* [0-1]+)+
numeral8  : "0" [oO] ("_"* [0-7]+)+
numeral16 : "0" [xX] ("_"* hex_char+)+
float     : numeral10 "." numeral10? [eE[+-]numeral10]
```

### Additional new featues

* [#6300](https://github.com/leanprover/lean4/pull/6300) adds the `debug.proofAsSorry` option. When enabled, the proofs
of theorems are ignored and replaced with `sorry`.

* [#6362](https://github.com/leanprover/lean4/pull/6362) adds the `--error=kind` option (shorthand: `-Ekind`) to the
`lean` CLI. When set, messages of `kind` (e.g.,
`linter.unusedVariables`) will be reported as errors. This setting does
nothing in interactive contexts (e.g., the server).

* [#6366](https://github.com/leanprover/lean4/pull/6366) adds support for `Float32` and fixes a bug in the runtime.

### Library updates

The Lean 4 library saw many changes that improve arithmetic reasoning, enhance data structure APIs,
and refine library organization. Key changes include better support for bitwise operations, shifts,
and conversions, expanded lemmas for `Array`, `Vector`, and `List`, and improved ordering definitions.
Some modules have been reorganized for clarity, and internal refinements ensure greater consistency and correctness.

### Breaking changes

[#6330](https://github.com/leanprover/lean4/pull/6330) removes unnecessary parameters from the functional induction
principles. This is a breaking change; broken code can typically be adjusted
simply by passing fewer parameters.

_This highlights section was contributed by Violetta Sim._

For this release, 201 changes landed. In addition to the 74 feature additions and 44 fixes listed below there were 7 refactoring changes, 5 documentation improvements and 62 chores.

## Language

* [#3696](https://github.com/leanprover/lean4/pull/3696) makes all message constructors handle pretty printer errors.

* [#4460](https://github.com/leanprover/lean4/pull/4460) runs all linters for a single command (together) on a separate
thread from further elaboration, making a first step towards
parallelizing the elaborator.

* [#5757](https://github.com/leanprover/lean4/pull/5757), see the highlights section above for details.

* [#6123](https://github.com/leanprover/lean4/pull/6123) ensures that the configuration in `Simp.Config` is used when
reducing terms and checking definitional equality in `simp`.

* [#6204](https://github.com/leanprover/lean4/pull/6204), see the highlights section above for details.

* [#6270](https://github.com/leanprover/lean4/pull/6270) fixes a bug that could cause the `injectivity` tactic to fail in
reducible mode, which could cause unfolding lemma generation to fail
(used by tactics such as `unfold`). In particular,
`Lean.Meta.isConstructorApp'?` was not aware that `n + 1` is equivalent
to `Nat.succ n`.

* [#6273](https://github.com/leanprover/lean4/pull/6273) modifies the "foo has been deprecated: use betterFoo instead"
warning so that foo and betterFoo are hoverable.

* [#6278](https://github.com/leanprover/lean4/pull/6278) enables simp configuration options to be passed to `norm_cast`.

* [#6286](https://github.com/leanprover/lean4/pull/6286) ensure `bv_decide` uses definitional equality in its reflection
procedure as much as possible. Previously it would build up explicit
congruence proofs for the kernel to check. This reduces the size of
proof terms passed to kernel speeds up checking of large reflection
proofs.

* [#6288](https://github.com/leanprover/lean4/pull/6288) uses Lean.RArray in bv_decide's reflection proofs. Giving
speedups on problems with lots of variables.

* [#6295](https://github.com/leanprover/lean4/pull/6295) sets up simprocs for all the remaining operations defined in
`Init.Data.Fin.Basic`

* [#6300](https://github.com/leanprover/lean4/pull/6300), see the highlights section above for details.

* [#6330](https://github.com/leanprover/lean4/pull/6330), see the highlights section above for details.

* [#6362](https://github.com/leanprover/lean4/pull/6362), see the highlights section above for details.

* [#6366](https://github.com/leanprover/lean4/pull/6366), see the highlights section above for details.

* [#6375](https://github.com/leanprover/lean4/pull/6375) fixes a bug in the simplifier. It was producing terms with loose
bound variables when eliminating unused `let_fun` expressions.

* [#6378](https://github.com/leanprover/lean4/pull/6378) adds an explanation to the error message when `cases` and
`induction` are applied to a term whose type is not an inductive type.
For `Prop`, these tactics now suggest the `by_cases` tactic. Example:
```
tactic 'cases' failed, major premise type is not an inductive type
  Prop
```

* [#6381](https://github.com/leanprover/lean4/pull/6381) fixes a bug in `withTrackingZetaDelta` and
`withTrackingZetaDeltaSet`. The `MetaM` caches need to be reset. See new
test.

* [#6385](https://github.com/leanprover/lean4/pull/6385) fixes a bug in `simp_all?` that caused some local declarations
to be omitted from the `Try this:` suggestions.

* [#6386](https://github.com/leanprover/lean4/pull/6386) ensures that `revertAll` clears auxiliary declarations when
invoked directly by users.

* [#6387](https://github.com/leanprover/lean4/pull/6387) fixes a type error in the proof generated by the `contradiction`
tactic.

* [#6397](https://github.com/leanprover/lean4/pull/6397) ensures that `simp` and `dsimp` do not unfold definitions that
are not intended to be unfolded by the user. See issue #5755 for an
example affected by this issue.

* [#6398](https://github.com/leanprover/lean4/pull/6398) ensures `Meta.check` check projections.

* [#6412](https://github.com/leanprover/lean4/pull/6412) adds reserved names for congruence theorems used in the
simplifier and `grind` tactics. The idea is prevent the same congruence
theorems to be generated over and over again.

* [#6413](https://github.com/leanprover/lean4/pull/6413) introduces the following features to the WIP `grind` tactic:
- `Expr` internalization.
- Congruence theorem cache.
- Procedure for adding new facts
- New tracing options
- New preprocessing steps: fold projections and eliminate dangling
`Expr.mdata`

* [#6414](https://github.com/leanprover/lean4/pull/6414) fixes a bug in `Lean.Meta.Closure` that would introduce
under-applied delayed assignment metavariables, which would keep them
from ever getting instantiated. This bug affected `match` elaboration
when the expected type contained postponed elaboration problems, for
example tactic blocks.

* [#6419](https://github.com/leanprover/lean4/pull/6419) fixes multiple bugs in the WIP `grind` tactic. It also adds
support for printing the `grind` internal state.

* [#6428](https://github.com/leanprover/lean4/pull/6428) adds a new preprocessing step to the `grind` tactic:
universe-level normalization. The goal is to avoid missing equalities in
the congruence closure module.

* [#6430](https://github.com/leanprover/lean4/pull/6430) adds the predicate `Expr.fvarsSet a b`, which returns `true` if
and only if the free variables in `a` are a subset of the free variables
in `b`.

* [#6433](https://github.com/leanprover/lean4/pull/6433) adds a custom type and instance canonicalizer for the (WIP)
`grind` tactic. The `grind` tactic uses congruence closure but
disregards types, type formers, instances, and proofs. Proofs are
ignored due to proof irrelevance. Types, type formers, and instances are
considered supporting elements and are not factored into congruence
detection. Instead, `grind` only checks whether elements are
structurally equal, which, in the context of the `grind` tactic, is
equivalent to pointer equality. See new tests for examples where the
canonicalizer is important.

* [#6435](https://github.com/leanprover/lean4/pull/6435) implements the congruence table for the (WIP) `grind` tactic. It
also fixes several bugs, and adds a new preprocessing step.

* [#6437](https://github.com/leanprover/lean4/pull/6437) adds support for detecting congruent terms in the (WIP) `grind`
tactic. It also introduces the `grind.debug` option, which, when set to
`true`, checks many invariants after each equivalence class is merged.
This option is intended solely for debugging purposes.

* [#6438](https://github.com/leanprover/lean4/pull/6438) ensures `norm_cast` doesn't fail to act in the presence of
`no_index` annotations

* [#6441](https://github.com/leanprover/lean4/pull/6441) adds basic truth value propagation rules to the (WIP) `grind`
tactic.

* [#6442](https://github.com/leanprover/lean4/pull/6442) fixes the `checkParents` sanity check in `grind`.

* [#6443](https://github.com/leanprover/lean4/pull/6443) adds support for propagating the truth value of equalities in
the (WIP) `grind` tactic.

* [#6447](https://github.com/leanprover/lean4/pull/6447) refactors `grind` and adds support for invoking the simplifier
using the `GrindM` monad.

* [#6448](https://github.com/leanprover/lean4/pull/6448) declares the command `builtin_grind_propagator` for registering
equation propagator for `grind`. It also declares the auxiliary the
attribute.

* [#6449](https://github.com/leanprover/lean4/pull/6449) completes the implementation of the command
`builtin_grind_propagator`.

* [#6452](https://github.com/leanprover/lean4/pull/6452) adds support for generating (small) proofs for any two
expressions that belong to the same equivalence class in the `grind`
tactic state.

* [#6453](https://github.com/leanprover/lean4/pull/6453) improves bv_decide's performance in the presence of large
literals.

* [#6455](https://github.com/leanprover/lean4/pull/6455) fixes a bug in the equality proof generator in the (WIP) `grind`
tactic.

* [#6456](https://github.com/leanprover/lean4/pull/6456) fixes another bug in the equality proof generator in the (WIP)
`grind` tactic.

* [#6457](https://github.com/leanprover/lean4/pull/6457) adds support for generating congruence proofs for congruences
detected by the `grind` tactic.

* [#6458](https://github.com/leanprover/lean4/pull/6458) adds support for compact congruence proofs in the (WIP) `grind`
tactic. The `mkCongrProof` function now verifies whether the congruence
proof can be constructed using only `congr`, `congrFun`, and `congrArg`,
avoiding the need to generate the more complex `hcongr` auxiliary
theorems.

* [#6459](https://github.com/leanprover/lean4/pull/6459) adds the (WIP) `grind` tactic. It currently generates a warning
message to make it clear that the tactic is not ready for production.

* [#6461](https://github.com/leanprover/lean4/pull/6461) adds a new propagation rule for negation to the (WIP) `grind`
tactic.

* [#6463](https://github.com/leanprover/lean4/pull/6463) adds support for constructors to the (WIP) `grind` tactic. When
merging equivalence classes, `grind` checks for equalities between
constructors. If they are distinct, it closes the goal; if they are the
same, it applies injectivity.

* [#6464](https://github.com/leanprover/lean4/pull/6464) completes support for literal values in the (WIP) `grind`
tactic. `grind` now closes the goal whenever it merges two equivalence
classes with distinct literal values.

* [#6465](https://github.com/leanprover/lean4/pull/6465) adds support for projection functions to the (WIP) `grind`
tactic.

* [#6466](https://github.com/leanprover/lean4/pull/6466) completes the implementation of `addCongrTable` in the (WIP)
`grind` tactic. It also adds a new test to demonstrate why the extra
check is needed. It also updates the field `cgRoot` (congruence root).

* [#6468](https://github.com/leanprover/lean4/pull/6468) fixes issue #6467

* [#6469](https://github.com/leanprover/lean4/pull/6469) adds support code for implementing e-match in the (WIP) `grind`
tactic.

* [#6470](https://github.com/leanprover/lean4/pull/6470) introduces a command for specifying patterns used in the
heuristic instantiation of global theorems in the `grind` tactic. Note
that this PR only adds the parser.

* [#6472](https://github.com/leanprover/lean4/pull/6472) implements the command `grind_pattern`. The new command allows
users to associate patterns with theorems. These patterns are used for
performing heuristic instantiation with e-matching. In the future, we
will add the attributes `@[grind_eq]`, `@[grind_fwd]`, and
`@[grind_bwd]` to compute the patterns automatically for theorems.

* [#6473](https://github.com/leanprover/lean4/pull/6473) adds a deriving handler for the `ToExpr` class. It can handle
mutual and nested inductive types, however it falls back to creating
`partial` instances in such cases. This is upstreamed from the Mathlib
deriving handler written by @kmill, but has fixes to handle autoimplicit
universe level variables.

* [#6474](https://github.com/leanprover/lean4/pull/6474) adds pattern validation to the `grind_pattern` command. The new
`checkCoverage` function will also be used to implement the attributes
`@[grind_eq]`, `@[grind_fwd]`, and `@[grind_bwd]`.

* [#6475](https://github.com/leanprover/lean4/pull/6475) adds support for activating relevant theorems for the (WIP)
`grind` tactic. We say a theorem is relevant to a `grind` goal if the
symbols occurring in its patterns also occur in the goal.

* [#6478](https://github.com/leanprover/lean4/pull/6478) internalize nested ground patterns when activating ematch
theorems in the (WIP) `grind` tactic.

* [#6481](https://github.com/leanprover/lean4/pull/6481) implements E-matching for the (WIP) `grind` tactic. We still
need to finalize and internalize the new instances.

* [#6484](https://github.com/leanprover/lean4/pull/6484) addresses a few error messages where diffs weren't being
exposed.

* [#6485](https://github.com/leanprover/lean4/pull/6485) implements `Grind.EMatch.instantiateTheorem` in the (WIP)
`grind` tactic.

* [#6487](https://github.com/leanprover/lean4/pull/6487) adds source position information for `structure` parent
projections, supporting "go to definition". Closes #3063.

* [#6488](https://github.com/leanprover/lean4/pull/6488) fixes and refactors the E-matching module for the (WIP) `grind`
tactic.

* [#6490](https://github.com/leanprover/lean4/pull/6490) adds basic configuration options for the `grind` tactic.

* [#6492](https://github.com/leanprover/lean4/pull/6492) fixes a bug in the theorem instantiation procedure in the (WIP)
`grind` tactic.

* [#6497](https://github.com/leanprover/lean4/pull/6497) fixes another theorem instantiation bug in the `grind` tactic.
It also moves new instances to be processed to `Goal`.

* [#6498](https://github.com/leanprover/lean4/pull/6498) adds support in the `grind` tactic for propagating dependent
forall terms `forall (h : p), q[h]` where `p` is a proposition.

* [#6499](https://github.com/leanprover/lean4/pull/6499) fixes the proof canonicalizer for `grind`.

* [#6500](https://github.com/leanprover/lean4/pull/6500) fixes a bug in the `markNestedProofs` used in `grind`. See new
test.

* [#6502](https://github.com/leanprover/lean4/pull/6502) fixes a bug in the proof assembly procedure utilized by the
`grind` tactic.

* [#6503](https://github.com/leanprover/lean4/pull/6503) adds a simple strategy to the (WIP) `grind` tactic. It just
keeps internalizing new theorem instances found by E-matching.

* [#6506](https://github.com/leanprover/lean4/pull/6506) adds the `monotonicity` tactic, intended to be used inside the
`partial_fixpoint` feature.

* [#6508](https://github.com/leanprover/lean4/pull/6508) fixes a bug in the sanity checkers for the `grind` tactic. See
the new test for an example of a case where it was panicking.

* [#6509](https://github.com/leanprover/lean4/pull/6509) fixes a bug in the congruence closure data structure used in the
`grind` tactic. The new test includes an example that previously caused
a panic. A similar panic was also occurring in the test
`grind_nested_proofs.lean`.

* [#6510](https://github.com/leanprover/lean4/pull/6510) adds a custom congruence rule for equality in `grind`. The new
rule takes into account that `Eq` is a symmetric relation. In the
future, we will add support for arbitrary symmetric relations. The
current rule is important for propagating disequalities effectively in
`grind`.

* [#6512](https://github.com/leanprover/lean4/pull/6512) introduces support for user-defined fallback code in the `grind`
tactic. The fallback code can be utilized to inspect the state of
failing `grind` subgoals and/or invoke user-defined automation. Users
can now write `grind on_failure <code>`, where `<code>` should have the
type `GoalM Unit`. See the modified tests in this PR for examples.

* [#6513](https://github.com/leanprover/lean4/pull/6513) adds support for (dependent) if-then-else terms (i.e., `ite` and
`dite` applications) in the `grind` tactic.

* [#6514](https://github.com/leanprover/lean4/pull/6514) enhances the assertion of new facts in `grind` by avoiding the
creation of unnecessary metavariables.

## Library

* [#6182](https://github.com/leanprover/lean4/pull/6182) adds `BitVec.[toInt|toFin]_concat` and moves a couple of
theorems into the concat section, as `BitVec.msb_concat` is needed for
the `toInt_concat` proof.

* [#6188](https://github.com/leanprover/lean4/pull/6188) completes the `toNat` theorems for the bitwise operations
(`and`, `or`, `xor`, `shiftLeft`, `shiftRight`) of the UInt types and
adds `toBitVec` theorems as well. It also renames `and_toNat` to
`toNat_and` to fit with the current naming convention.

* [#6238](https://github.com/leanprover/lean4/pull/6238) adds theorems characterizing the value of the unsigned shift
right of a bitvector in terms of its 2s complement interpretation as an
integer.
Unsigned shift right by at least one bit makes the value of the
bitvector less than or equal to `2^(w-1)`,
makes the interpretation of the bitvector `Int` and `Nat` agree.
In the case when `n = 0`, then the shift right value equals the integer
interpretation.

* [#6244](https://github.com/leanprover/lean4/pull/6244) changes the implementation of `HashMap.toList`, so the ordering
agrees with `HashMap.toArray`.

* [#6272](https://github.com/leanprover/lean4/pull/6272) introduces the basic theory of permutations of `Array`s and
proves `Array.swap_perm`.

* [#6282](https://github.com/leanprover/lean4/pull/6282) moves `IO.Channel` and `IO.Mutex` from `Init` to `Std.Sync` and
renames them to `Std.Channel` and `Std.Mutex`.

* [#6294](https://github.com/leanprover/lean4/pull/6294) upstreams `List.length_flatMap`, `countP_flatMap` and
`count_flatMap` from Mathlib. These were not possible to state before we
upstreamed `List.sum`.

* [#6315](https://github.com/leanprover/lean4/pull/6315) adds `protected` to `Fin.cast` and `BitVec.cast`, to avoid
confusion with `_root_.cast`. These should mostly be used via
dot-notation in any case.

* [#6316](https://github.com/leanprover/lean4/pull/6316) adds lemmas simplifying `for` loops over `Option` into
`Option.pelim`, giving parity with lemmas simplifying `for` loops of
`List` into `List.fold`.

* [#6317](https://github.com/leanprover/lean4/pull/6317) completes the basic API for BitVec.ofBool.

* [#6318](https://github.com/leanprover/lean4/pull/6318) generalizes the universe level for `Array.find?`, by giving it a
separate implementation from `Array.findM?`.

* [#6324](https://github.com/leanprover/lean4/pull/6324) adds `GetElem` lemmas for the basic `Vector` operations.

* [#6333](https://github.com/leanprover/lean4/pull/6333) generalizes the panic functions to a type of `Sort u` rather
than `Type u`. This better supports universe polymorphic types and
avoids confusing errors.

* [#6334](https://github.com/leanprover/lean4/pull/6334) adds `Nat` theorems for distributing `>>>` over bitwise
operations, paralleling those of `BitVec`.

* [#6338](https://github.com/leanprover/lean4/pull/6338) adds `BitVec.[toFin|getMsbD]_setWidth` and
`[getMsb|msb]_signExtend` as well as `ofInt_toInt`.

* [#6341](https://github.com/leanprover/lean4/pull/6341) generalizes `DecidableRel` to allow a heterogeneous relation.

* [#6353](https://github.com/leanprover/lean4/pull/6353) reproduces the API around `List.any/all` for `Array.any/all`.

* [#6364](https://github.com/leanprover/lean4/pull/6364) makes fixes suggested by the Batteries environment linters,
particularly `simpNF`, and `unusedHavesSuffices`.

* [#6365](https://github.com/leanprover/lean4/pull/6365) expands the `Array.set` and `Array.setIfInBounds` lemmas to
match existing lemmas for `List.set`.

* [#6367](https://github.com/leanprover/lean4/pull/6367) brings Vector lemmas about membership and indexing to parity
with List and Array.

* [#6369](https://github.com/leanprover/lean4/pull/6369) adds lemmas about `Vector.set`, `anyM`, `any`, `allM`, and
`all`.

* [#6376](https://github.com/leanprover/lean4/pull/6376) adds theorems about `==` on `Vector`, reproducing those already
on `List` and `Array`.

* [#6379](https://github.com/leanprover/lean4/pull/6379) replaces the inductive predicate `List.lt` with an upstreamed version of `List.Lex` from Mathlib.
(Previously `Lex.lt` was defined in terms of `<`; now it is generalized to take an arbitrary relation.)
This subtly changes the notion of ordering on `List α`.

  `List.lt` was a weaker relation: in particular if `l₁ < l₂`, then `a :: l₁ < b :: l₂` may hold according to `List.lt` even if `a` and `b` are merely incomparable (either neither `a < b` nor `b < a`), whereas according to `List.Lex` this would require `a = b`.

  When `<` is total, in the sense that `¬ · < ·` is antisymmetric, then the two relations coincide.

  Mathlib was already overriding the order instances for `List α`, so this change should not be noticed by anyone already using Mathlib.

  We simultaneously add the boolean valued `List.lex` function, parameterised by a `BEq` typeclass and an arbitrary `lt` function. This will support the flexibility previously provided for `List.lt`, via a `==` function which is weaker than strict equality.

* [#6390](https://github.com/leanprover/lean4/pull/6390) redefines `Range.forIn'` and `Range.forM`, in preparation for
writing lemmas about them.

* [#6391](https://github.com/leanprover/lean4/pull/6391) requires that the step size in `Std.Range` is positive, to avoid
ill-specified behaviour.

* [#6396](https://github.com/leanprover/lean4/pull/6396) adds lemmas reducing for loops over `Std.Range` to for loops
over `List.range'`.

* [#6399](https://github.com/leanprover/lean4/pull/6399) adds basic lemmas about lexicographic order on Array and Vector,
achieving parity with List.

* [#6423](https://github.com/leanprover/lean4/pull/6423) adds missing lemmas about lexicographic order on
List/Array/Vector.

* [#6477](https://github.com/leanprover/lean4/pull/6477) adds the necessary domain theory that backs the
`partial_fixpoint` feature.

## Compiler

* [#6311](https://github.com/leanprover/lean4/pull/6311) adds support for `HEq` to the new code generator.

* [#6348](https://github.com/leanprover/lean4/pull/6348) adds support for `Float32` to the Lean runtime.

* [#6350](https://github.com/leanprover/lean4/pull/6350) adds missing features and fixes bugs in the `Float32` support

* [#6383](https://github.com/leanprover/lean4/pull/6383) ensures the new code generator produces code for `opaque`
definitions that are not tagged as `@[extern]`.
Remark: This is the behavior of the old code generator.

* [#6405](https://github.com/leanprover/lean4/pull/6405) adds support for erasure of `Decidable.decide` to the new code
generator. It also adds a new `Probe.runOnDeclsNamed` function, which is
helpful for writing targeted single-file tests of compiler internals.

* [#6415](https://github.com/leanprover/lean4/pull/6415) fixes a bug in the `sharecommon` module, which was returning
incorrect results for objects that had already been processed by
`sharecommon`. See the new test for an example that triggered the bug.

* [#6429](https://github.com/leanprover/lean4/pull/6429) adds support for extern LCNF decls, which is required for parity
with the existing code generator.

* [#6535](https://github.com/leanprover/lean4/pull/6535) avoids a linker warning on Windows.

* [#6547](https://github.com/leanprover/lean4/pull/6547) should prevent Lake from accidentally picking up other linkers
installed on the machine.

* [#6574](https://github.com/leanprover/lean4/pull/6574) actually prevents Lake from accidentally picking up other
toolchains installed on the machine.

## Pretty Printing

* [#5689](https://github.com/leanprover/lean4/pull/5689) adjusts the way the pretty printer unresolves names. It used to
make use of all `export`s when pretty printing, but now it only uses
`export`s that put names into parent namespaces (heuristic: these are
"API exports" that are intended by the library author), rather than
"horizontal exports" that put the names into an unrelated namespace,
which the dot notation feature in #6189 now incentivizes.

* [#5757](https://github.com/leanprover/lean4/pull/5757), aside from introducing labeled sorries, fixes the bug that the metadata attached to the pretty-printed representation of arguments with a borrow annotation (for example, the second argument of `String.append`), is inconsistent with the metadata attached to the regular arguments.

## Documentation

* [#6450](https://github.com/leanprover/lean4/pull/6450) adds a docstring to the `@[app_delab]` attribute.

## Server

* [#6279](https://github.com/leanprover/lean4/pull/6279) fixes a bug in structure instance field completion that caused
it to not function correctly for bracketed structure instances written
in Mathlib style.

* [#6408](https://github.com/leanprover/lean4/pull/6408) fixes a regression where goals that don't exist were being
displayed. The regression was triggered by #5835 and originally caused
by #4926.

## Lake

* [#6176](https://github.com/leanprover/lean4/pull/6176) changes Lake's build process to no longer use `leanc` for
compiling C files or linking shared libraries and executables. Instead,
it directly invokes the bundled compiler (or the native compiler if
none) using the necessary flags.

* [#6289](https://github.com/leanprover/lean4/pull/6289) adapts Lake modules to use `prelude` and includes them in the
`check-prelude` CI.

* [#6291](https://github.com/leanprover/lean4/pull/6291) ensures the the log error position is properly preserved when
prepending stray log entries to the job log. It also adds comparison
support for `Log.Pos`.

* [#6388](https://github.com/leanprover/lean4/pull/6388) merges `BuildJob` and `Job`, deprecating the former. `Job` now
contains a trace as part of its state which can be interacted with
monadically. also simplifies the implementation of `OpaqueJob`.

* [#6411](https://github.com/leanprover/lean4/pull/6411) adds the ability to override package entries in a Lake manifest
via a separate JSON file. This file can be specified on the command line
with `--packages` or applied persistently by placing it at
`.lake/package-overrides.json`.

* [#6422](https://github.com/leanprover/lean4/pull/6422) fixes a bug in #6388 where the `Package.afterBuildCahe*`
functions would produce different traces depending on whether the cache
was fetched.

* [#6627](https://github.com/leanprover/lean4/pull/6627) aims to fix the trace issues reported by Mathlib that are
breaking `lake exe cache` in downstream projects.

* [#6631](https://github.com/leanprover/lean4/pull/6631) sets `MACOSX_DEPLOYMENT_TARGET` for shared libraries (it was
previously only set for executables).

## Other

* [#6285](https://github.com/leanprover/lean4/pull/6285) upstreams the `ToLevel` typeclass from mathlib and uses it to
fix the existing `ToExpr` instances so that they are truly universe
polymorphic (previously it generated malformed expressions when the
universe level was nonzero). We improve on the mathlib definition of
`ToLevel` to ensure the class always lives in `Type`, irrespective of
the universe parameter.

* [#6363](https://github.com/leanprover/lean4/pull/6363) fixes errors at load time in the comparison mode of the Firefox
profiler.

````
