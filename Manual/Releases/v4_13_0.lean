/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.13.0 (2024-11-01)" =>
%%%
tag := "release-v4.13.0"
file := "v4.13.0"
%%%

```markdown
**Full Changelog**: https://github.com/leanprover/lean4/compare/v4.12.0...v4.13.0

### Language features, tactics, and metaprograms

* `structure` command
  * [#5511](https://github.com/leanprover/lean4/pull/5511) allows structure parents to be type synonyms.
  * [#5531](https://github.com/leanprover/lean4/pull/5531) allows default values for structure fields to be noncomputable.

* `rfl` and `apply_rfl` tactics
  * [#3714](https://github.com/leanprover/lean4/pull/3714), [#3718](https://github.com/leanprover/lean4/pull/3718) improve the `rfl` tactic and give better error messages.
  * [#3772](https://github.com/leanprover/lean4/pull/3772) makes `rfl` no longer use kernel defeq for ground terms.
  * [#5329](https://github.com/leanprover/lean4/pull/5329) tags `Iff.refl` with `@[refl]` (@Parcly-Taxel)
  * [#5359](https://github.com/leanprover/lean4/pull/5359) ensures that the `rfl` tactic tries `Iff.rfl` (@Parcly-Taxel)

* `unfold` tactic
  * [#4834](https://github.com/leanprover/lean4/pull/4834) let `unfold` do zeta-delta reduction of local definitions, incorporating functionality of the Mathlib `unfold_let` tactic.

* `omega` tactic
  * [#5382](https://github.com/leanprover/lean4/pull/5382) fixes spurious error in [#5315](https://github.com/leanprover/lean4/issues/5315)
  * [#5523](https://github.com/leanprover/lean4/pull/5523) supports `Int.toNat`

* `simp` tactic
  * [#5479](https://github.com/leanprover/lean4/pull/5479) lets `simp` apply rules with higher-order patterns.

* `induction` tactic
  * [#5494](https://github.com/leanprover/lean4/pull/5494) fixes `induction`’s "pre-tactic" block to always be indented, avoiding unintended uses of it.

* `ac_nf` tactic
  * [#5524](https://github.com/leanprover/lean4/pull/5524) adds `ac_nf`, a counterpart to `ac_rfl`, for normalizing expressions with respect to associativity and commutativity. Tests it with `BitVec` expressions.

* `bv_decide`
  * [#5211](https://github.com/leanprover/lean4/pull/5211) makes `extractLsb'` the primitive `bv_decide` understands, rather than `extractLsb` (@alexkeizer)
  * [#5365](https://github.com/leanprover/lean4/pull/5365) adds `bv_decide` diagnoses.
  * [#5375](https://github.com/leanprover/lean4/pull/5375) adds `bv_decide` normalization rules for `ofBool (a.getLsbD i)` and `ofBool a[i]` (@alexkeizer)
  * [#5423](https://github.com/leanprover/lean4/pull/5423) enhances the rewriting rules of `bv_decide`
  * [#5433](https://github.com/leanprover/lean4/pull/5433) presents the `bv_decide` counterexample at the API
  * [#5484](https://github.com/leanprover/lean4/pull/5484) handles `BitVec.ofNat` with `Nat` fvars in `bv_decide`
  * [#5506](https://github.com/leanprover/lean4/pull/5506), [#5507](https://github.com/leanprover/lean4/pull/5507) add `bv_normalize` rules.
  * [#5568](https://github.com/leanprover/lean4/pull/5568) generalize the `bv_normalize` pipeline to support more general preprocessing passes
  * [#5573](https://github.com/leanprover/lean4/pull/5573) gets `bv_normalize` up-to-date with the current `BitVec` rewrites
  * Cleanups: [#5408](https://github.com/leanprover/lean4/pull/5408), [#5493](https://github.com/leanprover/lean4/pull/5493), [#5578](https://github.com/leanprover/lean4/pull/5578)


* Elaboration improvements
  * [#5266](https://github.com/leanprover/lean4/pull/5266) preserve order of overapplied arguments in `elab_as_elim` procedure.
  * [#5510](https://github.com/leanprover/lean4/pull/5510) generalizes `elab_as_elim` to allow arbitrary motive applications.
  * [#5283](https://github.com/leanprover/lean4/pull/5283), [#5512](https://github.com/leanprover/lean4/pull/5512) refine how named arguments suppress explicit arguments. Breaking change: some previously omitted explicit arguments may need explicit `_` arguments now.
  * [#5376](https://github.com/leanprover/lean4/pull/5376) modifies projection instance binder info for instances, making parameters that are instance implicit in the type be implicit.
  * [#5402](https://github.com/leanprover/lean4/pull/5402) localizes universe metavariable errors to `let` bindings and `fun` binders if possible. Makes "cannot synthesize metavariable" errors take precedence over unsolved universe level errors.
  * [#5419](https://github.com/leanprover/lean4/pull/5419) must not reduce `ite` in the discriminant of `match`-expression when reducibility setting is `.reducible`
  * [#5474](https://github.com/leanprover/lean4/pull/5474) have autoparams report parameter/field on failure
  * [#5530](https://github.com/leanprover/lean4/pull/5530) makes automatic instance names about types with hygienic names be hygienic.

* Deriving handlers
  * [#5432](https://github.com/leanprover/lean4/pull/5432) makes `Repr` deriving instance handle explicit type parameters

* Functional induction
  * [#5364](https://github.com/leanprover/lean4/pull/5364) adds more equalities in context, more careful cleanup.

* Linters
  * [#5335](https://github.com/leanprover/lean4/pull/5335) fixes the unused variables linter complaining about match/tactic combinations
  * [#5337](https://github.com/leanprover/lean4/pull/5337) fixes the unused variables linter complaining about some wildcard patterns

* Other fixes
  * [#4768](https://github.com/leanprover/lean4/pull/4768) fixes a parse error when `..` appears with a `.` on the next line

* Metaprogramming
  * [#3090](https://github.com/leanprover/lean4/pull/3090) handles level parameters in `Meta.evalExpr` (@eric-wieser)
  * [#5401](https://github.com/leanprover/lean4/pull/5401) instance for `Inhabited (TacticM α)` (@alexkeizer)
  * [#5412](https://github.com/leanprover/lean4/pull/5412) expose Kernel.check for debugging purposes
  * [#5556](https://github.com/leanprover/lean4/pull/5556) improves the "invalid projection" type inference error in `inferType`.
  * [#5587](https://github.com/leanprover/lean4/pull/5587) allows `MVarId.assertHypotheses` to set `BinderInfo` and `LocalDeclKind`.
  * [#5588](https://github.com/leanprover/lean4/pull/5588) adds `MVarId.tryClearMany'`, a variant of `MVarId.tryClearMany`.



### Language server, widgets, and IDE extensions

* [#5205](https://github.com/leanprover/lean4/pull/5205) decreases the latency of auto-completion in tactic blocks.
* [#5237](https://github.com/leanprover/lean4/pull/5237) fixes symbol occurrence highlighting in VS Code not highlighting occurrences when moving the text cursor into the identifier from the right.
* [#5257](https://github.com/leanprover/lean4/pull/5257) fixes several instances of incorrect auto-completions being reported.
* [#5299](https://github.com/leanprover/lean4/pull/5299) allows auto-completion to report completions for global identifiers when the elaborator fails to provide context-specific auto-completions.
* [#5312](https://github.com/leanprover/lean4/pull/5312) fixes the server breaking when changing whitespace after the module header.
* [#5322](https://github.com/leanprover/lean4/pull/5322) fixes several instances of auto-completion reporting non-existent namespaces.
* [#5428](https://github.com/leanprover/lean4/pull/5428) makes sure to always report some recent file range as progress when waiting for elaboration.


### Pretty printing

* [#4979](https://github.com/leanprover/lean4/pull/4979) make pretty printer escape identifiers that are tokens.
* [#5389](https://github.com/leanprover/lean4/pull/5389) makes formatter use the current token table.
* [#5513](https://github.com/leanprover/lean4/pull/5513) use breakable instead of unbreakable whitespace when formatting tokens.


### Library

* [#5222](https://github.com/leanprover/lean4/pull/5222) reduces allocations in `Json.compress`.
* [#5231](https://github.com/leanprover/lean4/pull/5231) upstreams `Zero` and `NeZero`
* [#5292](https://github.com/leanprover/lean4/pull/5292) refactors `Lean.Elab.Deriving.FromToJson` (@arthur-adjedj)
* [#5415](https://github.com/leanprover/lean4/pull/5415) implements `Repr Empty` (@TomasPuverle)
* [#5421](https://github.com/leanprover/lean4/pull/5421) implements `To/FromJSON Empty` (@TomasPuverle)

* Logic
  * [#5263](https://github.com/leanprover/lean4/pull/5263) allows simplifying `dite_not`/`decide_not` with only `Decidable (¬p)`.
  * [#5268](https://github.com/leanprover/lean4/pull/5268) fixes binders on `ite_eq_left_iff`
  * [#5284](https://github.com/leanprover/lean4/pull/5284) turns off `Inhabited (Sum α β)` instances
  * [#5355](https://github.com/leanprover/lean4/pull/5355) adds simp lemmas for `LawfulBEq`
  * [#5374](https://github.com/leanprover/lean4/pull/5374) add `Nonempty` instances for products, allowing more `partial` functions to elaborate successfully
  * [#5447](https://github.com/leanprover/lean4/pull/5447) updates Pi instance names
  * [#5454](https://github.com/leanprover/lean4/pull/5454) makes some instance arguments implicit
  * [#5456](https://github.com/leanprover/lean4/pull/5456) adds `heq_comm`
  * [#5529](https://github.com/leanprover/lean4/pull/5529) moves `@[simp]` from `exists_prop'` to `exists_prop`

* `Bool`
  * [#5228](https://github.com/leanprover/lean4/pull/5228) fills gaps in Bool lemmas
  * [#5332](https://github.com/leanprover/lean4/pull/5332) adds notation `^^` for Bool.xor
  * [#5351](https://github.com/leanprover/lean4/pull/5351) removes `_root_.and` (and or/not/xor) and instead exports/uses `Bool.and` (etc.).

* `BitVec`
  * [#5240](https://github.com/leanprover/lean4/pull/5240) removes BitVec simps with complicated RHS
  * [#5247](https://github.com/leanprover/lean4/pull/5247) `BitVec.getElem_zeroExtend`
  * [#5248](https://github.com/leanprover/lean4/pull/5248) simp lemmas for BitVec, improving confluence
  * [#5249](https://github.com/leanprover/lean4/pull/5249) removes `@[simp]` from some BitVec lemmas
  * [#5252](https://github.com/leanprover/lean4/pull/5252) changes `BitVec.intMin/Max` from abbrev to def
  * [#5278](https://github.com/leanprover/lean4/pull/5278) adds `BitVec.getElem_truncate` (@tobiasgrosser)
  * [#5281](https://github.com/leanprover/lean4/pull/5281) adds udiv/umod bitblasting for `bv_decide` (@bollu)
  * [#5297](https://github.com/leanprover/lean4/pull/5297) `BitVec` unsigned order theoretic results
  * [#5313](https://github.com/leanprover/lean4/pull/5313) adds more basic BitVec ordering theory for UInt
  * [#5314](https://github.com/leanprover/lean4/pull/5314) adds `toNat_sub_of_le` (@bollu)
  * [#5357](https://github.com/leanprover/lean4/pull/5357) adds `BitVec.truncate` lemmas
  * [#5358](https://github.com/leanprover/lean4/pull/5358) introduces `BitVec.setWidth` to unify zeroExtend and truncate (@tobiasgrosser)
  * [#5361](https://github.com/leanprover/lean4/pull/5361) some BitVec GetElem lemmas
  * [#5385](https://github.com/leanprover/lean4/pull/5385) adds `BitVec.ofBool_[and|or|xor]_ofBool` theorems (@tobiasgrosser)
  * [#5404](https://github.com/leanprover/lean4/pull/5404) more of `BitVec.getElem_*` (@tobiasgrosser)
  * [#5410](https://github.com/leanprover/lean4/pull/5410) BitVec analogues of `Nat.{mul_two, two_mul, mul_succ, succ_mul}` (@bollu)
  * [#5411](https://github.com/leanprover/lean4/pull/5411) `BitVec.toNat_{add,sub,mul_of_lt}` for BitVector non-overflow reasoning (@bollu)
  * [#5413](https://github.com/leanprover/lean4/pull/5413) adds `_self`, `_zero`, and `_allOnes` for `BitVec.[and|or|xor]` (@tobiasgrosser)
  * [#5416](https://github.com/leanprover/lean4/pull/5416) adds LawCommIdentity + IdempotentOp for `BitVec.[and|or|xor]` (@tobiasgrosser)
  * [#5418](https://github.com/leanprover/lean4/pull/5418) decidable quantifers for BitVec
  * [#5450](https://github.com/leanprover/lean4/pull/5450) adds `BitVec.toInt_[intMin|neg|neg_of_ne_intMin]` (@tobiasgrosser)
  * [#5459](https://github.com/leanprover/lean4/pull/5459) missing BitVec lemmas
  * [#5469](https://github.com/leanprover/lean4/pull/5469) adds `BitVec.[not_not, allOnes_shiftLeft_or_shiftLeft, allOnes_shiftLeft_and_shiftLeft]` (@luisacicolini)
  * [#5478](https://github.com/leanprover/lean4/pull/5478) adds `BitVec.(shiftLeft_add_distrib, shiftLeft_ushiftRight)` (@luisacicolini)
  * [#5487](https://github.com/leanprover/lean4/pull/5487) adds `sdiv_eq`, `smod_eq` to allow `sdiv`/`smod` bitblasting (@bollu)
  * [#5491](https://github.com/leanprover/lean4/pull/5491) adds `BitVec.toNat_[abs|sdiv|smod]` (@tobiasgrosser)
  * [#5492](https://github.com/leanprover/lean4/pull/5492) `BitVec.(not_sshiftRight, not_sshiftRight_not, getMsb_not, msb_not)` (@luisacicolini)
  * [#5499](https://github.com/leanprover/lean4/pull/5499) `BitVec.Lemmas` - drop non-terminal simps (@tobiasgrosser)
  * [#5505](https://github.com/leanprover/lean4/pull/5505) unsimps `BitVec.divRec_succ'`
  * [#5508](https://github.com/leanprover/lean4/pull/5508) adds `BitVec.getElem_[add|add_add_bool|mul|rotateLeft|rotateRight…` (@tobiasgrosser)
  * [#5554](https://github.com/leanprover/lean4/pull/5554) adds `Bitvec.[add, sub, mul]_eq_xor` and `width_one_cases` (@luisacicolini)

* `List`
  * [#5242](https://github.com/leanprover/lean4/pull/5242) improve naming for `List.mergeSort` lemmas
  * [#5302](https://github.com/leanprover/lean4/pull/5302) provide `mergeSort` comparator autoParam
  * [#5373](https://github.com/leanprover/lean4/pull/5373) fix name of `List.length_mergeSort`
  * [#5377](https://github.com/leanprover/lean4/pull/5377) upstream `map_mergeSort`
  * [#5378](https://github.com/leanprover/lean4/pull/5378) modify signature of lemmas about `mergeSort`
  * [#5245](https://github.com/leanprover/lean4/pull/5245) avoid importing `List.Basic` without List.Impl
  * [#5260](https://github.com/leanprover/lean4/pull/5260) review of List API
  * [#5264](https://github.com/leanprover/lean4/pull/5264) review of List API
  * [#5269](https://github.com/leanprover/lean4/pull/5269) remove HashMap's duplicated Pairwise and Sublist
  * [#5271](https://github.com/leanprover/lean4/pull/5271) remove @[simp] from `List.head_mem` and similar
  * [#5273](https://github.com/leanprover/lean4/pull/5273) lemmas about `List.attach`
  * [#5275](https://github.com/leanprover/lean4/pull/5275) reverse direction of `List.tail_map`
  * [#5277](https://github.com/leanprover/lean4/pull/5277) more `List.attach` lemmas
  * [#5285](https://github.com/leanprover/lean4/pull/5285) `List.count` lemmas
  * [#5287](https://github.com/leanprover/lean4/pull/5287) use boolean predicates in `List.filter`
  * [#5289](https://github.com/leanprover/lean4/pull/5289) `List.mem_ite_nil_left` and analogues
  * [#5293](https://github.com/leanprover/lean4/pull/5293) cleanup of `List.findIdx` / `List.take` lemmas
  * [#5294](https://github.com/leanprover/lean4/pull/5294) switch primes on `List.getElem_take`
  * [#5300](https://github.com/leanprover/lean4/pull/5300) more `List.findIdx` theorems
  * [#5310](https://github.com/leanprover/lean4/pull/5310) fix `List.all/any` lemmas
  * [#5311](https://github.com/leanprover/lean4/pull/5311) fix `List.countP` lemmas
  * [#5316](https://github.com/leanprover/lean4/pull/5316) `List.tail` lemma
  * [#5331](https://github.com/leanprover/lean4/pull/5331) fix implicitness of `List.getElem_mem`
  * [#5350](https://github.com/leanprover/lean4/pull/5350) `List.replicate` lemmas
  * [#5352](https://github.com/leanprover/lean4/pull/5352) `List.attachWith` lemmas
  * [#5353](https://github.com/leanprover/lean4/pull/5353) `List.head_mem_head?`
  * [#5360](https://github.com/leanprover/lean4/pull/5360) lemmas about `List.tail`
  * [#5391](https://github.com/leanprover/lean4/pull/5391) review of `List.erase` / `List.find` lemmas
  * [#5392](https://github.com/leanprover/lean4/pull/5392) `List.fold` / `attach` lemmas
  * [#5393](https://github.com/leanprover/lean4/pull/5393) `List.fold` relators
  * [#5394](https://github.com/leanprover/lean4/pull/5394) lemmas about `List.maximum?`
  * [#5403](https://github.com/leanprover/lean4/pull/5403) theorems about `List.toArray`
  * [#5405](https://github.com/leanprover/lean4/pull/5405) reverse direction of `List.set_map`
  * [#5448](https://github.com/leanprover/lean4/pull/5448) add lemmas about `List.IsPrefix` (@Command-Master)
  * [#5460](https://github.com/leanprover/lean4/pull/5460) missing `List.set_replicate_self`
  * [#5518](https://github.com/leanprover/lean4/pull/5518) rename `List.maximum?` to `max?`
  * [#5519](https://github.com/leanprover/lean4/pull/5519) upstream `List.fold` lemmas
  * [#5520](https://github.com/leanprover/lean4/pull/5520) restore `@[simp]` on `List.getElem_mem` etc.
  * [#5521](https://github.com/leanprover/lean4/pull/5521) List simp fixes
  * [#5550](https://github.com/leanprover/lean4/pull/5550) `List.unattach` and simp lemmas
  * [#5594](https://github.com/leanprover/lean4/pull/5594) induction-friendly `List.min?_cons`

* `Array`
  * [#5246](https://github.com/leanprover/lean4/pull/5246) cleanup imports of Array.Lemmas
  * [#5255](https://github.com/leanprover/lean4/pull/5255) split Init.Data.Array.Lemmas for better bootstrapping
  * [#5288](https://github.com/leanprover/lean4/pull/5288) rename `Array.data` to `Array.toList`
  * [#5303](https://github.com/leanprover/lean4/pull/5303) cleanup of `List.getElem_append` variants
  * [#5304](https://github.com/leanprover/lean4/pull/5304) `Array.not_mem_empty`
  * [#5400](https://github.com/leanprover/lean4/pull/5400) reorganization in Array/Basic
  * [#5420](https://github.com/leanprover/lean4/pull/5420) make `Array` functions either semireducible or use structural recursion
  * [#5422](https://github.com/leanprover/lean4/pull/5422) refactor `DecidableEq (Array α)`
  * [#5452](https://github.com/leanprover/lean4/pull/5452) refactor of Array
  * [#5458](https://github.com/leanprover/lean4/pull/5458) cleanup of Array docstrings after refactor
  * [#5461](https://github.com/leanprover/lean4/pull/5461) restore `@[simp]` on `Array.swapAt!_def`
  * [#5465](https://github.com/leanprover/lean4/pull/5465) improve Array GetElem lemmas
  * [#5466](https://github.com/leanprover/lean4/pull/5466) `Array.foldX` lemmas
  * [#5472](https://github.com/leanprover/lean4/pull/5472) @[simp] lemmas about `List.toArray`
  * [#5485](https://github.com/leanprover/lean4/pull/5485) reverse simp direction for `toArray_concat`
  * [#5514](https://github.com/leanprover/lean4/pull/5514) `Array.eraseReps`
  * [#5515](https://github.com/leanprover/lean4/pull/5515) upstream `Array.qsortOrd`
  * [#5516](https://github.com/leanprover/lean4/pull/5516) upstream `Subarray.empty`
  * [#5526](https://github.com/leanprover/lean4/pull/5526) fix name of `Array.length_toList`
  * [#5527](https://github.com/leanprover/lean4/pull/5527) reduce use of deprecated lemmas in Array
  * [#5534](https://github.com/leanprover/lean4/pull/5534) cleanup of Array GetElem lemmas
  * [#5536](https://github.com/leanprover/lean4/pull/5536) fix `Array.modify` lemmas
  * [#5551](https://github.com/leanprover/lean4/pull/5551) upstream `Array.flatten` lemmas
  * [#5552](https://github.com/leanprover/lean4/pull/5552) switch obvious cases of array "bang"`[]!` indexing to rely on hypothesis (@TomasPuverle)
  * [#5577](https://github.com/leanprover/lean4/pull/5577) add missing simp to `Array.size_feraseIdx`
  * [#5586](https://github.com/leanprover/lean4/pull/5586) `Array/Option.unattach`

* `Option`
  * [#5272](https://github.com/leanprover/lean4/pull/5272) remove @[simp] from `Option.pmap/pbind` and add simp lemmas
  * [#5307](https://github.com/leanprover/lean4/pull/5307) restoring Option simp confluence
  * [#5354](https://github.com/leanprover/lean4/pull/5354) remove @[simp] from `Option.bind_map`
  * [#5532](https://github.com/leanprover/lean4/pull/5532) `Option.attach`
  * [#5539](https://github.com/leanprover/lean4/pull/5539) fix explicitness of `Option.mem_toList`

* `Nat`
  * [#5241](https://github.com/leanprover/lean4/pull/5241) add @[simp] to `Nat.add_eq_zero_iff`
  * [#5261](https://github.com/leanprover/lean4/pull/5261) Nat bitwise lemmas
  * [#5262](https://github.com/leanprover/lean4/pull/5262) `Nat.testBit_add_one` should not be a global simp lemma
  * [#5267](https://github.com/leanprover/lean4/pull/5267) protect some Nat bitwise theorems
  * [#5305](https://github.com/leanprover/lean4/pull/5305) rename Nat bitwise lemmas
  * [#5306](https://github.com/leanprover/lean4/pull/5306) add `Nat.self_sub_mod` lemma
  * [#5503](https://github.com/leanprover/lean4/pull/5503) restore @[simp] to upstreamed `Nat.lt_off_iff`

* `Int`
  * [#5301](https://github.com/leanprover/lean4/pull/5301) rename `Int.div/mod` to `Int.tdiv/tmod`
  * [#5320](https://github.com/leanprover/lean4/pull/5320) add `ediv_nonneg_of_nonpos_of_nonpos` to DivModLemmas (@sakehl)

* `Fin`
  * [#5250](https://github.com/leanprover/lean4/pull/5250) missing lemma about `Fin.ofNat'`
  * [#5356](https://github.com/leanprover/lean4/pull/5356) `Fin.ofNat'` uses `NeZero`
  * [#5379](https://github.com/leanprover/lean4/pull/5379) remove some @[simp]s from Fin lemmas
  * [#5380](https://github.com/leanprover/lean4/pull/5380) missing Fin @[simp] lemmas

* `HashMap`
  * [#5244](https://github.com/leanprover/lean4/pull/5244) (`DHashMap`|`HashMap`|`HashSet`).(`getKey?`|`getKey`|`getKey!`|`getKeyD`)
  * [#5362](https://github.com/leanprover/lean4/pull/5362) remove the last use of `Lean.(HashSet|HashMap)`
  * [#5369](https://github.com/leanprover/lean4/pull/5369) `HashSet.ofArray`
  * [#5370](https://github.com/leanprover/lean4/pull/5370) `HashSet.partition`
  * [#5581](https://github.com/leanprover/lean4/pull/5581) `Singleton`/`Insert`/`Union` instances for `HashMap`/`Set`
  * [#5582](https://github.com/leanprover/lean4/pull/5582) `HashSet.all`/`any`
  * [#5590](https://github.com/leanprover/lean4/pull/5590) adding `Insert`/`Singleton`/`Union` instances for `HashMap`/`Set.Raw`
  * [#5591](https://github.com/leanprover/lean4/pull/5591) `HashSet.Raw.all/any`

* `Monads`
  * [#5463](https://github.com/leanprover/lean4/pull/5463) upstream some monad lemmas
  * [#5464](https://github.com/leanprover/lean4/pull/5464) adjust simp attributes on monad lemmas
  * [#5522](https://github.com/leanprover/lean4/pull/5522) more monadic simp lemmas

* Simp lemma cleanup
  * [#5251](https://github.com/leanprover/lean4/pull/5251) remove redundant simp annotations
  * [#5253](https://github.com/leanprover/lean4/pull/5253) remove Int simp lemmas that can't fire
  * [#5254](https://github.com/leanprover/lean4/pull/5254) variables appearing on both sides of an iff should be implicit
  * [#5381](https://github.com/leanprover/lean4/pull/5381) cleaning up redundant simp lemmas


### Compiler, runtime, and FFI

* [#4685](https://github.com/leanprover/lean4/pull/4685) fixes a typo in the C `run_new_frontend` signature
* [#4729](https://github.com/leanprover/lean4/pull/4729) has IR checker suggest using `noncomputable`
* [#5143](https://github.com/leanprover/lean4/pull/5143) adds a shared library for Lake
* [#5437](https://github.com/leanprover/lean4/pull/5437) removes (syntactically) duplicate imports (@euprunin)
* [#5462](https://github.com/leanprover/lean4/pull/5462) updates `src/lake/lakefile.toml` to the adjusted Lake build process
* [#5541](https://github.com/leanprover/lean4/pull/5541) removes new shared libs before build to better support Windows
* [#5558](https://github.com/leanprover/lean4/pull/5558) make `lean.h` compile with MSVC (@kant2002)
* [#5564](https://github.com/leanprover/lean4/pull/5564) removes non-conforming size-0 arrays (@eric-wieser)


### Lake
  * Reservoir build cache. Lake will now attempt to fetch a pre-built copy of the package from Reservoir before building it. This is only enabled for packages in the leanprover or leanprover-community organizations on versions indexed by Reservoir. Users can force Lake to build packages from the source by passing --no-cache on the CLI or by setting the  LAKE_NO_CACHE environment variable to true. [#5486](https://github.com/leanprover/lean4/pull/5486), [#5572](https://github.com/leanprover/lean4/pull/5572), [#5583](https://github.com/leanprover/lean4/pull/5583), [#5600](https://github.com/leanprover/lean4/pull/5600), [#5641](https://github.com/leanprover/lean4/pull/5641), [#5642](https://github.com/leanprover/lean4/pull/5642).
  * [#5504](https://github.com/leanprover/lean4/pull/5504) lake new and lake init now produce TOML configurations by default.
  * [#5878](https://github.com/leanprover/lean4/pull/5878) fixes a serious issue where Lake would delete path dependencies when attempting to cleanup a dependency required with an incorrect name.

  * **Breaking changes**
    * [#5641](https://github.com/leanprover/lean4/pull/5641) A Lake build of target within a package will no longer build a package's dependencies package-level extra target dependencies. At the technical level, a package's extraDep facet no longer transitively builds its dependencies’ extraDep facets (which include their extraDepTargets).

### Documentation fixes

* [#3918](https://github.com/leanprover/lean4/pull/3918) `@[builtin_doc]` attribute (@digama0)
* [#4305](https://github.com/leanprover/lean4/pull/4305) explains the borrow syntax (@eric-wieser)
* [#5349](https://github.com/leanprover/lean4/pull/5349) adds documentation for `groupBy.loop` (@vihdzp)
* [#5473](https://github.com/leanprover/lean4/pull/5473) fixes typo in `BitVec.mul` docstring (@llllvvuu)
* [#5476](https://github.com/leanprover/lean4/pull/5476) fixes typos in `Lean.MetavarContext`
* [#5481](https://github.com/leanprover/lean4/pull/5481) removes mention of `Lean.withSeconds` (@alexkeizer)
* [#5497](https://github.com/leanprover/lean4/pull/5497) updates documentation and tests for `toUIntX` functions (@TomasPuverle)
* [#5087](https://github.com/leanprover/lean4/pull/5087) mentions that `inferType` does not ensure type correctness
* Many fixes to spelling across the doc-strings, (@euprunin): [#5425](https://github.com/leanprover/lean4/pull/5425) [#5426](https://github.com/leanprover/lean4/pull/5426) [#5427](https://github.com/leanprover/lean4/pull/5427) [#5430](https://github.com/leanprover/lean4/pull/5430)  [#5431](https://github.com/leanprover/lean4/pull/5431) [#5434](https://github.com/leanprover/lean4/pull/5434) [#5435](https://github.com/leanprover/lean4/pull/5435) [#5436](https://github.com/leanprover/lean4/pull/5436) [#5438](https://github.com/leanprover/lean4/pull/5438) [#5439](https://github.com/leanprover/lean4/pull/5439) [#5440](https://github.com/leanprover/lean4/pull/5440) [#5599](https://github.com/leanprover/lean4/pull/5599)

### Changes to CI

* [#5343](https://github.com/leanprover/lean4/pull/5343) allows addition of `release-ci` label via comment (@thorimur)
* [#5344](https://github.com/leanprover/lean4/pull/5344) sets check level correctly during workflow (@thorimur)
* [#5444](https://github.com/leanprover/lean4/pull/5444) Mathlib's `lean-pr-testing-NNNN` branches should use Batteries' `lean-pr-testing-NNNN` branches
* [#5489](https://github.com/leanprover/lean4/pull/5489) commit `lake-manifest.json` when updating `lean-pr-testing` branches
* [#5490](https://github.com/leanprover/lean4/pull/5490) use separate secrets for commenting and branching in `pr-release.yml`

```
