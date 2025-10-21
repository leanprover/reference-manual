/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.25.0-rc1 (2025-10-20)" =>
%%%
tag := "release-v4.25.0"
file := "v4.25.0"
%%%

````markdown
For this release, 398 changes landed. In addition to the 141 feature additions and 83 fixes listed below there were 21 refactoring changes, 9 documentation improvements, 4 performance improvements, 5 improvements to the test suite and 135 other changes.

## Language

* [#7844](https://github.com/leanprover/lean4/pull/7844) adds a simple implementation of MePo, from "Lightweight
  relevance filtering for machine-generated resolution problems" by Meng
  and Paulson.

* [#10158](https://github.com/leanprover/lean4/pull/10158) adds information about definitions blocked from unfolding via
  the module system to type defeq errors.

* [#10268](https://github.com/leanprover/lean4/pull/10268) adds an alternative implementation of `DerivingBEq` based on
  comparing `.ctorIdx` and using a dedicated matcher for comparing same
  constructors (added in #10152), to avoid the quadratic overhead of the
  default match implementation. The new option
  `deriving.beq.linear_construction_threshold` sets the constructor count
  threshold (10 by default) for using the new construction. Such instances
  also allow `deriving ReflBEq, LawfulBeq`, although these proofs for
  these properties are still quadratic.

* [#10270](https://github.com/leanprover/lean4/pull/10270) adds an alternative implementation of `Deriving Ord` based on
  comparing `.ctorIdx` and using a dedicated matcher for comparing same
  constructors (added in #10152). The new option
  `deriving.ord.linear_construction_threshold` sets the constructor count
  threshold (10 by default) for using the new construction.

* [#10302](https://github.com/leanprover/lean4/pull/10302) introduces the `@[specs]` attribute. It can be applied to
  (certain) type class instances and define “specification theorems” for
  the class’ operations, by taking the equational theorems of the
  implementation function mentioned in the type class instance and
  rephrasing them in terms of the overloaded operations. Fixes #5295.

* [#10333](https://github.com/leanprover/lean4/pull/10333) introduces a `coinductive` keyword, that can be used to define
  coinductive predicates via a syntax identical to the one for `inductive`
  keyword. The machinery relies on the implementation of elaboration of
  inductive types and extracts an endomap on the appropriate space of the
  predicates from the definition that is then fed to the
  `PartialFixpoint`. Upon elaborating definitions, all the constructors
  are declared through automatically generated lemmas.

* [#10346](https://github.com/leanprover/lean4/pull/10346) lets `deriving BEq` and `deriving Ord` use `@[method_specs]`
  from #10302 when applicable (i.e. when not using `partial`).

* [#10351](https://github.com/leanprover/lean4/pull/10351) adds the ability to do `deriving ReflBEq, LawfulBEq`. Both
  classes have to listed in the `deriving` clause. For `ReflBEq`, a simple
  `simp`-based proof is used. For `LawfulBEq`, a dedicated,
  syntax-directed tactic is used that should work for derived `BEq`
  instances. This is meant to work with `deriving BEq` (but you can try to
  use it on hand-rolled `@[methods_specs] instance : BEq…` instances).
  Does not support mutual or nested inductives.

* [#10375](https://github.com/leanprover/lean4/pull/10375) adds support for non-commutative ring normalization in `grind`.
  The new normalizer also accounts for the `IsCharP` type class. Examples:
  ```lean
  open Lean Grind

  variable (R : Type u) [Ring R]
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + -b * (-4) * a - 2*b*a + 4 * b^2 := by grind

  variable [IsCharP R 4]
  example (a b : R) : (a - b)^2 = a^2 - a * b - b * 5 * a + b^2 := by grind
  example (a b : R) : (a - b)^2 = 13*a^2 - a * b - b * 5 * a + b*3*b*3 := by grind
  ```

* [#10377](https://github.com/leanprover/lean4/pull/10377) fixes an issue where the "eta feature" in the app elaborator,
  which is invoked when positional arguments are skipped due to named
  arguments, results in variables that can be captured by those named
  arguments. Now the temporary local variables that implement this feature
  get fresh names. The names used for the closed lambda expression still
  use the original parameter names.

* [#10378](https://github.com/leanprover/lean4/pull/10378) enables using `notation` items in
  `infix`/`infixl`/`infixr`/`prefix`/`postfix`. The motivation for this is
  to enable being able to use `pp.unicode`-aware parsers. A followup PR
  can combine core parsers as such:
  ```lean
  infixr:30 unicode(" ∨ ", " \\/ ") => Or
  ```

* [#10379](https://github.com/leanprover/lean4/pull/10379) modifies the syntax for tactic configurations. Previously just
  `(ident` would commit to tactic configuration item parsing, but now it
  needs to be `(ident :=`. This enables reliably using tactic
  configurations before the `term` category. For example, given `syntax
  "my_tac" optConfig term : tactic`, it used to be that `my_tac (x + y)`
  would have an error on `+` with "expected `:=`", but now it parses the
  term.

* [#10380](https://github.com/leanprover/lean4/pull/10380) implements sanity checks in the `grind ring` module to ensure
  the instances synthesized by type class resolution are definitionally
  equal to the corresponding ones in the `grind` core classes. The
  definitional equality test is performed with reduction restricted to
  reducible definitions and instances.

* [#10382](https://github.com/leanprover/lean4/pull/10382) makes the builtin Verso docstring elaborators bootstrap
  correctly, adds the ability to postpone checks (which is necessary for
  resolving forward references and bootstrapping issues), and fixes a
  minor parser bug.

* [#10388](https://github.com/leanprover/lean4/pull/10388) fixes a bug where definitions with nested proofs that contain
  `sorry` might not report "warning: declaration uses 'sorry'" if the
  proof has the same type as another nested proof from a previous
  declaration. The bug only affected log messages; `#print axioms` would
  still correctly report uses of `sorryAx`.

* [#10391](https://github.com/leanprover/lean4/pull/10391) gives anonymous constructor notation (`⟨x,y⟩`) an error recovery
  mechanism where if there are not enough arguments then synthetic sorries
  are inserted for the missing arguments and an error is logged, rather
  than outright failing.

* [#10392](https://github.com/leanprover/lean4/pull/10392) fixes an issue with the `if` tactic where errors were not placed
  at the correct source ranges. It also adds some error recovery to avoid
  additional errors about unsolved goals on the `if` token when the tactic
  has incomplete syntax.

* [#10394](https://github.com/leanprover/lean4/pull/10394) adds the `reduceBEq` and `reduceOrd` simprocs. They rewrite
  occurrences of `_ == _` resp. `Ord.compare _ _` if both arguments are
  constructors and the corresponding instance has been marked with
  `@[method_specs]` (introduced in #10302), which now by default is the
  case for derived instances.

* [#10406](https://github.com/leanprover/lean4/pull/10406) improves upon #10302 to properly make the method spec theorems
  private if the implementation function is not exposed.

* [#10415](https://github.com/leanprover/lean4/pull/10415) changes the order of steps tried when proving equational
  theorems for structural recursion. In order to avoid goals that `split`
  cannot handle, avoid unfolding the LHS of the equation to `.brecOn` and
  `.rec` until after the RHS has been split into its final cases.

* [#10417](https://github.com/leanprover/lean4/pull/10417) changes the automation in `deriving_LawfulEq_tactic_step` to use
  `with_reducible` when asserting the shape of the goal using `change`, so
  that we do not accidentally unfold `x == x'` calls here. Fixes #10416.

* [#10419](https://github.com/leanprover/lean4/pull/10419) adds the helper theorem `eq_normS_nc` for normalizing
  non-commutative semirings. We will use this theorem to justify
  normalization steps in the `grind ring` module.

* [#10421](https://github.com/leanprover/lean4/pull/10421) adds a normalizer for non-commutative semirings to `grind`.
  Examples:
  ```lean
  open Lean.Grind
  variable (R : Type u) [Semiring R]

  example (a b c : R) : a * (b + c) = a * c + a * b := by grind
  example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
  example (a b : R) : b^2 + (a + 2 * b)^2 = a^2 + 2 * a * b + b * (1+1) * a * 1 + 5 * b^2 := by grind
  example (a b : R) : a^3 + a^2*b + a*b*a + b*a^2 + a*b^2 + b*a*b + b^2*a + b^3 = (a+b)^3 := by grind
  ```

* [#10422](https://github.com/leanprover/lean4/pull/10422) implements the new E-matching pattern inference heuristic for
  `grind`. It is not enabled yet. You can activate the new behavior using
  `set_option backward.grind.inferPattern false`. Here is a summary of the
  new behavior.

* [#10425](https://github.com/leanprover/lean4/pull/10425) lets the `split` tactic generalize discriminants that are not
  free variables and proofs using `generalize`. If the only
  non-fvar-discriminants are proofs, then this avoids the more elaborate
  generalization strategy of `split`, which can fail with dependent
  motives, thus mitigating issue #10424.

* [#10428](https://github.com/leanprover/lean4/pull/10428) makes explicit missing `grind` modifiers, and ensures `grind`
  uses "minIndexable" for local theorems.

* [#10430](https://github.com/leanprover/lean4/pull/10430) ensures users can select the "minimal indexable subexpression"
  condition in `grind` parameters. Example, they can now write `grind [!
  -> thmName]`. `grind?` will include the `!` modifier whenever users had
  used `@[grind!]`. also fixes a missing case in the new pattern
  inference procedure.
  It also adjusts some `grind` annotations and tests in preparation for
  setting the new pattern inference heuristic as the new default.

* [#10432](https://github.com/leanprover/lean4/pull/10432) enables the new E-matching pattern inference heuristic for
  `grind`, implemented in PR #10422.
  **Important**: Users can still use the old pattern inference heuristic
  by setting:

  ```lean
  set_option backward.grind.inferPattern true
  ```

* [#10434](https://github.com/leanprover/lean4/pull/10434) adds `reprove N by T`, which effectively elaborates `example
  type_of% N := by T`. It supports multiple identifiers. This is useful
  for testing tactics.

* [#10438](https://github.com/leanprover/lean4/pull/10438) fixes an issue where notations and other overloadings would
  signal kernel errors even though there exists a successful
  interpretation.

* [#10440](https://github.com/leanprover/lean4/pull/10440) adds the `reduceCtorIdx` simproc which recognizes and reduces
  `ctorIdx` applications. This is not on by default yet because it does
  not use the discrimination tree (yet).

* [#10453](https://github.com/leanprover/lean4/pull/10453) makes `mvcgen` reduce through `let`s, so that it progresses over
  `(have t := 42; fun _ => foo t) 23` by reduction to `have t := 42; foo
  t` and then introducing `t`.

* [#10456](https://github.com/leanprover/lean4/pull/10456) implements `mvcgen invariants?` for providing initial invariant
  skeletons for the user to flesh out. When the loop body has an early
  return, it will helpfully suggest `Invariant.withEarlyReturn ...` as a
  skeleton.

* [#10479](https://github.com/leanprover/lean4/pull/10479) implements module docstrings in Verso syntax, as well as adding
  a number of improvements and fixes to Verso docstrings in general. In
  particular, they now have language server support and are parsed at
  parse time rather than elaboration time, so the snapshot's syntax tree
  includes the parsed documentation.

* [#10506](https://github.com/leanprover/lean4/pull/10506) annotates the shadowing main definitions of `bv_decide`,
  `mvcgen` and similar tactics in `Std` with the semantically richer
  `tactic_alt` attribute so that `verso` will not warn about overloads.

* [#10507](https://github.com/leanprover/lean4/pull/10507) makes the missing docs linter aware of `tactic_alt`.

* [#10508](https://github.com/leanprover/lean4/pull/10508) allows `.congr_simp` theorems to be created not just for
  definitoins, but any constant. This is important to make the machinery
  work across module boundaries.

* [#10512](https://github.com/leanprover/lean4/pull/10512) adds some helper functions for the premise selection API, to
  assist implementers.

* [#10533](https://github.com/leanprover/lean4/pull/10533) adds a docstring role for module names, called `module`. It also
  improves the suggestions provided for code elements, making them more
  relevant and proposing `lit`.

* [#10535](https://github.com/leanprover/lean4/pull/10535) ensures that `#guard` can be called under the module system
  without issues.

* [#10536](https://github.com/leanprover/lean4/pull/10536) fixes `simp` in `-zeta -zetaUnused` mode from producing
  incorrect proofs if in a `have` telescope a variable occurrs in the
  type of the body only transitively. Fixes #10353.

* [#10543](https://github.com/leanprover/lean4/pull/10543) lets `#print T.rec` show more information about a recursor, in
  particular it's reduction rules.

* [#10560](https://github.com/leanprover/lean4/pull/10560) adds highlighted Lean code to Verso docstrings and fixes smaller
  quality-of-life issues.

* [#10563](https://github.com/leanprover/lean4/pull/10563) moves some `ReduceEval` instances about basic types up from the
  `quote4` library.

* [#10566](https://github.com/leanprover/lean4/pull/10566) improves `mvcgen invariants?` to suggest concrete invariants
  based on how invariants are used in VCs.
  These suggestions are intentionally simplistic and boil down to "this
  holds at the start of the loop and this must hold at the end of the
  loop":

  ```lean
  def mySum (l : List Nat) : Nat := Id.run do
    let mut acc := 0
    for x in l do
      acc := acc + x
    return acc

  /--
  info: Try this:
    invariants
      · ⇓⟨xs, letMuts⟩ => ⌜xs.prefix = [] ∧ letMuts = 0 ∨ xs.suffix = [] ∧ letMuts = l.sum⌝
  -/
  #guard_msgs (info) in
  theorem mySum_suggest_invariant (l : List Nat) : mySum l = l.sum := by
    generalize h : mySum l = r
    apply Id.of_wp_run_eq h
    mvcgen invariants?
    all_goals admit
  ```

* [#10567](https://github.com/leanprover/lean4/pull/10567) fixes argument index calculation in `Lean.Expr.getArg!'`.

* [#10570](https://github.com/leanprover/lean4/pull/10570) adds support for case label like syntax in `mvcgen invariants`
  in order to refer to inaccessible names. Example:

  ```lean
  def copy (l : List Nat) : Id (Array Nat) := do
    let mut acc := #[]
    for x in l do
      acc := acc.push x
    return acc

  theorem copy_labelled_invariants (l : List Nat) : ⦃⌜True⌝⦄ copy l ⦃⇓ r => ⌜r = l.toArray⌝⦄ := by
    mvcgen [copy] invariants
    | inv1 acc => ⇓ ⟨xs, letMuts⟩ => ⌜acc = l.toArray⌝
    with admit
  ```

* [#10571](https://github.com/leanprover/lean4/pull/10571) ensures that `SPred` proof mode tactics such as `mspec`,
  `mintro`, etc. immediately replace the main goal when entering the proof
  mode. This prevents `No goals to be solved` errors.

* [#10612](https://github.com/leanprover/lean4/pull/10612) fixes an issue reported [on
  Zulip](https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/.60abstractMVars.60.20not.20instantiating.20level.20mvars/near/541918246)
  where `abstractMVars` (which is used in typeclass inference and `simp`
  argument elaboration) was not instantiating metavariables in the types
  of metavariables, causing it to abstract already-assigned metavariables.

* [#10618](https://github.com/leanprover/lean4/pull/10618) removes superfluous `Monad` instances from the spec lemmas of
  the `MonadExceptOf` lifting framework.

* [#10638](https://github.com/leanprover/lean4/pull/10638) disables the "experimental" warning for `mvcgen` by changing its
  default.

* [#10639](https://github.com/leanprover/lean4/pull/10639) fixes hygiene of the local context for *all* goals generated by
  `mvcgen`, not just those that get a fresh MVar as in #9781.

* [#10641](https://github.com/leanprover/lean4/pull/10641) ensures that the `mspec` and `mvcgen` tactics no longer
  spuriously instantiate loop invariants by `rfl`.

* [#10644](https://github.com/leanprover/lean4/pull/10644) explicitly tries to synthesize synthetic MVars in `mspec`. Doing
  so resolves a bug triggered by use of the loop invariant lemma for
  `Std.PRange`.

* [#10650](https://github.com/leanprover/lean4/pull/10650) improves the error message for `mstart` when the goal is not a
  `Prop`.

* [#10654](https://github.com/leanprover/lean4/pull/10654) avoid reducing at transparency all in equational theorem
  generation. Fixes #10651.

* [#10663](https://github.com/leanprover/lean4/pull/10663) disables `{name}` suggestions for `.anonymous` and adds syntax
  suggestions.

* [#10682](https://github.com/leanprover/lean4/pull/10682) changes the instance name for `deriving ToExpr` to be consistent
  with other derived instance since #10271. Fixes #10678.

* [#10697](https://github.com/leanprover/lean4/pull/10697) lets `induction` print a warning if a variable occurring in the
  `using` clause is generalized. Fixes #10683.

* [#10712](https://github.com/leanprover/lean4/pull/10712) lets `MVarId.cleanup` chase local declarations (a bit as if they
  were equalities). Fixes #10710.

* [#10714](https://github.com/leanprover/lean4/pull/10714) removes support for reducible well-founded recursion, a Breaking
  Change. Using `@[semireducible]` on a definition by well-founded
  recursion prints a warning that this is no longer effective.

* [#10716](https://github.com/leanprover/lean4/pull/10716) adds a new helper parser for implementing parsers that contain
  hexadecimal numbers. We are going to use it to implement anchors in the
  `grind` interactive mode.

* [#10720](https://github.com/leanprover/lean4/pull/10720) re-enables the "experimental" warning for `mvcgen` by changing
  its default. The official release has been postponed to justify small
  breaking changes in the semantic foundations in the near future.

* [#10722](https://github.com/leanprover/lean4/pull/10722) changes where errors are displayed when trying to use
  `coinductive` keyword when targeting things that do not live in `Prop`.
  Instead of displaying the error above the first element of the mutual
  block, it is displayed above the erroneous definition.

* [#10733](https://github.com/leanprover/lean4/pull/10733) unfolds auxillary theorems more aggressively during termination
  checking. This fixes #10721.

* [#10734](https://github.com/leanprover/lean4/pull/10734) follows upon #10606 and creates equational theorems uniformly
  from the unfold theorem, there is only one handler registered in
  `registerGetEqnsFn`.

* [#10780](https://github.com/leanprover/lean4/pull/10780) improves the error message when `decide +kernel` fails in the
  kernel, but not the elaborator. Fixes #10766.

* [#10782](https://github.com/leanprover/lean4/pull/10782) implements a hint tactic `mvcgen?`, expanding to `mvcgen
  invariants?`

* [#10783](https://github.com/leanprover/lean4/pull/10783) ensures that error messages such as “redundant alternative” have
  the right error location even if the arms share their RHS. Fixes #10781.

* [#10793](https://github.com/leanprover/lean4/pull/10793) fixes #10792.

* [#10796](https://github.com/leanprover/lean4/pull/10796) changes match compilation to reject some pattern matches that
  were previously accepted due to inaccessible patterns sometimes treated
  like accessible ones. Fixes #10794.

* [#10807](https://github.com/leanprover/lean4/pull/10807) introduces the `backward.privateInPublic` option to aid in
  porting projects to the module system by temporarily allowing access to
  private declarations from the public scope, even across modules. A
  warning will be generated by such accesses unless
  `backward.privateInPublic.warn` is disabled.

* [#10839](https://github.com/leanprover/lean4/pull/10839) exposes the `optionValue` parser used to implement the
  `set_option` notation.

## Library

* [#9258](https://github.com/leanprover/lean4/pull/9258) adds support for signal handlers to the Lean standard library.

* [#9298](https://github.com/leanprover/lean4/pull/9298) adds support the Count Trailing Zeros operation `BitVec.ctz` to
  the bitvector library and to `bv_decide`, relying on the existing `clz`
  circuit. We also build some theory around `BitVec.ctz` (analogous to the
  theory existing for `BitVec.clz`) and introduce lemmas
  `BitVec.[ctz_eq_reverse_clz, clz_eq_reverse_ctz, ctz_lt_iff_ne_zero,
  getLsbD_false_of_lt_ctz, getLsbD_true_ctz_of_ne_zero,
  two_pow_ctz_le_toNat_of_ne_zero, reverse_reverse_eq,
  reverse_eq_zero_iff]`.

* [#9932](https://github.com/leanprover/lean4/pull/9932) adds `LawfulMonad` and `WPMonad` instances for `Option` and
  `OptionT`.

* [#10304](https://github.com/leanprover/lean4/pull/10304) redefines `String` to be the type of byte arrays `b` for which
  `b.IsValidUtf8`.

* [#10319](https://github.com/leanprover/lean4/pull/10319) "monomorphizes" the structure `Std.PRange shape α`, replacing it
  with nine distinct structures `Std.Rcc`, `Std.Rco`, `Std.Rci` etc., one
  for each possible shape of a range's bounds. This change was necessary
  because the shape polymorphism is detrimental to attempts of automation.

* [#10366](https://github.com/leanprover/lean4/pull/10366) refactors the Async module to use the `Async` type in all of the
  `Async` files.

* [#10367](https://github.com/leanprover/lean4/pull/10367) adds vectored write for TCP and UDP (that helps a lot with not
  copying the arrays over and over) and fix a RC issue in TCP and UDP
  cancel functions with the line `lean_dec((lean_object*)udp_socket);` and
  a similar one that tries to decrement the object inside of the `socket`.

* [#10368](https://github.com/leanprover/lean4/pull/10368) adds `Notify` that is a structure that is similar to `CondVar`
  but it's used for concurrency. The main difference between
  `Std.Sync.Notify` and `Std.Condvar` is that depends on a `Std.Mutex` and
  blocks the entire thread that the `Task` is using while waiting.

* [#10369](https://github.com/leanprover/lean4/pull/10369) adds a multi-consumer, multi-producer channel to Std.Sync.

* [#10370](https://github.com/leanprover/lean4/pull/10370) adds async type classes for streams.

* [#10400](https://github.com/leanprover/lean4/pull/10400) adds the StreamMap type that enables multiplexing in
  asynchronous streams.

* [#10407](https://github.com/leanprover/lean4/pull/10407) adds `@[method_specs_simp]` in `Init` for type classes like
  `HAppend`.

* [#10457](https://github.com/leanprover/lean4/pull/10457) introduces safe alternatives to `String.Pos` and `Substring`
  that can only represent valid positions/slices.

* [#10487](https://github.com/leanprover/lean4/pull/10487) adds vectored write and fix rc issues in tcp and udp cancel
  functions.

* [#10510](https://github.com/leanprover/lean4/pull/10510) adds a `Std.CancellationToken` type

* [#10514](https://github.com/leanprover/lean4/pull/10514) defines the new `String.Slice` API.

* [#10552](https://github.com/leanprover/lean4/pull/10552) ensures that `Substring.beq` is reflexive, and in particular
  satisfies the equivalence `ss1 == ss2 <-> ss1.toString = ss2.toString`.

* [#10611](https://github.com/leanprover/lean4/pull/10611) adds adds union operation on `DHashMap`/`HashMap`/`HashSet` and
  their raw variants and provides lemmas about union operations.

* [#10618](https://github.com/leanprover/lean4/pull/10618) removes superfluous `Monad` instances from the spec lemmas of
  the `MonadExceptOf` lifting framework.

* [#10624](https://github.com/leanprover/lean4/pull/10624) renames `String.Pos` to `String.Pos.Raw`.

* [#10627](https://github.com/leanprover/lean4/pull/10627) adds lemmas `forall_fin_zero` and `exists_fin_zero`. It also
  marks lemmas `forall_fin_zero`, `forall_fin_one`, `forall_fin_two`,
  `exists_fin_zero`, `exists_fin_one`, `exists_fin_two` with `simp`
  attribute.

* [#10630](https://github.com/leanprover/lean4/pull/10630) aims to fix the Timer API selector to make it finish as soon as
  possible when unregistered. This change makes the `Selectable.one`
  function drop the `selectables` array as soon as possible, so when
  combined with finalizers that have some effects like the TCP socket
  finalizer, it runs it as soon as possible.

* [#10631](https://github.com/leanprover/lean4/pull/10631) exposes the definitions about `Int*`. The main reason is that
  the `SInt` simprocs require many of them to be exposed. Furthermore,
  `decide` now works with `Int*` operations. This fixes #10631.

* [#10633](https://github.com/leanprover/lean4/pull/10633) provides range support for the signed finite number types
  `Int{8,16,32,64}` and `ISize`. The proof obligations are handled by
  reducing all of them to proofs about an internal `UpwardEnumerable`
  instance for `BitVec` interpreted as signed numbers.

* [#10634](https://github.com/leanprover/lean4/pull/10634) defines `ByteArray.validateUTF8`, uses it to show that
  `ByteArray.IsValidUtf8` is decidable and redefines `String.fromUTF8` and
  friends to use it.

* [#10636](https://github.com/leanprover/lean4/pull/10636) renames `String.getUtf8Byte` to `String.getUTF8Byte` in order to
  adhere to the standard library naming convention.

* [#10642](https://github.com/leanprover/lean4/pull/10642) introduces `List.Cursor.pos` as an abbreviation for
  `prefix.length`.

* [#10645](https://github.com/leanprover/lean4/pull/10645) renames `Stream` to `Std.Stream` so that the name becomes
  available to mathlib after a deprecation cycle.

* [#10649](https://github.com/leanprover/lean4/pull/10649) renames `Nat.and_distrib_right` to `Nat.and_or_distrib_right`.
  This is to make the name consistent with other theorems in the same file
  (e.g. `Nat.and_or_distrib_left`).

* [#10653](https://github.com/leanprover/lean4/pull/10653) adds equational lemmas about (filter-)mapping and then folding
  iterators.

* [#10667](https://github.com/leanprover/lean4/pull/10667) adds more selectors for TCP and Signals.

* [#10676](https://github.com/leanprover/lean4/pull/10676) adds the `IO.FS.hardLink` function, which can be used to create
  hard links.

* [#10685](https://github.com/leanprover/lean4/pull/10685) introduces `LT` and `LE` instances on `String.ValidPos` and
  `String.Slice.Pos`.

* [#10686](https://github.com/leanprover/lean4/pull/10686) introduces `any`, `anyM`, `all` and `allM` for pure and monadic
  iterators. It also provides lemmas about them.

* [#10713](https://github.com/leanprover/lean4/pull/10713) enforces rules around arithmetic of `String.Pos.Raw`.

* [#10728](https://github.com/leanprover/lean4/pull/10728) introduces the `flatMap` iterator combinator. It also adds
  lemmas relating `flatMap` to `toList` and `toArray`.

* [#10735](https://github.com/leanprover/lean4/pull/10735) moves many operations involving `String.Pos.Raw` to a the
  `String.Pos.Raw` namespace with the eventual aim of freeing up the
  `String` namespace to contain operations using `String.ValidPos` (to be
  renamed to `String.Pos`) instead.

* [#10761](https://github.com/leanprover/lean4/pull/10761) provides iterators on hash maps.

````

```markdown

## Tactics

* [#10445](https://github.com/leanprover/lean4/pull/10445) adds helper definitions in preparation for the upcoming
  injective function support in `grind`.

* [#10447](https://github.com/leanprover/lean4/pull/10447) adds the `[grind inj]` attribute for marking injectivity
  theorems for `grind`.

* [#10448](https://github.com/leanprover/lean4/pull/10448) modifies the "issues" grind diagnostics prints. Previously we
  would just describe synthesis failures. These messages were confusing to
  users, as in fact the linarith module continues to work, but less
  capably. For most of the issues, we now explain the resulting change in
  behaviour. There is a still a TODO to explain the change when
  `IsOrderedRing` is not available.

* [#10449](https://github.com/leanprover/lean4/pull/10449) ensures that issues reported by the E-matching module are
  displayed only when `set_option grind.debug true` is enabled. Users
  reported that these messages are too distracting and not very useful.
  They are more valuable for library developers when annotating their
  libraries.

* [#10461](https://github.com/leanprover/lean4/pull/10461) fixes unnecessary case splits generated by the `grind mbtc`
  module. Here, `mbtc` stands for model-based theory combination.

* [#10463](https://github.com/leanprover/lean4/pull/10463) adds `Nat.sub_zero` as a `grind` normalization rule.

* [#10465](https://github.com/leanprover/lean4/pull/10465) skips cast-like helper `grind` functions during `grind mbtc`

* [#10466](https://github.com/leanprover/lean4/pull/10466) reduces noise in the 'Equivalence classes' section of the
  `grind` diagnostics. It now uses a notion of *support expressions*.
  Right now, it is hard-coded, but we will probably make it extensible in
  the future. The current definition is

* [#10469](https://github.com/leanprover/lean4/pull/10469) fixes an incorrect optimization in the `grind` canonicalizer.
  See the new test for an example that exposes the problem.

* [#10472](https://github.com/leanprover/lean4/pull/10472) adds a code action for `grind` parameters. We need to use
  `set_option grind.param.codeAction true` to enable the option. The PR
  also adds a modifier to instruct `grind` to use the "default" pattern
  inference strategy.

* [#10473](https://github.com/leanprover/lean4/pull/10473) ensures the code action messages produced by `grind` include the
  full context

* [#10474](https://github.com/leanprover/lean4/pull/10474) adds a doc string for the `!` parameter modifier in `grind`.

* [#10477](https://github.com/leanprover/lean4/pull/10477) ensures sorts are internalized by `grind`.

* [#10480](https://github.com/leanprover/lean4/pull/10480) fixes a bug in the equality resolution frontend used in `grind`.

* [#10481](https://github.com/leanprover/lean4/pull/10481) generalizes the theorem activation function used in `grind`.
  The goal is to reuse it to implement the injective function module.

* [#10482](https://github.com/leanprover/lean4/pull/10482) fixes symbol collection for the `@[grind inj]` attribute.

```

````markdown

* [#10483](https://github.com/leanprover/lean4/pull/10483) completes support for injective functions in grind. See
  examples:
  ```lean
  /-! Add some injectivity theorems. -/

  def double (x : Nat) := 2*x

  @[grind inj] theorem double_inj : Function.Injective double := by
    grind [Function.Injective, double]

  structure InjFn (α : Type) (β : Type) where
    f : α → β
    h : Function.Injective f

  instance : CoeFun (InjFn α β) (fun _ => α → β) where
    coe s := s.f

  @[grind inj] theorem fn_inj (F : InjFn α β) : Function.Injective (F : α → β) := by
    grind [Function.Injective, cases InjFn]

  def toList (a : α) : List α := [a]

  @[grind inj] theorem toList_inj : Function.Injective (toList : α → List α) := by
    grind [Function.Injective, toList]

  /-! Examples -/

  example (x y : Nat) : toList (double x) = toList (double y) → x = y := by
    grind

  example (f : InjFn (List Nat) α) (x y z : Nat)
      : f (toList (double x)) = f (toList y) →
        y = double z →
        x = z := by
    grind
  ```

* [#10486](https://github.com/leanprover/lean4/pull/10486) adds and expands `grind` related docstrings.

* [#10529](https://github.com/leanprover/lean4/pull/10529) adds some helper theorems for the upcoming `grind order` solver.

* [#10553](https://github.com/leanprover/lean4/pull/10553) implements infrastructure for the new `grind order` module.

* [#10562](https://github.com/leanprover/lean4/pull/10562) simplifies the `grind order` module, and internalizes the order
  constraints. It removes the `Offset` type class because it introduced
  too much complexity. We now cover the same use cases with a simpler
  approach:
  - Any type that implements at least `Std.IsPreorder`
  - Arbitrary ordered rings.
  - `Nat` by the `Nat.ToInt` adapter.

* [#10583](https://github.com/leanprover/lean4/pull/10583) allows users to declare additional `grind` constraint
  propagators for declarations that already include propagators in core.

* [#10589](https://github.com/leanprover/lean4/pull/10589) adds helper theorems for implementing  `grind order`

* [#10590](https://github.com/leanprover/lean4/pull/10590) implements proof term construction for `grind order`.

* [#10594](https://github.com/leanprover/lean4/pull/10594) implements proof construction for theory propagation in `grind
  order`.

* [#10596](https://github.com/leanprover/lean4/pull/10596) implements the function for adding new edges to the graph used
  by `grind order`. The graph maintains the transitive closure of all
  asserted constraints.

* [#10598](https://github.com/leanprover/lean4/pull/10598) implements support for positive constraints in `grind order`.
  The new module can already solve problems such as:

  ```lean
  example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
      (a b c : α) : a ≤ b → b ≤ c → c < a → False := by
    grind

  example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
      (a b c d : α) : a ≤ b → b ≤ c → c < d → d ≤ a → False := by
    grind

  example [LE α] [Std.IsPreorder α]
      (a b c : α) : a ≤ b → b ≤ c → a ≤ c := by
    grind

  example [LE α] [Std.IsPreorder α]
      (a b c d : α) : a ≤ b → b ≤ c → c ≤ d → a ≤ d := by
    grind
  ```

* [#10599](https://github.com/leanprover/lean4/pull/10599) fixes the support for `Nat` in `grind order`. This module uses
  the `Nat.ToInt` adapter.

* [#10600](https://github.com/leanprover/lean4/pull/10600) implements support for negative constraints in `grind order`.
  Examples:

  ```lean
  open Lean Grind
  example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α]
      (a b c d : α) : a ≤ b → ¬ (c ≤ b) → ¬ (d ≤ c) → d < a → False := by
    grind -linarith (splits := 0)

  example [LE α] [Std.IsLinearPreorder α]
      (a b c d : α) : a ≤ b → ¬ (c ≤ b) → ¬ (d ≤ c) → ¬ (a ≤ d) → False := by
    grind -linarith (splits := 0)

  example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] [CommRing α] [OrderedRing α]
      (a b c d : α) : a - b ≤ 5 → ¬ (c ≤ b) → ¬ (d ≤ c + 2) → d ≤ a - 8 → False := by
    grind -linarith (splits := 0)
  ```

* [#10601](https://github.com/leanprover/lean4/pull/10601) fixes a panic in `grind order` when order is not a partial
  order.

* [#10604](https://github.com/leanprover/lean4/pull/10604) implements the method `processNewEq` in `grind order`. It is
  responsible for processing equalities propagated by the `grind` E-graph.

````

````markdown

* [#10607](https://github.com/leanprover/lean4/pull/10607) adds infrastructure for the upcoming `grind` tactic mode, which
  will be similar to the `conv` mode. The goal is to extend `grind` from a
  terminal tactic into an interactive mode: `grind => …`.

* [#10677](https://github.com/leanprover/lean4/pull/10677) implements the basic tactics for the new `grind` interactive
  mode. While many additional `grind` tactics will be added later, the
  foundational framework is already operational. The following `grind`
  tactics are currently implemented: `skip`, `done`, `finish`, `lia`, and
  `ring`.
  also removes the notion of `grind` fallback procedure since it
  is subsumed by the new framework. Examples:
  ```lean
  example (x y : Nat) : x ≥ y + 1 → x > 0 := by
    grind => skip; lia; done
  ```

* [#10679](https://github.com/leanprover/lean4/pull/10679) fixes an issue where "Invalid alternative name" errors from
  `induction` stick around after removing the offending alternative.

* [#10690](https://github.com/leanprover/lean4/pull/10690) adds the `instantiate`, `show_true`, `show_false`,
  `show_asserted`, and `show_eqcs` tactics for the `grind` interactive
  mode. The `show` tactic take an optional "filter" and are used to probe
  the `grind` state. Example:
  ```lean
  example (as bs cs : Array α) (v₁ v₂ : α)
          (i₁ i₂ j : Nat)
          (h₁ : i₁ < as.size)
          (h₂ : bs = as.set i₁ v₁)
          (h₃ : i₂ < bs.size)
          (h₃ : cs = bs.set i₂ v₂)
          (h₄ : i₁ ≠ j ∧ i₂ ≠ j)
          (h₅ : j < cs.size)
          (h₆ : j < as.size)
          : cs[j] = as[j] := by
    grind =>
      instantiate
      -- Display asserted facts with `generation > 0`
      show_asserted gen > 0
      -- Display propositions known to be `True`, containing `j`, and `generation > 0`
      show_true j && gen > 0
      -- Display equivalence classes with terms that contain `as` or `bs`
      show_eqcs as || bs
      instantiate
  ```

* [#10695](https://github.com/leanprover/lean4/pull/10695) fixes an issue where non-`macro` members of a `mutual` block
  were discarded if there was at least one macro present.

* [#10706](https://github.com/leanprover/lean4/pull/10706) adds the `have` tactic for the `grind` interactive mode.
  Example:
  ```lean
  example {a b c d e : Nat}
      : a > 0 → b > 0 → 2*c + e <= 2 → e = d + 1 → a*b + 2 > 2*c + d := by
    grind =>
      have : a*b > 0 := Nat.mul_pos h h_1
      lia
  ```

* [#10707](https://github.com/leanprover/lean4/pull/10707) ensures the `finish` tactic in `grind` interactive mode fails
  and reports diagnostics when goal is not closed.

* [#10709](https://github.com/leanprover/lean4/pull/10709) implements *anchors* (also known as stable hash codes) for
  referencing terms occurring in a `grind` goal. It also introduces the
  commands `show_splits` and `show_state`. The former displays the anchors
  for candidate case splits in the current `grind` goal.

* [#10715](https://github.com/leanprover/lean4/pull/10715) improves anchor stability (aka stable hash codes) used to
  reference terms in a `grind` goal.

````

````markdown

* [#10731](https://github.com/leanprover/lean4/pull/10731) adds the following tactics to the `grind` interactive mode:
  - `focus <grind_tac_seq>`
  - `next => <grind_tac_seq>`
  - `any_goals <grind_tac_seq>`
  - `all_goals <grind_tac_seq>`
  - `grind_tac <;> grind_tac`
  - `cases <anchor>`
  - `tactic => <tac_seq>`

* [#10737](https://github.com/leanprover/lean4/pull/10737) adds the tactics `linarith`, `ac`, `fail`, `first`, `try`,
  `fail_if_success`, and `admit` to `grind` interactive mode.

* [#10740](https://github.com/leanprover/lean4/pull/10740) improves the tactics `ac`, `linarith`, `lia`, `ring` tactics in
  `grind` interactive mode. They now fail if no progress has been made.
  They also generate an info message with counterexample/basis if the goal
  was not closed.

* [#10746](https://github.com/leanprover/lean4/pull/10746) implements parameters for the `instantiate` tactic in the
  `grind` interactive mode. Users can now select both global and local
  theorems. Local theorems are selected using anchors. It also adds the
  `show_thms` tactic for displaying local theorems. Example:

  ```lean
  example (as bs cs : Array α) (v₁ v₂ : α)
          (i₁ i₂ j : Nat)
          (h₁ : i₁ < as.size)
          (h₂ : bs = as.set i₁ v₁)
          (h₃ : i₂ < bs.size)
          (h₃ : cs = bs.set i₂ v₂)
          (h₄ : i₁ ≠ j ∧ i₂ ≠ j)
          (h₅ : j < cs.size)
          (h₆ : j < as.size)
          : cs[j] = as[j] := by
    grind =>
      instantiate = Array.getElem_set
      instantiate Array.getElem_set
  ```

````

```markdown

* [#10747](https://github.com/leanprover/lean4/pull/10747) implements infrastructure for `finish?` and `grind?` tactics.

* [#10748](https://github.com/leanprover/lean4/pull/10748) implements the `repeat` tactical for the `grind` interactive
  mode.

* [#10767](https://github.com/leanprover/lean4/pull/10767) implements the new control interface for implementing `grind`
  search strategies. It will replace the `SearchM` framework.

* [#10778](https://github.com/leanprover/lean4/pull/10778) ensures that `grind` interactive mode is hygienic. It also adds
  tactics for renaming inaccessible names: `rename_i h_1 ... h_n` and
  `next h_1 ... h_n => ..`, and `expose_names` for automatically generated
  tactic scripts. The PR also adds helper functions for implementing
  case-split actions.

* [#10779](https://github.com/leanprover/lean4/pull/10779) implements hover information for `grind` anchors. Anchors are
  stable hash codes for referencing terms in the grind state. The anchors
  will be used when auto generating tactic scripts.

* [#10791](https://github.com/leanprover/lean4/pull/10791) adds a silent info message with the `grind` state in its
  interactive mode. The message is shown only when there is exactly one
  goal in the grind interactive mode. The condition is a workaround for
  current limitations of our `InfoTree`.

* [#10798](https://github.com/leanprover/lean4/pull/10798) implements the `grind` actions `intro`, `intros`, `assertNext`,
  `assertAll`.

* [#10801](https://github.com/leanprover/lean4/pull/10801) implements the `splitNext` action for `grind`.

* [#10808](https://github.com/leanprover/lean4/pull/10808) implements support for compressing auto-generated `grind` tactic
  sequences.

```

```markdown

* [#10811](https://github.com/leanprover/lean4/pull/10811) implements proper case-split anchor generation in the
  `splitNext` action, which will be used to implement `grind?` and
  `finish?`.

* [#10812](https://github.com/leanprover/lean4/pull/10812) implements `lia`, `linarith`, and `ac` actions for `grind`
  interactive mode.

* [#10824](https://github.com/leanprover/lean4/pull/10824) implements the `cases?` tactic for the `grind` interactive mode.
  It provides a convenient way to select anchors. Users can filter the
  candidates using the filter language.

* [#10828](https://github.com/leanprover/lean4/pull/10828) implements a compact notation for inspecting the `grind` state
  in interactive mode. Within a `grind` tactic block, each tactic may
  optionally have a suffix of the form `| filter?`.

* [#10833](https://github.com/leanprover/lean4/pull/10833) implements infrastructure for evaluating `grind` tactics in the
  `GrindM` monad. We are going to use it to check whether auto-generated
  tactics can effectively close the original goal.

* [#10834](https://github.com/leanprover/lean4/pull/10834) implements the `ring` action for `grind`.

* [#10836](https://github.com/leanprover/lean4/pull/10836) implements support for `Action` in the `grind` solver extensions
  (`SolverExtension`). It also provides the `Solvers.mkAction` function
  that constructs an `Action` using all registered solvers. The generated
  action is "fair," that is, a solver cannot prevent other solvers from
  making progress.

* [#10837](https://github.com/leanprover/lean4/pull/10837) implements the `finish?` tactic for the `grind` interactive
  mode. When it successfully closes the goal, it produces a code action
  that allows the user to close the goal using explicit grind tactic
  steps, i.e., without any search. It also makes explicit which solvers
  have been used.

* [#10841](https://github.com/leanprover/lean4/pull/10841) improves the `grind` tactic generated by the `instantiate`
  action in tracing mode. It also updates the syntax for the `instantiate`
  tactic, making it similar to `simp`. For example:

  * `instantiate only [thm1, thm2]` instantiates only theorems `thm1` and
  `thm2`.
  * `instantiate [thm1, thm2]` instantiates theorems marked with the
  `@[grind]` attribute **and** theorems `thm1` and `thm2`.

* [#10843](https://github.com/leanprover/lean4/pull/10843) implements the `set_option` tactic in `grind` interactive mode.

* [#10846](https://github.com/leanprover/lean4/pull/10846) fixes a few issues on `instance only [...]` tactic generation at
  `finish?`.

```

```markdown

## Compiler

* [#10429](https://github.com/leanprover/lean4/pull/10429) fixes and overeager reuse of specialisation in the code
  generator.

* [#10444](https://github.com/leanprover/lean4/pull/10444) fixes an overeager insertion of `inc` operations for large uint
  constants.

* [#10488](https://github.com/leanprover/lean4/pull/10488) changes the way that scientific numerals are parsed in order to
  give better error messages for (invalid) syntax like `32.succ`.

* [#10495](https://github.com/leanprover/lean4/pull/10495) fixes constant folding for UIntX in the code generator. This
  optimization was previously simply dead code due to the way that uint
  literals are encoded.

* [#10610](https://github.com/leanprover/lean4/pull/10610) ensures that even if a type is marked as `irreducible` the
  compiler can see through it in
  order to discover functions hidden behind type aliases.

* [#10626](https://github.com/leanprover/lean4/pull/10626) reduces the aggressiveness of the dead let eliminator from
  lambda RC.

* [#10689](https://github.com/leanprover/lean4/pull/10689) fixes an oversight in the RC insertion phase in the code
  generator.

## Pretty Printing

* [#10376](https://github.com/leanprover/lean4/pull/10376) modifies pretty printing of `fun` binders, suppressing the safe
  shadowing feature among the binders in the same `fun`. For example,
  rather than pretty printing as `fun x x => 0`, we now see `fun x x_1 =>
  0`. The calculation is done per `fun`, so for example `fun x => id fun x
  => 0` pretty prints as-is, taking advantage of safe shadowing.

## Documentation

* [#10632](https://github.com/leanprover/lean4/pull/10632) adds missing docstrings for ByteArray and makes existing ones
  consistent with our style.

* [#10640](https://github.com/leanprover/lean4/pull/10640) adds a missing docstring and applies our style guide to parts of
  the String API.

## Server

* [#10365](https://github.com/leanprover/lean4/pull/10365) implements the server-side for a new trace search mechanism in
  the InfoView.

* [#10442](https://github.com/leanprover/lean4/pull/10442) ensures that unknown identifier code actions are provided on
  auto-implicits.

* [#10524](https://github.com/leanprover/lean4/pull/10524) adds support for interactivity to the combined "try this"
  messages that were introduced in #9966. In doing so, it moves the link
  to apply a suggestion to a separate `[apply]` button in front of the
  suggestion. Hints with diffs remain unchanged, as they did not
  previously support interacting with terms in the diff, either.

* [#10538](https://github.com/leanprover/lean4/pull/10538) fixes deadlocking `exit` calls in the language server.

* [#10584](https://github.com/leanprover/lean4/pull/10584) causes Verso docstrings to search for a name in the environment
  that is at least as long as the current name, providing it as a
  suggestion.

* [#10609](https://github.com/leanprover/lean4/pull/10609) fixes an LSP-non-compliance in the `FileSystemWatcher` that was
  introduced in #925.

* [#10619](https://github.com/leanprover/lean4/pull/10619) fixes a bug in the unknown identifier code actions where it
  would yield non-sensical suggestions for nested `open` declarations like
  `open Foo.Bar`.

* [#10660](https://github.com/leanprover/lean4/pull/10660) adds auto-completion for identifiers after `end`. It also fixes
  a bug where completion in the whitespace after `set_option` would not
  yield the full option list.

* [#10662](https://github.com/leanprover/lean4/pull/10662) re-enables semantic tokens for Verso docstrings, after a prior
  change accidentally disabled them. It also adds a test to prevent this
  from happening again.

* [#10738](https://github.com/leanprover/lean4/pull/10738) fixes a regression introduced by #10307, where hovering the name
  of an inductive type or constructor in its own declaration didn't show
  the docstring. In the process, a bug in docstring handling for
  coinductive types was discovered and also fixed. Tests are added to
  prevent the regression from repeating in the future.

* [#10757](https://github.com/leanprover/lean4/pull/10757) fixes a bug in combination with VS Code where Lean code that
  looks like CSS color codes would display a color picker decoration.

* [#10797](https://github.com/leanprover/lean4/pull/10797) fixes a bug in the unknown identifier code actions where the
  identifiers wouldn't be correctly minimized in nested namespaces. It
  also fixes a bug where identifiers would sometimes be minimized to
  `[anonymous]`.

## Lake

* [#9855](https://github.com/leanprover/lean4/pull/9855) adds a new `allowImportAll` configuration option for packages
  and libraries. When enabled by an upstream package or library,
  downstream packages will be able to `import all` modules of that package
  or library. This enables package authors to selectively choose which
  `private` elements, if any, downstream packages may have access to.

* [#10188](https://github.com/leanprover/lean4/pull/10188) adds support for remote artifact caches (e.g., Reservoir) to
  Lake. As part of this support, a new suite of `lake cache` CLI commands
  has been introduced to help manage Lake's cache. Also, the existing
  local cache support has been overhauled for better interplay with the
  new remote support.

* [#10452](https://github.com/leanprover/lean4/pull/10452) refactors Lake's package naming procedure to allow packages to
  be renamed by the consumer. With this, users can now require a package
  using a different name than the one it was defined with.

* [#10459](https://github.com/leanprover/lean4/pull/10459) fixes a conditional check in a GitHub Action template generated
  by Lake.

* [#10468](https://github.com/leanprover/lean4/pull/10468) refactors the Lake log monads to take a `LogConfig` structure
  when run (rather than multiple arguments). This breaking change should
  help minimize future breakages due to changes in configurations options.

* [#10551](https://github.com/leanprover/lean4/pull/10551) enables Reservoir packages to be required as dependencies at a
  specific package version (i.e., the `version` specified in the package's
  configuration file).

* [#10576](https://github.com/leanprover/lean4/pull/10576) adds a new package configuration option: `restoreAllArtifacts`.
  When set to `true` and the Lake local artifact cache is enabled, Lake
  will copy all cached artifacts into the build directory. This ensures
  they are available for external consumers who expect build results to be
  in the build directory.

* [#10578](https://github.com/leanprover/lean4/pull/10578) adds support for the CMake spelling of a build type (i.e.,
  capitalized) to Lake's `buildType` configuration option.

* [#10579](https://github.com/leanprover/lean4/pull/10579) alters `libPrefixOnWindows` behavior to add the `lib` prefix to
  the library's `libName` rather than just the file path. This means that
  Lake's `-l` will now have the prefix on Windows. While this should not
  matter to a MSYS2 build (which accepts both `lib`-prefixed and
  unprefixed variants), it should ensure compatibility with MSVC (if that
  is ever an issue).

* [#10730](https://github.com/leanprover/lean4/pull/10730) changes the Lake's remote cache interface to scope cache outputs
  by toolchain and/or platform were useful.

* [#10741](https://github.com/leanprover/lean4/pull/10741) fixes a bug where partially up-to-date files built with `--old`
  could be stored in the cache as fully up-to-date. Such files are no
  longer cached. In addition, builds without traces now only perform an
  modification time check with `--old`. Otherwise, they are considered
  out-of-date.

## Other

* [#10383](https://github.com/leanprover/lean4/pull/10383) includes some improvements to the release process, making the
  updating of `stable` branches more robust, and including `cslib` in the
  release checklist.

* [#10389](https://github.com/leanprover/lean4/pull/10389) fixes a bug where string literal parsing ignored its trailing
  whitespace setting.

* [#10460](https://github.com/leanprover/lean4/pull/10460) introduces a simple script that adjusts module headers in a
  package for use of the module system, without further minimizing import
  or annotation use.

* [#10476](https://github.com/leanprover/lean4/pull/10476) fixes the dead `let` elimination code in the kernel's
  `infer_let` function.

* [#10575](https://github.com/leanprover/lean4/pull/10575) adds the necessary infrastructure for recording elaboration
  dependencies that may not be apparent from the resulting environment
  such as notations and other metaprograms. An adapted version of `shake`
  from Mathlib is added to `script/` but may be moved to another location
  or repo in the future.

* [#10777](https://github.com/leanprover/lean4/pull/10777) improves the scripts assisting with cutting Lean releases (by
  reporting CI status of open PRs, and adding documentation), and adds a
  `.claude/commands/release.md` prompt file so Claude can assist.

```
