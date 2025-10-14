/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.24.0-rc1 (2025-09-15)" =>
%%%
tag := "release-v4.24.0"
file := "v4.24.0"
%%%

````markdown
For this release, 377 changes landed. In addition to the 105 feature additions and 75 fixes listed below there were 25 refactoring changes, 9 documentation improvements, 21 performance improvements, 4 improvements to the test suite and 138 other changes.

## Highlights

Lean 4.24.0 release brings continued improvements to the module system and the verification framework,
strengthens the `grind` tactic, and advances the standard library.
The release also introduces more efficient constructions of `DecidableEq` instances and `noConfusion` ([#10152](https://github.com/leanprover/lean4/pull/10152) and [#10300](https://github.com/leanprover/lean4/pull/10300)),
optimizing compilation.

As an example for our continuous improvements to performance:

- [#10249](https://github.com/leanprover/lean4/pull/10249) speeds up auto-completion by a factor of ~3.5x through various
performance improvements in the language server.

As always, there are plenty of bug fixes and new features, some of which are listed below:

### "Try this" suggestions are rendered under 'Messages'

- [#9966](https://github.com/leanprover/lean4/pull/9966) adjusts the "try this" widget to be rendered as a widget message
  under 'Messages', not a separate widget under a 'Suggestions' section.
  The main benefit of this is that the message of the widget is not
  duplicated between 'Messages' and 'Suggestions'.

### `invariants` and `with` sections in `mvcgen`

- [#9927](https://github.com/leanprover/lean4/pull/9927) implements extended `induction`-inspired syntax for `mvcgen`,
  allowing optional `invariants` and `with` sections.

  The example below gives the proof that `nodup` correctly checks for duplicates in a list.

  ```lean
  import Std.Tactic.Do
  import Std

  open Std Do

  def nodup (l : List Int) : Bool := Id.run do
    let mut seen : HashSet Int := ∅
    for x in l do
      if x ∈ seen then
        return false
      seen := seen.insert x
    return true

  theorem nodup_correct (h : nodup l = r) : r = true ↔ l.Nodup := by
    unfold nodup at h
    apply Id.of_wp_run_eq h; clear h
    mvcgen
    invariants
    · Invariant.withEarlyReturn
        (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
        (onContinue := fun xs seen =>
          ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
    with grind
  ```

### Library: Dyadic rationals

- [#9993](https://github.com/leanprover/lean4/pull/9993) defines the dyadic rationals, showing they are an ordered ring
  embedding into the rationals.

### Grind AC solver

`grind` can reason about associative, commutative, idempotent, and/or unital operations
([#10105](https://github.com/leanprover/lean4/pull/10105), [#10146](https://github.com/leanprover/lean4/pull/10146), etc..):

```lean
example (a b c : Nat) : max a (max b c) = max (max b 0) (max a c) := by
  grind only

example {α} (as bs cs : List α) : as ++ (bs ++ cs) = ((as ++ []) ++ bs) ++ (cs ++ []) := by
  grind only

example {α : Sort u} (op : α → α → α) (u : α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op] [Std.LawfulIdentity op u] (a b c : α)
    : op (op a a) (op b c) = op (op (op b a) (op (op u b) b)) c := by
  grind only
```

### Metaprogramming notes

- [#10306](https://github.com/leanprover/lean4/pull/10306) fixes a few bugs in the `rw` tactic.

  Metaprogramming API: Instead of `Lean.MVarId.rewrite` prefer `Lean.Elab.Tactic.elabRewrite`
  for elaborating rewrite theorems and applying rewrites to expressions.

### Breaking changes

- [#9749](https://github.com/leanprover/lean4/pull/9749) refactors the Lake codebase to use the new module system
  throughout. Every module in `Lake` is now a `module`.

  **Breaking change:** Since the module system encourages a `private`-by-default design,
  the Lake API has switched from its previous `public`-by-default approach. As such,
  many definitions that were previously public are now private. The newly private definitions
  are not expected to have had significant user use, nonetheless, important use cases could be missed.
  If a key API is now inaccessible but seems like it should be public, users are encouraged
  to report this as an issue on GitHub.

## Language

* [#8891](https://github.com/leanprover/lean4/pull/8891) improves the error message produced when passing (automatically
  redundant) local hypotheses to `grind`.

* [#9651](https://github.com/leanprover/lean4/pull/9651) modifies the generation of induction and partial correctness
  lemmas for `mutual` blocks defined via `partial_fixpoint`. Additionally,
  the generation of lattice-theoretic induction principles of functions
  via `mutual` blocks is modified for consistency with `partial_fixpoint`.

* [#9674](https://github.com/leanprover/lean4/pull/9674) cleans up `optParam`/`autoParam`/etc. annotations before
  elaborating definition bodies, theorem bodies, `fun` bodies, and `let`
  function bodies. Both `variable`s and binders in declaration headers are
  supported.

* [#9918](https://github.com/leanprover/lean4/pull/9918) prevents `rcases` and `obtain` from creating absurdly long case
  tag names when taking single constructor types (like `Exists`) apart.
  Fixes #6550

* [#9923](https://github.com/leanprover/lean4/pull/9923) adds a guard for a delaborator that is causing panics in
  doc-gen4. This is a band-aid solution for now, and @sgraf812 will take a
  look when they're back from leave.

* [#9926](https://github.com/leanprover/lean4/pull/9926) guards the `Std.Tactic.Do.MGoalEntails` delaborator by a check
  ensuring that there are at least 3 arguments present, preventing
  potential panics.

* [#9927](https://github.com/leanprover/lean4/pull/9927) implements extended `induction`-inspired syntax for `mvcgen`,
  allowing optional `using invariants` and `with` sections.

* [#9930](https://github.com/leanprover/lean4/pull/9930) reverts the way `grind cutsat` embeds `Nat.sub` into `Int`. It
  fixes a regression reported by David Renshaw on Zulip.

* [#9938](https://github.com/leanprover/lean4/pull/9938) removes a duplicate `mpure_intro` tactic definition.

* [#9939](https://github.com/leanprover/lean4/pull/9939) expands `mvcgen using invariants | $n => $t` to `mvcgen; case
  inv<$n> => exact $t` to avoid MVar instantiation mishaps observable in
  the test case for #9581.

* [#9942](https://github.com/leanprover/lean4/pull/9942) modifies `intro` to create tactic info localized to each
  hypothesis, making it possible to see how `intro` works
  variable-by-variable. Additionally:
  - The tactic supports `intro rfl` to introduce an equality and
  immediately substitute it, like `rintro rfl` (recall: the `rfl` pattern
  is like doing `intro h; subst h`). The `rintro` tactic can also now
  support `HEq` in `rfl` patterns if `eq_of_heq` applies.
  - In `intro (h : t)`, elaboration of `t` is interleaved with unification
  with the type of `h`, which prevents default instances from causing
  unification to fail.
  - Tactics that change types of hypotheses (including `intro (h : t)`,
  `delta`, `dsimp`) now update the local instance cache.

* [#9945](https://github.com/leanprover/lean4/pull/9945) optimizes the proof terms produced by `grind cutsat`. It removes
  unused entries from the context objects when generating the final proof,
  significantly reducing the amount of junk in the resulting terms.
  Example:
  ```lean
  /--
  trace: [grind.debug.proof] fun h h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 =>
        let ctx := RArray.leaf (f 2);
        let p_1 := Poly.add 1 0 (Poly.num 0);
        let p_2 := Poly.add (-1) 0 (Poly.num 1);
        let p_3 := Poly.num 1;
        le_unsat ctx p_3 (eagerReduce (Eq.refl true)) (le_combine ctx p_2 p_1 p_3 (eagerReduce (Eq.refl true)) h_8 h_1)
  -/
  #guard_msgs in -- Context should contain only `f 2`
  open Lean Int Linear in
  set_option trace.grind.debug.proof true in
  example (f : Nat → Int) :
      f 1 <= 0 → f 2 <= 0 → f 3 <= 0 → f 4 <= 0 → f 5 <= 0 →
      f 6 <= 0 → f 7 <= 0 → f 8 <= 0 → -1 * f 2 + 1 <= 0 → False := by
    grind
  ```

* [#9946](https://github.com/leanprover/lean4/pull/9946) optimizes the proof terms produced by `grind ring`. It is
  similar to #9945, but for the ring module in `grind`.
  It removes unused entries from the context objects when generating the
  final proof, significantly reducing the amount of junk in the resulting
  terms. Example:
  ```lean
  /--
  trace: [grind.debug.proof] fun h h_1 h_2 h_3 =>
        Classical.byContradiction fun h_4 =>
          let ctx := RArray.branch 1 (RArray.leaf x) (RArray.leaf x⁻¹);
          let e_1 := (Expr.var 0).mul (Expr.var 1);
          let e_2 := Expr.num 0;
          let e_3 := Expr.num 1;
          let e_4 := (Expr.var 0).pow 2;
          let m_1 := Mon.mult (Power.mk 1 1) Mon.unit;
          let m_2 := Mon.mult (Power.mk 0 1) Mon.unit;
          let p_1 := Poly.num (-1);
          let p_2 := Poly.add (-1) (Mon.mult (Power.mk 0 1) Mon.unit) (Poly.num 0);
          let p_3 := Poly.add 1 (Mon.mult (Power.mk 0 2) Mon.unit) (Poly.num 0);
          let p_4 := Poly.add 1 (Mon.mult (Power.mk 0 1) (Mon.mult (Power.mk 1 1) Mon.unit)) (Poly.num (-1));
          let p_5 := Poly.add 1 (Mon.mult (Power.mk 0 1) Mon.unit) (Poly.num 0);
          one_eq_zero_unsat ctx p_1 (eagerReduce (Eq.refl true))
            (Stepwise.simp ctx 1 p_4 (-1) m_1 p_5 p_1 (eagerReduce (Eq.refl true))
              (Stepwise.core ctx e_1 e_3 p_4 (eagerReduce (Eq.refl true)) (diseq0_to_eq x h_4))
              (Stepwise.mul ctx p_2 (-1) p_5 (eagerReduce (Eq.refl true))
                (Stepwise.superpose ctx 1 m_2 p_4 (-1) m_1 p_3 p_2 (eagerReduce (Eq.refl true))
                  (Stepwise.core ctx e_1 e_3 p_4 (eagerReduce (Eq.refl true)) (diseq0_to_eq x h_4))
                  (Stepwise.core ctx e_4 e_2 p_3 (eagerReduce (Eq.refl true)) h))))
  -/
  #guard_msgs in -- Context should contains only `x` and its inverse.
  set_option trace.grind.debug.proof true in
  set_option pp.structureInstances false in
  open Lean Grind CommRing in
  example [Field α] (x y z w : α) :
     x^2 = 0 → y^2 = 0 → z^3 = 0 → w^2 = 0 → x = 0 := by
    grind
  ```

* [#9947](https://github.com/leanprover/lean4/pull/9947) optimizes the proof terms produced by `grind linarith`. It is
  similar to #9945, but for the `linarith` module in `grind`.
  It removes unused entries from the context objects when generating the
  final proof, significantly reducing the amount of junk in the resulting
  terms.

* [#9951](https://github.com/leanprover/lean4/pull/9951) generates `.ctorIdx` functions for all inductive types, not just
  enumeration types. This can be a building block for other constructions
  (`BEq`, `noConfusion`) that are size-efficient even for large
  inductives.

* [#9952](https://github.com/leanprover/lean4/pull/9952) adds “non-branching case statements”: For each inductive
  constructor `T.con` this adds a function `T.con.with` that is similar
  `T.casesOn`, but has only one arm (the one for `con`), and an additional
  `t.toCtorIdx = 12` assumption.

* [#9954](https://github.com/leanprover/lean4/pull/9954) removes the option `grind +ringNull`. It provided an alternative
  proof term construction for the `grind ring` module, but it was less
  effective than the default proof construction mode and had effectively
  become dead code.
  also optimizes semiring normalization proof terms using the
  infrastructure added in #9946.
  **Remark:** After updating stage0, we can remove several background
  theorems from the `Init/Grind` folder.

* [#9958](https://github.com/leanprover/lean4/pull/9958) ensures that equations in the `grind cutsat` module are
  maintained in solved form. That is, given an equation `a*x + p = 0` used
  to eliminate `x`, the linear polynomial `p` must not contain other
  eliminated variables. Before this PR, equations were maintained in
  triangular form. We are going to use the solved form to linearize
  nonlinear terms.

* [#9968](https://github.com/leanprover/lean4/pull/9968) modifies macros, which implement non-atomic definitions and
  ```$cmd1 in $cmd2``` syntax. These macros involve implicit scopes,
  introduced through ```section``` and ```namespace``` commands. Since
  sections or namespaces are designed to delimit local attributes, this
  has led to unintuitive behaviour when applying local attributes to
  definitions appearing in the above-mentioned contexts. This has been
  causing the following examples to fail:
  ```lean4
  axiom A : Prop

* [#9974](https://github.com/leanprover/lean4/pull/9974) registers a parser alias for `Lean.Parser.Command.visibility`.
  This avoids having to import `Lean.Parser.Command` in simple command
  macros that use visibilities.

* [#9980](https://github.com/leanprover/lean4/pull/9980) fixes a bug in the dynamic variable reordering function used in
  `grind cutsat`.

* [#9989](https://github.com/leanprover/lean4/pull/9989) changes the new extended syntax for `mvcgen` to `mvcgen
  invariants ... with ...`.

* [#9995](https://github.com/leanprover/lean4/pull/9995) almost completely rewrites the inductive predicate recursion
  algorithm; in particular `IndPredBelow` to function more consistently.
  Historically, the `brecOn` generation through `IndPredBelow` has been
  very error-prone -- this should be fixed now since the new algorithm is
  very direct and doesn't rely on tactics or meta-variables at all.
  Additionally, the new structural recursion procedure for inductive
  predicates shares more code with regular structural recursion and thus
  allows for mutual and nested recursion in the same way it was possible
  with regular structural recursion. For example, the following works now:
  ```lean-4
  mutual

* [#9996](https://github.com/leanprover/lean4/pull/9996) improves support for nonlinear monomials in `grind cutsat`. For
  example, given a monomial `a * b`, if `cutsat` discovers that `a = 2`,
  it now propagates that `a * b = 2 * b`.
  Recall that nonlinear monomials like `a * b` are treated as variables in
  `cutsat`, a procedure designed for linear integer arithmetic.

* [#10007](https://github.com/leanprover/lean4/pull/10007) lets #print print `private` before `protected`, matching the
  syntax.

* [#10008](https://github.com/leanprover/lean4/pull/10008) fixes a bug in `#eval` where clicking on the evaluated
  expression could show errors in the Infoview. This was caused by `#eval`
  not saving the temporary environment that is used when elaborating the
  expression.

* [#10010](https://github.com/leanprover/lean4/pull/10010) improves support for nonlinear `/` and `%` in `grind cutsat`.
  For example, given `a / b`, if `cutsat` discovers that `b = 2`, it now
  propagates that `a / b = b / 2`. is similar to #9996, but for
  `/` and `%`. Example:

  ```lean
  example (a b c d : Nat)
      : b > 1 → d = 1 → b ≤ d + 1 → a % b = 1 → a = 2 * c → False := by
    grind
  ```

* [#10020](https://github.com/leanprover/lean4/pull/10020) fixes a missing case for PR #10010.

* [#10021](https://github.com/leanprover/lean4/pull/10021) make some minor changes to the grind annotation analysis script,
  including sorting results and handling errors. Still need to add an
  external UI.

* [#10022](https://github.com/leanprover/lean4/pull/10022) improves support for `Fin n` in `grind cutsat` when `n` is not a
  numeral. For example, the following goals can now be solved
  automatically:

  ```lean
  example (p d : Nat) (n : Fin (p + 1))
      : 2 ≤ p → p ≤ d + 1 → d = 1 → n = 0 ∨ n = 1 ∨ n = 2 := by
    grind

* [#10034](https://github.com/leanprover/lean4/pull/10034) changes the "declaration uses 'sorry'" error to pretty print an
  actual `sorry` expression in the message. The effect is that the `sorry`
  is hoverable and, if it's labeled, you can "go to definition" to see
  where it came from.

* [#10038](https://github.com/leanprover/lean4/pull/10038) ensures `grind` error messages use `{.ofConstName declName}`
  when referencing declaration names.

* [#10060](https://github.com/leanprover/lean4/pull/10060) allows for more fine-grained control over what derived instances
  have exposed definitions under the module system: handlers should not
  expose their implementation unless either the deriving item or a
  surrounding section is marked with `@[expose]`. Built-in handlers to be
  updated after a stage 0 update.

* [#10069](https://github.com/leanprover/lean4/pull/10069) adds helper theorems to support `NatModule` in `grind linarith`.

* [#10071](https://github.com/leanprover/lean4/pull/10071) improves support for `a^n` in `grind cutsat`. For example, if
  `cutsat` discovers that `a` and `b` are equal to numerals, it now
  propagates the equality. is similar to #9996, but `a^b`.
  Example:

  ```lean
  example (n : Nat) : n = 2 → 2 ^ (n+1) = 8 := by
    grind
  ```

* [#10085](https://github.com/leanprover/lean4/pull/10085) adds a parser alias for the `rawIdent` parser, so that it can be
  used in `syntax` declarations in `Init`.

* [#10093](https://github.com/leanprover/lean4/pull/10093) adds background theorems for a new solver to be implemented in
  `grind` that will support associative and commutative operators.

* [#10095](https://github.com/leanprover/lean4/pull/10095) modifies the `grind` algebra typeclasses to use `SMul x y`
  instead of `HMul x y y`.

* [#10105](https://github.com/leanprover/lean4/pull/10105) adds support for detecting associative operators in `grind`. The
  new AC module also detects whether the operator is commutative,
  idempotent, and whether it has a neutral element. The information is
  cached.

* [#10113](https://github.com/leanprover/lean4/pull/10113) deprecates `.toCtorIdx` for the more naturally named `.ctorIdx`
  (and updates the standard library).

* [#10120](https://github.com/leanprover/lean4/pull/10120) fixes an issue where private definitions recursively invoked
  using generalized field notation (dot notation) would give an "invalid
  field" errors. It also fixes an issue where "invalid field notation"
  errors would pretty print the name of the declaration with a `_private`
  prefix.

* [#10125](https://github.com/leanprover/lean4/pull/10125) allows `#guard_msgs` to report the relative positions of logged
  messages with the config option `(positions := true)`.

* [#10129](https://github.com/leanprover/lean4/pull/10129) replaces the interim order typeclasses used by `Grind` with the
  new publicly available classes in `Std`.

* [#10134](https://github.com/leanprover/lean4/pull/10134) makes the generation of functional induction principles more
  robust when the user `let`-binds a variable that is then `match`'ed on.
  Fixes #10132.

* [#10135](https://github.com/leanprover/lean4/pull/10135) lets the `ctorIdx` definition for single constructor inductives
  avoid the pointless `.casesOn`, and uses `macro_inline` to avoid
  compiling the function and wasting symbols.

* [#10141](https://github.com/leanprover/lean4/pull/10141) reverts the `macro_inline` part of #10135.

* [#10144](https://github.com/leanprover/lean4/pull/10144) changes the construction of a `CompleteLattice` instance on
  predicates (maps intro `Prop`) inside of
  `coinductive_fixpoint`/`inductive_fixpoint` machinery.

* [#10146](https://github.com/leanprover/lean4/pull/10146) implements the basic infrastructure for the new procedure
  handling AC operators in grind. It already supports normalizing
  disequalities. Future PRs will add support for simplification using
  equalities, and computing critical pairs. Examples:
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c : α)
      : op a (op b c) = op (op a b) c := by
    grind only

* [#10151](https://github.com/leanprover/lean4/pull/10151) ensures `where finally` tactics can access private data under
  the module system even when the corresponding holes are in the public
  scope as long as all of them are of proposition types.

* [#10152](https://github.com/leanprover/lean4/pull/10152) introduces an alternative construction for `DecidableEq`
  instances that avoids the quadratic overhead of the default
  construction.

* [#10166](https://github.com/leanprover/lean4/pull/10166) reviews the expected-to-fail-right-now tests for `grind`, moving
  some (now passing) tests to the main test suite, updating some tests,
  and adding some tests about normalisation of exponents.

* [#10177](https://github.com/leanprover/lean4/pull/10177) fixes a bug in the `grind` preprocessor exposed by #10160.

* [#10179](https://github.com/leanprover/lean4/pull/10179) fixes `grind` instance normalization procedure.
  Some modules in grind use builtin instances defined directly in core
  (e.g., `cutsat`), while others synthesize them using `synthInstance`
  (e.g., `ring`). This inconsistency is problematic, as it may introduce
  mismatches and result in two different representations for the same
  term. fixes the issue.

* [#10183](https://github.com/leanprover/lean4/pull/10183) lets match equations be proved by `rfl` if possible, instead of
  explicitly unfolding the LHS first. May lead to smaller proofs.

* [#10185](https://github.com/leanprover/lean4/pull/10185) documents all `grind` attribute modifiers (e.g., `=`, `usr`,
  `ext`, etc).

* [#10186](https://github.com/leanprover/lean4/pull/10186) adds supports for simplifying disequalities in the `grind ac`
  module.

* [#10189](https://github.com/leanprover/lean4/pull/10189) implements the proof terms for the new `grind ac` module.
  Examples:
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] (a b c d : α)
      : op a (op b b) = op c d → op c (op d c) = op (op a b) (op b c) := by
    grind only

* [#10205](https://github.com/leanprover/lean4/pull/10205) adds superposition for associative and commutative operators in
  `grind ac`. Examples:

  ```lean
  example (a b c d e f g h : Nat) :
      max a b = max c d → max b e = max d f → max b g = max d h →
      max (max f d) (max c g) = max (max e (max d (max b (max c e)))) h := by
    grind -cutsat only

* [#10206](https://github.com/leanprover/lean4/pull/10206) adds superposition for associative (but non-commutative)
  operators in `grind ac`. Examples:
  ```lean
  example {α} (op : α → α → α) [Std.Associative op] (a b c d : α)
     : op a b = c →
       op b a = d →
       op (op c a) (op b c) = op (op a d) (op d b) := by
    grind

* [#10208](https://github.com/leanprover/lean4/pull/10208) adds the extra critical pairs to ensure the `grind ac` procedure
  is complete when the operator is AC and idempotent. Example:
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.Commutative op] [Std.IdempotentOp op]
        (a b c d : α) : op a (op b b) = op d c → op (op b a) (op b c) = op c (op d c)  := by
    grind only
  ```

* [#10221](https://github.com/leanprover/lean4/pull/10221) adds the extra critical pairs to ensure the `grind ac` procedure
  is complete when the operator is associative and idempotent, but not
  commutative. Example:
  ```lean
  example {α : Sort u} (op : α → α → α) [Std.Associative op] [Std.IdempotentOp op] (a b c d e f x y w : α)
      : op d (op x c) = op a b →
        op e (op f (op y w)) = op a (op b c) →
        op d (op x c) = op e (op f (op y w)) := by
    grind only

* [#10223](https://github.com/leanprover/lean4/pull/10223) implements equality propagation from the new AC module into the
  `grind` core. Examples:

  ```lean
  example {α β : Sort u} (f : α → β) (op : α → α → α) [Std.Associative op] [Std.Commutative op]
      (a b c d : α) : op a (op b b) = op d c → f (op (op b a) (op b c)) = f (op c (op d c)) := by
    grind only

* [#10230](https://github.com/leanprover/lean4/pull/10230) adds `MonoBind` for more monad transformers. This allows using
  `partial_fixpoint` for more complicated monads based on `Option` and
  `EIO`. Example:
  ```lean-4
  abbrev M := ReaderT String (StateT String.Pos Option)

* [#10237](https://github.com/leanprover/lean4/pull/10237) fixes a missing case in the `grind` canonicalizer. Some types
  may include terms or propositions that are internalized later in the
  `grind` state.

* [#10239](https://github.com/leanprover/lean4/pull/10239) fixes the E-matching procedure for theorems that contain
  universe parameters not referenced by any regular parameter. This kind
  of theorem seldom happens in practice, but we do have instances in the
  standard library. Example:
  ```
  @[simp, grind =] theorem Std.Do.SPred.down_pure {φ : Prop} : (⌜φ⌝ : SPred []).down = φ := rfl
  ```

* [#10241](https://github.com/leanprover/lean4/pull/10241) adds some test cases for `grind` working with `Fin`. There are
  many still failing tests in `tests/lean/grind/grind_fin.lean` which I'm
  intending to triage and work on.

* [#10245](https://github.com/leanprover/lean4/pull/10245) changes the implementation of a function `unfoldPredRel` used in
  (co)inductive predicate machinery, that unfolds pointwise order on
  predicates to quantifications and implications. Previous implementation
  relied on `withDeclsDND` that could not deal with types which depend on
  each other. This caused the following example to fail:

  ```lean4
  inductive infSeq_functor1.{u} {α : Type u} (r : α → α → Prop) (call : {α : Type u} → (r : α → α → Prop) → α → Prop) : α → Prop where
    | step : r a b → infSeq_functor1 r call b → infSeq_functor1 r call a

* [#10265](https://github.com/leanprover/lean4/pull/10265) fixes a panic in `grind ring` exposed by #10242. `grind ring`
  should not assume that all normalizations have been applied, because
  some subterms cannot be rewritten by `simp` due to typing constraints.
  Moreover, `grind` uses `preprocessLight` in a few places, and it skips
  the simplifier/normalizer.

* [#10267](https://github.com/leanprover/lean4/pull/10267) implements the infrastructure for supporting `NatModule` in
  `grind linarith` and uses it to handle disequalities. Another PR will
  add support for equalities and inequalities. Example:
  ```lean
  open Lean Grind
  variable (M : Type) [NatModule M] [AddRightCancel M]

* [#10269](https://github.com/leanprover/lean4/pull/10269) changes the string interpolation procedure to omit redundant
  empty parts. For example `s!"{1}{2}"` previously elaborated to `toString
  "" ++ toString 1 ++ toString "" ++ toString 2 ++ toString ""` and now
  elaborates to `toString 1 ++ toString 2`.

* [#10271](https://github.com/leanprover/lean4/pull/10271) changes the naming of the internal functions in deriving
  instances like BEq to use accessible names. This is necessary to
  reasonably easily prove things about these functions. For example after
  `deriving BEq` for a type `T`, the implementation of `instBEqT` is in
  `instBEqT.beq`.

* [#10273](https://github.com/leanprover/lean4/pull/10273) tries to do the right thing about the visibility of the
  same-ctor-match-construct.

* [#10274](https://github.com/leanprover/lean4/pull/10274) changes the implementation of the linear `DecidableEq`
  implementation to use `match decEq` rather than `if h : ` to compare the
  constructor tags. Otherwise, the “smart unfolding” machinery will not
  let `rfl` decide that different constructors are different.

* [#10277](https://github.com/leanprover/lean4/pull/10277) adds the missing instances `IsPartialOrder`, `IsLinearPreorder`
  and `IsLinearOrder` for `OfNatModule.Q α`.

* [#10278](https://github.com/leanprover/lean4/pull/10278) adds support for `NatModule` equalities and inequalities in
  `grind linarith`. Examples:
  ```lean
  open Lean Grind Std

* [#10280](https://github.com/leanprover/lean4/pull/10280) adds the auxiliary theorem `Lean.Grind.Linarith.eq_normN` for
  normalizing `NatModule` equations when the instance `AddRightCancel` is
  not available.

* [#10281](https://github.com/leanprover/lean4/pull/10281) implements `NatModule` normalization when the `AddRightCancel`
  instance is not available. Note that in this case, the embedding into
  `IntModule` is not injective. Therefore, we use a custom normalizer,
  similar to the `CommSemiring` normalizer used in the `grind ring`
  module. Example:

  ```lean
  open Lean Grind
  example [NatModule α] (a b c : α)
      : 2•a + 2•(b + 2•c) + 3•a = 4•a + c + 2•b + 3•c + a := by
    grind
  ```

* [#10282](https://github.com/leanprover/lean4/pull/10282) improves the counterexamples produced by `grind linarith` for
  `NatModule`s. `grind` now hides occurrences of the auxiliary function
  `Grind.IntModule.OfNatModule.toQ`.

* [#10283](https://github.com/leanprover/lean4/pull/10283) implements diagnostic information for the `grind ac` module. It
  now displays the basis, normalized disequalities, and additional
  properties detected for each associative operator.

* [#10290](https://github.com/leanprover/lean4/pull/10290) adds infrastructure for registering new `grind` solvers. `grind`
  already includes many solvers, and this PR is the first step toward
  modularizing the design and supporting user-defined solvers.

* [#10294](https://github.com/leanprover/lean4/pull/10294) completes the `grind` solver extension design and ports the
  `grind ac` solver to the new framework. Future PRs will document the API
  and port the remaining solvers. An additional benefit of the new design
  is faster build times.

* [#10296](https://github.com/leanprover/lean4/pull/10296) fixes a bug in an auxiliary function used to construct proof
  terms in `grind cutsat`.

* [#10300](https://github.com/leanprover/lean4/pull/10300) offers an alternative `noConfusion` construction for the
  off-diagonal use (i.e. for different constructors), based on comparing
  the `.ctorIdx`. This should lead to faster type checking, as the kernel
  only has to reduce `.ctorIdx` twice, instead of the complicate
  `noConfusionType` construction.

* [#10301](https://github.com/leanprover/lean4/pull/10301) exposes ctorIdx and per-constructor eliminators. Fixes #10299.

* [#10306](https://github.com/leanprover/lean4/pull/10306) fixes a few bugs in the `rw` tactic: it could "steal" goals
  because they appear in the type of the rewrite, it did not do an occurs
  check, and new proof goals would not be synthetic opaque. also
  lets the `rfl` tactic assign synthetic opaque metavariables so that it
  is equivalent to `exact rfl`.

* [#10307](https://github.com/leanprover/lean4/pull/10307) upstreams the Verso parser and adds preliminary support for
  Verso in docstrings. This will allow the compiler to check examples and
  cross-references in documentation.

* [#10309](https://github.com/leanprover/lean4/pull/10309) modifies the `simpa` tactic so that in `simpa ... using e` there
  is tactic info on the range `simpa ... using` that shows the simplified
  goal.

* [#10313](https://github.com/leanprover/lean4/pull/10313) adds missing `grind` normalization rules for `natCast` and
  `intCast` Examples:
  ```
  open Lean.Grind
  variable (R : Type) (a b : R)

* [#10314](https://github.com/leanprover/lean4/pull/10314) skips model based theory combination on instances.

* [#10315](https://github.com/leanprover/lean4/pull/10315) adds `T.ctor.noConfusion` declarations, which are
  specializations of `T.noConfusion` to equalities between `T.ctor`. The
  point is to avoid reducing the `T.noConfusionType` construction every
  time we use `injection` or a similar tactic.

* [#10316](https://github.com/leanprover/lean4/pull/10316) shares common functionality relate to equalities between same
  constructors, and when these are type-correct. In particular it uses the
  more complete logic from `mkInjectivityThm` also in other places, such
  as `CasesOnSameCtor` and the deriving code for `BEq`, `DecidableEq`,
  `Ord`, for more consistency and better error messages.

* [#10321](https://github.com/leanprover/lean4/pull/10321) ensures that the auxiliary temporary metavariable IDs created by
  the E-matching module used in `grind` are not affected by what has been
  executed before invoking `grind`. The goal is to increase `grind`’s
  robustness.

* [#10322](https://github.com/leanprover/lean4/pull/10322) introduces limited functionality frontends `cutsat` and
  `grobner` for `grind`. We disable theorem instantiation (and case
  splitting for `grobner`), and turn off all other solvers. Both still
  allow `grind` configuration options, so for example one can use `cutsat
  +ring` (or `grobner +cutsat`) to solve problems that require both.

* [#10323](https://github.com/leanprover/lean4/pull/10323) fixes the `grind` canonicalizer for `OfNat.ofNat` applications.
  Example:
  ```lean
  example {C : Type} (h : Fin 2 → C) :
      -- `0` in the first `OfNat.ofNat` is not a raw literal
      h (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = h 0 := by
    grind
  ```

* [#10324](https://github.com/leanprover/lean4/pull/10324) disables an unused instance that causes expensive typeclass
  searches.

* [#10325](https://github.com/leanprover/lean4/pull/10325) implements model-based theory combination for types `A` which
  implement the `ToInt` interface. Examples:
  ```lean
  example {C : Type} (h : Fin 4 → C) (x : Fin 4)
      : 3 ≤ x → x ≤ 3 → h x = h (-1) := by
    grind

* [#10326](https://github.com/leanprover/lean4/pull/10326) fixes a performance issue in `grind linarith`. It was creating
  unnecessary `NatModule`/`IntModule` structures for commutative rings
  without an order. This kind of type should be handled by `grind ring`
  only.

* [#10331](https://github.com/leanprover/lean4/pull/10331) implements `mkNoConfusionImp` in Lean rather than in C. This
  reduces our reliance on C, and may bring performance benefits from not
  reducing `noConfusionType` during elaboration time (it still gets
  reduced by the kernel when type-checking).

* [#10332](https://github.com/leanprover/lean4/pull/10332) ensures that the infotree recognizes `Classical.propDecidable`
  as an instance, when below a `classical` tactic.

* [#10335](https://github.com/leanprover/lean4/pull/10335) fixes the nested proof term detection in `grind`. It must check
  whether the gadget `Grind.nestedProof` is over-applied.

* [#10342](https://github.com/leanprover/lean4/pull/10342) implements a new E-matching pattern inference procedure that is
  faithful to the behavior documented in the reference manual regarding
  minimal indexable subexpressions. The old inference procedure was
  failing to enforce this condition. For example, the manual documents
  `[grind ->]` as follows

* [#10373](https://github.com/leanprover/lean4/pull/10373) adds a `pp.unicode` option and a `unicode("→", "->")` syntax
  description alias for the lower-level `unicodeSymbol "→" "->"` parser.
  The syntax is added to the `notation` command as well. When `pp.unicode`
  is true (the default) then the first form is used when pretty printing,
  and otherwise the second ASCII form is used. A variant, `unicode("→",
  "->", preserveForPP)` causes the `->` form to be preferred; delaborators
  can insert `→` directly into the syntax, which will be pretty printed
  as-is; this allows notations like `fun` to use custom options such as
  `pp.unicode.fun` to opt into the unicode form when pretty printing.

## Library

* [#7858](https://github.com/leanprover/lean4/pull/7858) implements the fast circuit for overflow detection in unsigned
  multiplication used by Bitwuzla and proposed in:
  https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=987767

* [#9127](https://github.com/leanprover/lean4/pull/9127) makes `saveModuleData` throw an IO.Error instead of panicking,
  if given something that cannot be serialized. This doesn't really matter
  for saving modules, but is handy when writing tools to save auxiliary
  date in olean files via Batteries' `pickle`.

* [#9560](https://github.com/leanprover/lean4/pull/9560) fixes the `forIn` function, that previously caused the resulting
  Promise to be dropped without a value when an exception was thrown
  inside of it. It also corrects the parameter order of the `background`
  function.

* [#9599](https://github.com/leanprover/lean4/pull/9599) adds the type `Std.Internal.Parsec.Error`, which contains the
  constructors `.eof` (useful for checking if parsing failed due to not
  having enough input and then retrying when more input arrives that is
  useful in the HTTP server) and `.other`, which describes other errors.
  It also adds documentation to many functions, along with some new
  functions to the `ByteArray` Parsec, such as `peekWhen?`, `octDigit`,
  `takeWhile`, `takeUntil`, `skipWhile`, and `skipUntil`.

* [#9632](https://github.com/leanprover/lean4/pull/9632) adds lemmas for the `TreeMap` operations `filter`, `map` and
  `filterMap`. These lemmas existed already for hash maps and are simply
  ported over from there.

* [#9685](https://github.com/leanprover/lean4/pull/9685) verifies `toArray` and related functions for hashmaps.

* [#9797](https://github.com/leanprover/lean4/pull/9797) provides the means to quickly provide all the order instances
  associated with some high-level order structure (preorder, partial
  order, linear preorder, linear order). This can be done via the factory
  functions `PreorderPackage.ofLE`, `PartialOrderPackage.ofLE`,
  `LinearPreorderPackage.ofLE` and `LinearOrderPackage.ofLE`.

* [#9908](https://github.com/leanprover/lean4/pull/9908) makes `IsPreorder`, `IsPartialOrder`, `IsLinearPreorder` and
  `IsLinearOrder` extend `BEq` and `Ord` as appropriate, adds the
  `LawfulOrderBEq` and `LawfulOrderOrd` typeclasses relating `BEq` and
  `Ord` to `LE`, and adds many lemmas and instances.

* [#9916](https://github.com/leanprover/lean4/pull/9916) provides factories that derive order typeclasses in bulk, given
  an `Ord` instance. If present, existing instances are preferred over
  those derived from `Ord`. It is possible to specify any instance
  manually if desired.

* [#9924](https://github.com/leanprover/lean4/pull/9924) fixes examples in the documentation for `PostCond`.

* [#9931](https://github.com/leanprover/lean4/pull/9931) implements `Std.Do.Triple.mp`, enabling users to compose two
  specifications for the same program.

* [#9949](https://github.com/leanprover/lean4/pull/9949) allows most of the `List.lookup` lemmas to be used when
  `LawfulBEq α` is not available.

* [#9957](https://github.com/leanprover/lean4/pull/9957) upstreams the definition of Rat from Batteries, for use in our
  planned interval arithmetic tactic.

* [#9967](https://github.com/leanprover/lean4/pull/9967) removes local `Triple` notation from SpecLemmas.lean to work
  around a bug that breaks the stage2 build.

* [#9979](https://github.com/leanprover/lean4/pull/9979) replaces `Std.Internal.Rat` with the new public `Rat` upstreamed
  from Batteries.

* [#9987](https://github.com/leanprover/lean4/pull/9987) improves the tactic for proving that elements of a `Nat`-based
  `PRange` are in-bounds by relying on the `omega` tactic.

* [#9993](https://github.com/leanprover/lean4/pull/9993) defines the dyadic rationals, showing they are an ordered ring
  embedding into the rationals. We will use this for future interval
  arithmetic tactics.

* [#9999](https://github.com/leanprover/lean4/pull/9999) reduces the number of `Nat.Bitwise` grind annotations we have
  the deal with distributivity. The new smaller set encourages `grind` to
  rewrite into DNF. The old behaviour just resulted in saturating up to
  the instantiation limits.

* [#10000](https://github.com/leanprover/lean4/pull/10000) removes a `grind` annotation that fired on all `Option.map`s,
  causing an avalanche of instantiations.

* [#10005](https://github.com/leanprover/lean4/pull/10005) shortens the work necessary to make a type compatible with the
  polymorphic range notation. In the concrete case of `Nat`, it reduces
  the required lines of code from 150 to 70.

* [#10015](https://github.com/leanprover/lean4/pull/10015) exposes the bodies of `Name.append`, `Name.appendCore`, and
  `Name.hasMacroScopes`. This enables proof by reflection of the
  concatenation of name literals when using the module system.

* [#10018](https://github.com/leanprover/lean4/pull/10018) derives `BEq` and `Hashable` for `Lean.Import`. Lake already did
  this later, but it now done when defining `Import`.

* [#10019](https://github.com/leanprover/lean4/pull/10019) adds `@[expose]` to `Lean.ParserState.setPos`. This makes it
  possible to prove in-boundedness for a state produced by `setPos` for
  functions like `next'` and `get'` without needing to `import all`.

* [#10024](https://github.com/leanprover/lean4/pull/10024) adds useful declarations to the `LawfulOrderMin/Max` and
  `LawfulOrderLeftLeaningMin/Max` API. In particular, it introduces
  `.leftLeaningOfLE` factories for `Min` and `Max`. It also renames
  `LawfulOrderMin/Max.of_le` to .of_le_min_iff` and `.of_max_le_iff` and
  introduces a second variant with different arguments.

* [#10045](https://github.com/leanprover/lean4/pull/10045) implements the necessary typeclasses so that range notation
  works for integers. For example, `((-2)...3).toList = [-2, -1, 0, 1, 2]
  : List Int`.

* [#10049](https://github.com/leanprover/lean4/pull/10049) adds some background material needed for introducing the dyadic
  rationals in #9993.

* [#10050](https://github.com/leanprover/lean4/pull/10050) fixes some naming issues in Data/Rat/Lemmas, and upstreams the
  eliminator `numDenCasesOn` and its relatives.

* [#10059](https://github.com/leanprover/lean4/pull/10059) improves the names of definitions and lemmas in the polymorphic
  range API. It also introduces a recommended spelling. For example, a
  left-closed, right-open range is spelled `Rco` in analogy with Mathlib's
  `Ico` intervals.

* [#10075](https://github.com/leanprover/lean4/pull/10075) contains lemmas about `Int` (minor amendments for BitVec and
  Nat) that are being used in preparing the dyadics. This is all work of
  @Rob23oba, which I'm pulling out of #9993 early to keep that one
  manageable.

* [#10077](https://github.com/leanprover/lean4/pull/10077) upstreams lemmas about `Rat` from `Mathlib.Data.Rat.Defs` and
  `Mathlib.Algebra.Order.Ring.Unbundled.Rat`, specifically enough to get
  `Lean.Grind.Field Rat` and `Lean.Grind.OrderedRing Rat`. In addition to
  the lemmas, instances for `Inv Rat`, `Pow Rat Nat` and `Pow Rat Int`
  have been upstreamed.

* [#10107](https://github.com/leanprover/lean4/pull/10107) adds the `Lean.Grind.AddCommGroup` instance for `Rat`.

* [#10138](https://github.com/leanprover/lean4/pull/10138) adds lemmas about the `Dyadic.roundUp` and `Dyadic.roundDown`
  operations.

* [#10159](https://github.com/leanprover/lean4/pull/10159) adds `nodup_keys` lemmas as corollaries of existing
  `distinct_keys` to all `Map` variants.

* [#10162](https://github.com/leanprover/lean4/pull/10162) removes `grind →` annotations that fire too often, unhelpfully.
  It would be nice for `grind` to instantiate these lemmas, but only if
  they already see `xs ++ ys` and `#[]` in the same equivalence class, not
  just as soon as it sees `xs ++ ys`.

* [#10163](https://github.com/leanprover/lean4/pull/10163) removes some (hopefully) unnecessary `grind` annotations that
  cause instantiation explosions.

* [#10173](https://github.com/leanprover/lean4/pull/10173) removes the `extends Monad` from `MonadAwait` and `MonadAsync`
  to avoid underdetermined instances.

* [#10182](https://github.com/leanprover/lean4/pull/10182) adds lemmas about `Nat.fold` and `Nat.foldRev` on sums, to match
  the existing theorems about `dfold` and `dfoldRev`.

* [#10194](https://github.com/leanprover/lean4/pull/10194) adds the inverse of a dyadic rational, at a given precision, and
  characterising lemmas. Also cleans up various parts of the `Int.DivMod`
  and `Rat` APIs, and proves some characterising lemmas about
  `Rat.toDyadic`.

* [#10216](https://github.com/leanprover/lean4/pull/10216) fixes #10193.

* [#10224](https://github.com/leanprover/lean4/pull/10224) generalizes the monadic operations for `HashMap`, `TreeMap`, and
  `HashSet` to work for `m : Type u → Type v`.

* [#10227](https://github.com/leanprover/lean4/pull/10227) adds `@[grind]` annotations (nearly all `@[grind =]` annotations
  parallel to existing `@[simp]`s) for `ReaderT`, `StateT`, `ExceptT`.

* [#10244](https://github.com/leanprover/lean4/pull/10244) adds more lemmas about the `toList` and `toArray` functions on
  ranges and iterators. It also renames `Array.mem_toArray` into
  `List.mem_toArray`.

* [#10247](https://github.com/leanprover/lean4/pull/10247) adds missing the lemmas `ofList_eq_insertMany_empty`,
  `get?_eq_some_iff`, `getElem?_eq_some_iff` and `getKey?_eq_some_iff` to
  all container types.

* [#10250](https://github.com/leanprover/lean4/pull/10250) fixes a bug in the `LinearOrderPackage.ofOrd` factory. If there
  is a `LawfulEqOrd` instance available, it should automatically use it
  instead of requiring the user to provide the `eq_of_compare` argument to
  the factory. The PR also solves a hygiene-related problem making the
  factories fail when `Std` is not open.

* [#10303](https://github.com/leanprover/lean4/pull/10303) adds range support to`BitVec` and the `UInt*` types. This means
  that it is now possible to write, for example, `for i in (1 : UInt8)...5
  do`, in order to loop over the values 1, 2, 3 and 4 of type `UInt8`.

* [#10341](https://github.com/leanprover/lean4/pull/10341) moves the definitions and basic facts about `Function.Injective`
  and `Function.Surjective` up from Mathlib. We can do a better job of
  arguing via injectivity in `grind` if these are available.

## Compiler

* [#9631](https://github.com/leanprover/lean4/pull/9631) makes `IO.RealWorld` opaque. It also adds a new compiler -only
  `lcRealWorld` constant to represent this type within the compiler. By
  default, an opaque type definition is treated like `lcAny`, whereas we
  want a more efficient representation. At the moment, this isn't a big
  difference, but in the future we would like to completely erase
  `IO.RealWorld` at runtime.

* [#9922](https://github.com/leanprover/lean4/pull/9922) changes `internalizeCode` to replace all substitutions with
  non-param-bound fvars in `Expr`s (which are all types) with `lcAny`,
  preserving the invariant that there are no such dependencies. The
  violation of this invariant across files caused test failures in a
  pending PR, but it is difficult to write a direct test for it. In the
  future, we should probably change the LCNF checker to detect this.

* [#9972](https://github.com/leanprover/lean4/pull/9972) fixes an issue when running Mathlib's `FintypeCat` as code,
  where an erased type former is passed to a polymorphic function. We were
  lowering the arrow type to`object`, which conflicts with the runtime
  representation of an erased value as a tagged scalar.

* [#9977](https://github.com/leanprover/lean4/pull/9977) adds support for compilation of `casesOn` recursors of
  subsingleton predicates.

* [#10023](https://github.com/leanprover/lean4/pull/10023) adds support for correctly handling computations on fields in
  `casesOn` for inductive predicates that support large elimination. In
  any such predicate, the only relevant fields allowed are those that are
  also used as an index, in which case we can find the supplied index and
  use that term instead.

* [#10032](https://github.com/leanprover/lean4/pull/10032) changes the handling of overapplied constructors when lowering
  LCNF to IR from a (slightly implicit) assertion failure to producing
  `unreachable`. Transformations on inlined unreachable code can produce
  constructor applications with additional arguments.

* [#10040](https://github.com/leanprover/lean4/pull/10040) changes the `toMono` pass to replace decls with their `_redArg`
  equivalent, which has the consequence of not considering arguments
  deemed useless by the `reduceArity` pass for the purposes of the
  `noncomputable` check.

* [#10070](https://github.com/leanprover/lean4/pull/10070) fixes the compilation of `noConfusion` by repairing an oversight
  made when porting this code from the old compiler. The old compiler only
  repeatedly expanded the major for each non-`Prop` field of the inductive
  under consideration, mirroring the construction of `noConfusion` itself,
  whereas the new compiler erroneously counted all fields.

* [#10133](https://github.com/leanprover/lean4/pull/10133) fixes compatibility of Lean-generated executables with Unicode
  file system paths on Windows

* [#10214](https://github.com/leanprover/lean4/pull/10214) fixes #10213.

* [#10256](https://github.com/leanprover/lean4/pull/10256) corrects a mistake in `toIR` where it could over-apply a
  function that has an IR decl but no mono decl.

* [#10355](https://github.com/leanprover/lean4/pull/10355) changes `toLCNF` to convert `.proj` for builtin types to use
  projection functions instead.

## Pretty Printing

* [#10122](https://github.com/leanprover/lean4/pull/10122) adds support for pretty printing using generalized field
  notation (dot notation) for private definitions on public types. It also
  modifies dot notation elaboration to resolve names after removing the
  private prefix, which enables using dot notation for private definitions
  on private imported types.

* [#10373](https://github.com/leanprover/lean4/pull/10373) adds a `pp.unicode` option and a `unicode("→", "->")` syntax
  description alias for the lower-level `unicodeSymbol "→" "->"` parser.
  The syntax is added to the `notation` command as well. When `pp.unicode`
  is true (the default) then the first form is used when pretty printing,
  and otherwise the second ASCII form is used. A variant, `unicode("→",
  "->", preserveForPP)` causes the `->` form to be preferred; delaborators
  can insert `→` directly into the syntax, which will be pretty printed
  as-is; this allows notations like `fun` to use custom options such as
  `pp.unicode.fun` to opt into the unicode form when pretty printing.

* [#10374](https://github.com/leanprover/lean4/pull/10374) adds the options `pp.piBinderNames` and
  `pp.piBinderNames.hygienic`. Enabling `pp.piBinderNames` causes
  non-dependent pi binder names to be pretty printed, rather than be
  omitted. When `pp.piBinderNames.hygienic` is false (the default) then
  only non-hygienic such biner names are pretty printed. Setting `pp.all`
  enables `pp.piBinderNames` if it is not otherwise explicitly set.

## Documentation

* [#9956](https://github.com/leanprover/lean4/pull/9956) adds additional information to the `let` and `have` tactic
  docstrings about opaqueness, when to use each, and associated tactics.

## Server

* [#9966](https://github.com/leanprover/lean4/pull/9966) adjusts the "try this" widget to be rendered as a widget message
  under 'Messages', not a separate widget under a 'Suggestions' section.
  The main benefit of this is that the message of the widget is not
  duplicated between 'Messages' and 'Suggestions'.

* [#10047](https://github.com/leanprover/lean4/pull/10047) ensures that hovering over `match` displays the type of the
  match.

* [#10052](https://github.com/leanprover/lean4/pull/10052) fixes a bug that caused the Lean server process tree to survive
  the closing of VS Code.

* [#10249](https://github.com/leanprover/lean4/pull/10249) speeds up auto-completion by a factor of ~3.5x through various
  performance improvements in the language server. On one machine, with
  `import Mathlib`, completing `i` used to take 3200ms and now instead
  yields a result in 920ms.

## Lake

* [#9749](https://github.com/leanprover/lean4/pull/9749) refactors the Lake codebase to use the new module system
  throughout. Every module in `Lake` is now a `module`.

* [#10276](https://github.com/leanprover/lean4/pull/10276) moves the `verLit` syntax into the `Lake.DSL` namespace to be
  consistent with other code found in `Lake.DSL`.

## Other

* [#10043](https://github.com/leanprover/lean4/pull/10043) allows Lean's parser to run with a final position prior to the
  end of the string, so it can be invoked on a sub-region of the input.

* [#10217](https://github.com/leanprover/lean4/pull/10217) ensures `@[init]` declarations such as from `initialize` are run
  in the order they were declared on import.

* [#10262](https://github.com/leanprover/lean4/pull/10262) adds a new option `maxErrors` that limits the number of errors
  printed from a single `lean` run, defaulting to 100. Processing is
  aborted when the limit is reached, but this is tracked only on a
  per-command level.


````
