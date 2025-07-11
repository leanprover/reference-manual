/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.6.0 (2024-02-29)" =>
%%%
tag := "release-v4.6.0"
file := "v4.6.0"
%%%

````markdown
* Add custom simplification procedures (aka `simproc`s) to `simp`. Simprocs can be triggered by the simplifier on a specified term-pattern. Here is an small example:
  ```lean
  import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

  def foo (x : Nat) : Nat :=
    x + 10

  /--
  The `simproc` `reduceFoo` is invoked on terms that match the pattern `foo _`.
  -/
  simproc reduceFoo (foo _) :=
    /- A term of type `Expr → SimpM Step -/
    fun e => do
      /-
      The `Step` type has three constructors: `.done`, `.visit`, `.continue`.
      * The constructor `.done` instructs `simp` that the result does
        not need to be simplified further.
      * The constructor `.visit` instructs `simp` to visit the resulting expression.
      * The constructor `.continue` instructs `simp` to try other simplification procedures.

      All three constructors take a `Result`. The `.continue` constructor may also take `none`.
      `Result` has two fields `expr` (the new expression), and `proof?` (an optional proof).
       If the new expression is definitionally equal to the input one, then `proof?` can be omitted or set to `none`.
      -/
      /- `simp` uses matching modulo reducibility. So, we ensure the term is a `foo`-application. -/
      unless e.isAppOfArity ``foo 1 do
        return .continue
      /- `Nat.fromExpr?` tries to convert an expression into a `Nat` value -/
      let some n ← Nat.fromExpr? e.appArg!
        | return .continue
      return .done { expr := Lean.mkNatLit (n+10) }
  ```
  We disable simprocs support by using the command `set_option simprocs false`. This command is particularly useful when porting files to v4.6.0.
  Simprocs can be scoped, manually added to `simp` commands, and suppressed using `-`. They are also supported by `simp?`. `simp only` does not execute any `simproc`. Here are some examples for the `simproc` defined above.
  ```lean
  example : x + foo 2 = 12 + x := by
    set_option simprocs false in
      /- This `simp` command does not make progress since `simproc`s are disabled. -/
      fail_if_success simp
    simp_arith

  example : x + foo 2 = 12 + x := by
    /- `simp only` must not use the default simproc set. -/
    fail_if_success simp only
    simp_arith

  example : x + foo 2 = 12 + x := by
    /-
    `simp only` does not use the default simproc set,
    but we can provide simprocs as arguments. -/
    simp only [reduceFoo]
    simp_arith

  example : x + foo 2 = 12 + x := by
    /- We can use `-` to disable `simproc`s. -/
    fail_if_success simp [-reduceFoo]
    simp_arith
  ```
  The command `register_simp_attr <id>` now creates a `simp` **and** a `simproc` set with the name `<id>`. The following command instructs Lean to insert the `reduceFoo` simplification procedure into the set `my_simp`. If no set is specified, Lean uses the default `simp` set.
  ```lean
  simproc [my_simp] reduceFoo (foo _) := ...
  ```

* The syntax of the `termination_by` and `decreasing_by` termination hints is overhauled:

  * They are now placed directly after the function they apply to, instead of
    after the whole `mutual` block.
  * Therefore, the function name no longer has to be mentioned in the hint.
  * If the function has a `where` clause, the `termination_by` and
    `decreasing_by` for that function come before the `where`. The
    functions in the `where` clause can have their own termination hints, each
    following the corresponding definition.
  * The `termination_by` clause can only bind “extra parameters”, that are not
    already bound by the function header, but are bound in a lambda (`:= fun x
    y z =>`) or in patterns (`| x, n + 1 => …`). These extra parameters used to
    be understood as a suffix of the function parameters; now it is a prefix.

  Migration guide: In simple cases just remove the function name, and any
  variables already bound at the header.
  ```diff
   def foo : Nat → Nat → Nat := …
  -termination_by foo a b => a - b
  +termination_by a b => a - b
  ```
  or
  ```diff
   def foo : Nat → Nat → Nat := …
  -termination_by _ a b => a - b
  +termination_by a b => a - b
  ```

  If the parameters are bound in the function header (before the `:`), remove them as well:
  ```diff
   def foo (a b : Nat) : Nat := …
  -termination_by foo a b => a - b
  +termination_by a - b
  ```

  Else, if there are multiple extra parameters, make sure to refer to the right
  ones; the bound variables are interpreted from left to right, no longer from
  right to left:
  ```diff
   def foo : Nat → Nat → Nat → Nat
     | a, b, c => …
  -termination_by foo b c => b
  +termination_by a b => b
  ```

  In the case of a `mutual` block, place the termination arguments (without the
  function name) next to the function definition:
  ```diff
  -mutual
  -def foo : Nat → Nat → Nat := …
  -def bar : Nat → Nat := …
  -end
  -termination_by
  -  foo a b => a - b
  -  bar a => a
  +mutual
  +def foo : Nat → Nat → Nat := …
  +termination_by a b => a - b
  +def bar : Nat → Nat := …
  +termination_by a => a
  +end
  ```

  Similarly, if you have (mutual) recursion through `where` or `let rec`, the
  termination hints are now placed directly after the function they apply to:
  ```diff
  -def foo (a b : Nat) : Nat := …
  -  where bar (x : Nat) : Nat := …
  -termination_by
  -  foo a b => a - b
  -  bar x => x
  +def foo (a b : Nat) : Nat := …
  +termination_by a - b
  +  where
  +    bar (x : Nat) : Nat := …
  +    termination_by x

  -def foo (a b : Nat) : Nat :=
  -  let rec bar (x : Nat) :  Nat := …
  -  …
  -termination_by
  -  foo a b => a - b
  -  bar x => x
  +def foo (a b : Nat) : Nat :=
  +  let rec bar (x : Nat) : Nat := …
  +    termination_by x
  +  …
  +termination_by a - b
  ```

  In cases where a single `decreasing_by` clause applied to multiple mutually
  recursive functions before, the tactic now has to be duplicated.

* The semantics of `decreasing_by` changed; the tactic is applied to all
  termination proof goals together, not individually.

  This helps when writing termination proofs interactively, as one can focus
  each subgoal individually, for example using `·`. Previously, the given
  tactic script had to work for _all_ goals, and one had to resort to tactic
  combinators like `first`:

  ```diff
   def foo (n : Nat) := … foo e1 … foo e2 …
  -decreasing_by
  -simp_wf
  -first | apply something_about_e1; …
  -      | apply something_about_e2; …
  +decreasing_by
  +all_goals simp_wf
  +· apply something_about_e1; …
  +· apply something_about_e2; …
  ```

  To obtain the old behaviour of applying a tactic to each goal individually,
  use `all_goals`:
  ```diff
   def foo (n : Nat) := …
  -decreasing_by some_tactic
  +decreasing_by all_goals some_tactic
  ```

  In the case of mutual recursion each `decreasing_by` now applies to just its
  function. If some functions in a recursive group do not have their own
  `decreasing_by`, the default `decreasing_tactic` is used. If the same tactic
  ought to be applied to multiple functions, the `decreasing_by` clause has to
  be repeated at each of these functions.

* Modify `InfoTree.context` to facilitate augmenting it with partial contexts while elaborating a command. This breaks backwards compatibility with all downstream projects that traverse the `InfoTree` manually instead of going through the functions in `InfoUtils.lean`, as well as those manually creating and saving `InfoTree`s. See [PR #3159](https://github.com/leanprover/lean4/pull/3159) for how to migrate your code.

* Add language server support for [call hierarchy requests](https://www.youtube.com/watch?v=r5LA7ivUb2c) ([PR #3082](https://github.com/leanprover/lean4/pull/3082)). The change to the .ilean format in this PR means that projects must be fully rebuilt once in order to generate .ilean files with the new format before features like "find references" work correctly again.

* Structure instances with multiple sources (for example `{a, b, c with x := 0}`) now have their fields filled from these sources
  in strict left-to-right order. Furthermore, the structure instance elaborator now aggressively use sources to fill in subobject
  fields, which prevents unnecessary eta expansion of the sources,
  and hence greatly reduces the reliance on costly structure eta reduction. This has a large impact on mathlib,
  reducing total CPU instructions by 3% and enabling impactful refactors like leanprover-community/mathlib4#8386
  which reduces the build time by almost 20%.
  See [PR #2478](https://github.com/leanprover/lean4/pull/2478) and [RFC #2451](https://github.com/leanprover/lean4/issues/2451).

* Add pretty printer settings to omit deeply nested terms (`pp.deepTerms false` and `pp.deepTerms.threshold`) ([PR #3201](https://github.com/leanprover/lean4/pull/3201))

* Add pretty printer options `pp.numeralTypes` and `pp.natLit`.
  When `pp.numeralTypes` is true, then natural number literals, integer literals, and rational number literals
  are pretty printed with type ascriptions, such as `(2 : Rat)`, `(-2 : Rat)`, and `(-2 / 3 : Rat)`.
  When `pp.natLit` is true, then raw natural number literals are pretty printed as `nat_lit 2`.
  [PR #2933](https://github.com/leanprover/lean4/pull/2933) and [RFC #3021](https://github.com/leanprover/lean4/issues/3021).

Lake updates:
* improved platform information & control [#3226](https://github.com/leanprover/lean4/pull/3226)
* `lake update` from unsupported manifest versions [#3149](https://github.com/leanprover/lean4/pull/3149)

Other improvements:
* make `intro` be aware of `let_fun` [#3115](https://github.com/leanprover/lean4/pull/3115)
* produce simpler proof terms in `rw` [#3121](https://github.com/leanprover/lean4/pull/3121)
* fuse nested `mkCongrArg` calls in proofs generated by `simp` [#3203](https://github.com/leanprover/lean4/pull/3203)
* `induction using` followed by a general term [#3188](https://github.com/leanprover/lean4/pull/3188)
* allow generalization in `let` [#3060](https://github.com/leanprover/lean4/pull/3060), fixing [#3065](https://github.com/leanprover/lean4/issues/3065)
* reducing out-of-bounds `swap!` should return `a`, not `default`` [#3197](https://github.com/leanprover/lean4/pull/3197), fixing [#3196](https://github.com/leanprover/lean4/issues/3196)
* derive `BEq` on structure with `Prop`-fields [#3191](https://github.com/leanprover/lean4/pull/3191), fixing [#3140](https://github.com/leanprover/lean4/issues/3140)
* refine through more `casesOnApp`/`matcherApp` [#3176](https://github.com/leanprover/lean4/pull/3176), fixing [#3175](https://github.com/leanprover/lean4/pull/3175)
* do not strip dotted components from lean module names [#2994](https://github.com/leanprover/lean4/pull/2994), fixing [#2999](https://github.com/leanprover/lean4/issues/2999)
* fix `deriving` only deriving the first declaration for some handlers [#3058](https://github.com/leanprover/lean4/pull/3058), fixing [#3057](https://github.com/leanprover/lean4/issues/3057)
* do not instantiate metavariables in kabstract/rw for disallowed occurrences [#2539](https://github.com/leanprover/lean4/pull/2539), fixing [#2538](https://github.com/leanprover/lean4/issues/2538)
* hover info for `cases h : ...` [#3084](https://github.com/leanprover/lean4/pull/3084)
````
