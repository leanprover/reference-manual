/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.11.0 (2024-09-02)" =>
%%%
tag := "release-v4.11.0"
file := "v4.11.0"
%%%

````markdown
### Language features, tactics, and metaprograms

* The variable inclusion mechanism has been changed. Like before, when a definition mentions a variable, Lean will add it as an argument of the definition, but now in theorem bodies, variables are not included based on usage in order to ensure that changes to the proof cannot change the statement of the overall theorem. Instead, variables are only available to the proof if they have been mentioned in the theorem header or in an **`include` command** or are instance implicit and depend only on such variables. The **`omit` command** can be used to omit included variables.

  See breaking changes below.

  PRs: [#4883](https://github.com/leanprover/lean4/pull/4883), [#4814](https://github.com/leanprover/lean4/pull/4814), [#5000](https://github.com/leanprover/lean4/pull/5000), [#5036](https://github.com/leanprover/lean4/pull/5036), [#5138](https://github.com/leanprover/lean4/pull/5138), [0edf1b](https://github.com/leanprover/lean4/commit/0edf1bac392f7e2fe0266b28b51c498306363a84).

* **Recursive definitions**
  * Structural recursion can now be explicitly requested using
    ```
    termination_by structural x
    ```
    in analogy to the existing `termination_by x` syntax that causes well-founded recursion to be used.
    [#4542](https://github.com/leanprover/lean4/pull/4542)
  * [#4672](https://github.com/leanprover/lean4/pull/4672) fixes a bug that could lead to ill-typed terms.
  * The `termination_by?` syntax no longer forces the use of well-founded recursion, and when structural
    recursion is inferred, it will print the result using the `termination_by structural` syntax.
  * **Mutual structural recursion** is now supported. This feature supports both mutual recursion over a non-mutual
    data type, as well as recursion over mutual or nested data types:

    ```lean
    mutual
    def Even : Nat → Prop
      | 0 => True
      | n+1 => Odd n

    def Odd : Nat → Prop
      | 0 => False
      | n+1 => Even n
    end

    mutual
    inductive A
    | other : B → A
    | empty
    inductive B
    | other : A → B
    | empty
    end

    mutual
    def A.size : A → Nat
    | .other b => b.size + 1
    | .empty => 0

    def B.size : B → Nat
    | .other a => a.size + 1
    | .empty => 0
    end

    inductive Tree where | node : List Tree → Tree

    mutual
    def Tree.size : Tree → Nat
    | node ts => Tree.list_size ts

    def Tree.list_size : List Tree → Nat
    | [] => 0
    | t::ts => Tree.size t + Tree.list_size ts
    end
    ```

    Functional induction principles are generated for these functions as well (`A.size.induct`, `A.size.mutual_induct`).

    Nested structural recursion is still not supported.

    PRs: [#4639](https://github.com/leanprover/lean4/pull/4639), [#4715](https://github.com/leanprover/lean4/pull/4715), [#4642](https://github.com/leanprover/lean4/pull/4642), [#4656](https://github.com/leanprover/lean4/pull/4656), [#4684](https://github.com/leanprover/lean4/pull/4684), [#4715](https://github.com/leanprover/lean4/pull/4715), [#4728](https://github.com/leanprover/lean4/pull/4728), [#4575](https://github.com/leanprover/lean4/pull/4575), [#4731](https://github.com/leanprover/lean4/pull/4731), [#4658](https://github.com/leanprover/lean4/pull/4658), [#4734](https://github.com/leanprover/lean4/pull/4734), [#4738](https://github.com/leanprover/lean4/pull/4738), [#4718](https://github.com/leanprover/lean4/pull/4718), [#4733](https://github.com/leanprover/lean4/pull/4733), [#4787](https://github.com/leanprover/lean4/pull/4787), [#4788](https://github.com/leanprover/lean4/pull/4788), [#4789](https://github.com/leanprover/lean4/pull/4789), [#4807](https://github.com/leanprover/lean4/pull/4807), [#4772](https://github.com/leanprover/lean4/pull/4772)
  * [#4809](https://github.com/leanprover/lean4/pull/4809) makes unnecessary `termination_by` clauses cause warnings, not errors.
  * [#4831](https://github.com/leanprover/lean4/pull/4831) improves handling of nested structural recursion through non-recursive types.
  * [#4839](https://github.com/leanprover/lean4/pull/4839) improves support for structural recursive over inductive predicates when there are reflexive arguments.
* `simp` tactic
  * [#4784](https://github.com/leanprover/lean4/pull/4784) sets configuration `Simp.Config.implicitDefEqProofs` to `true` by default.

* `omega` tactic
  * [#4612](https://github.com/leanprover/lean4/pull/4612) normalizes the order that constraints appear in error messages.
  * [#4695](https://github.com/leanprover/lean4/pull/4695) prevents pushing casts into multiplications unless it produces a non-trivial linear combination.
  * [#4989](https://github.com/leanprover/lean4/pull/4989) fixes a regression.

* `decide` tactic
  * [#4711](https://github.com/leanprover/lean4/pull/4711) switches from using default transparency to *at least* default transparency when reducing the `Decidable` instance.
  * [#4674](https://github.com/leanprover/lean4/pull/4674) adds detailed feedback on `decide` tactic failure. It tells you which `Decidable` instances it unfolded, if it get stuck on `Eq.rec` it gives a hint about avoiding tactics when defining `Decidable` instances, and if it gets stuck on `Classical.choice` it gives hints about classical instances being in scope. During this process, it processes `Decidable.rec`s and matches to pin blame on a non-reducing instance.

* `@[ext]` attribute
  * [#4543](https://github.com/leanprover/lean4/pull/4543) and [#4762](https://github.com/leanprover/lean4/pull/4762) make `@[ext]` realize `ext_iff` theorems from user `ext` theorems. Fixes the attribute so that `@[local ext]` and `@[scoped ext]` are usable. The `@[ext (iff := false)]` option can be used to turn off `ext_iff` realization.
  * [#4694](https://github.com/leanprover/lean4/pull/4694) makes "go to definition" work for the generated lemmas. Also adjusts the core library to make use of `ext_iff` generation.
  * [#4710](https://github.com/leanprover/lean4/pull/4710) makes `ext_iff` theorem preserve inst implicit binder types, rather than making all binder types implicit.

* `#eval` command
  * [#4810](https://github.com/leanprover/lean4/pull/4810) introduces a safer `#eval` command that prevents evaluation of terms that contain `sorry`. The motivation is that failing tactics, in conjunction with operations such as array accesses, can lead to the Lean process crashing. Users can use the new `#eval!` command to use the previous unsafe behavior. ([#4829](https://github.com/leanprover/lean4/pull/4829) adjusts a test.)

* [#4447](https://github.com/leanprover/lean4/pull/4447) adds `#discr_tree_key` and `#discr_tree_simp_key` commands, for helping debug discrimination tree failures. The `#discr_tree_key t` command prints the discrimination tree keys for a term `t` (or, if it is a single identifier, the type of that constant). It uses the default configuration for generating keys. The `#discr_tree_simp_key` command is similar to `#discr_tree_key`, but treats the underlying type as one of a simp lemma, that is it transforms it into an equality and produces the key of the left-hand side.

  For example,
  ```
  #discr_tree_key (∀ {a n : Nat}, bar a (OfNat.ofNat n))
  -- bar _ (@OfNat.ofNat Nat _ _)

  #discr_tree_simp_key Nat.add_assoc
  -- @HAdd.hAdd Nat Nat Nat _ (@HAdd.hAdd Nat Nat Nat _ _ _) _
  ```

* [#4741](https://github.com/leanprover/lean4/pull/4741) changes option parsing to allow user-defined options from the command line. Initial options are now re-parsed and validated after importing. Command line option assignments prefixed with `weak.` are silently discarded if the option name without the prefix does not exist.

* **Deriving handlers**
  * [7253ef](https://github.com/leanprover/lean4/commit/7253ef8751f76bcbe0e6f46dcfa8069699a2bac7) and [a04f3c](https://github.com/leanprover/lean4/commit/a04f3cab5a9fe2870825af6544ca13c5bb766706) improve the construction of the `BEq` deriving handler.
  * [86af04](https://github.com/leanprover/lean4/commit/86af04cc08c0dbbe0e735ea13d16edea3465f850) makes `BEq` deriving handler work when there are dependently typed fields.
  * [#4826](https://github.com/leanprover/lean4/pull/4826) refactors the `DecidableEq` deriving handle to use `termination_by structural`.

* **Metaprogramming**
  * [#4593](https://github.com/leanprover/lean4/pull/4593) adds `unresolveNameGlobalAvoidingLocals`.
  * [#4618](https://github.com/leanprover/lean4/pull/4618) deletes deprecated functions from 2022.
  * [#4642](https://github.com/leanprover/lean4/pull/4642) adds `Meta.lambdaBoundedTelescope`.
  * [#4731](https://github.com/leanprover/lean4/pull/4731) adds `Meta.withErasedFVars`, to enter a context with some fvars erased from the local context.
  * [#4777](https://github.com/leanprover/lean4/pull/4777) adds assignment validation at `closeMainGoal`, preventing users from circumventing the occurs check for tactics such as `exact`.
  * [#4807](https://github.com/leanprover/lean4/pull/4807) introduces `Lean.Meta.PProdN` module for packing and projecting nested `PProd`s.
  * [#5170](https://github.com/leanprover/lean4/pull/5170) fixes `Syntax.unsetTrailing`. A consequence of this is that "go to definition" now works on the last module name in an `import` block (issue [#4958](https://github.com/leanprover/lean4/issues/4958)).


### Language server, widgets, and IDE extensions

* [#4727](https://github.com/leanprover/lean4/pull/4727) makes it so that responses to info view requests come as soon as the relevant tactic has finished execution.
* [#4580](https://github.com/leanprover/lean4/pull/4580) makes it so that whitespace changes do not invalidate imports, and so starting to type the first declaration after imports should no longer cause them to reload.
* [#4780](https://github.com/leanprover/lean4/pull/4780) fixes an issue where hovering over unimported builtin names could result in a panic.

### Pretty printing

* [#4558](https://github.com/leanprover/lean4/pull/4558) fixes the `pp.instantiateMVars` setting and changes the default value to `true`.
* [#4631](https://github.com/leanprover/lean4/pull/4631) makes sure syntax nodes always run their formatters. Fixes an issue where if `ppSpace` appears in a `macro` or `elab` command then it does not format with a space.
* [#4665](https://github.com/leanprover/lean4/pull/4665) fixes a bug where pretty printed signatures (for example in `#check`) were overly hoverable due to `pp.tagAppFns` being set.
* [#4724](https://github.com/leanprover/lean4/pull/4724) makes `match` pretty printer be sensitive to `pp.explicit`, which makes hovering over a `match` in the Infoview show the underlying term.
* [#4764](https://github.com/leanprover/lean4/pull/4764) documents why anonymous constructor notation isn't pretty printed with flattening.
* [#4786](https://github.com/leanprover/lean4/pull/4786) adjusts the parenthesizer so that only the parentheses are hoverable, implemented by having the parentheses "steal" the term info from the parenthesized expression.
* [#4854](https://github.com/leanprover/lean4/pull/4854) allows arbitrarily long sequences of optional arguments to be omitted from the end of applications, versus the previous conservative behavior of omitting up to one optional argument.

### Library

* `Nat`
  * [#4597](https://github.com/leanprover/lean4/pull/4597) adds bitwise lemmas `Nat.and_le_(left|right)`.
  * [#4874](https://github.com/leanprover/lean4/pull/4874) adds simprocs for simplifying bit expressions.
* `Int`
  * [#4903](https://github.com/leanprover/lean4/pull/4903) fixes performance of `HPow Int Nat Int` synthesis by rewriting it as a `NatPow Int` instance.
* `UInt*` and `Fin`
  * [#4605](https://github.com/leanprover/lean4/pull/4605) adds lemmas.
  * [#4629](https://github.com/leanprover/lean4/pull/4629) adds `*.and_toNat`.
* `Option`
  * [#4599](https://github.com/leanprover/lean4/pull/4599) adds `get` lemmas.
  * [#4600](https://github.com/leanprover/lean4/pull/4600) adds `Option.or`, a version of `Option.orElse` that is strict in the second argument.
* `GetElem`
  * [#4603](https://github.com/leanprover/lean4/pull/4603) adds `getElem_congr` to help with rewriting indices.
* `List` and `Array`
  * Upstreamed from Batteries: [#4586](https://github.com/leanprover/lean4/pull/4586) upstreams `List.attach` and `Array.attach`, [#4697](https://github.com/leanprover/lean4/pull/4697) upstreams `List.Subset` and `List.Sublist` and API, [#4706](https://github.com/leanprover/lean4/pull/4706) upstreams basic material on `List.Pairwise` and `List.Nodup`, [#4720](https://github.com/leanprover/lean4/pull/4720) upstreams more `List.erase` API, [#4836](https://github.com/leanprover/lean4/pull/4836) and [#4837](https://github.com/leanprover/lean4/pull/4837) upstream `List.IsPrefix`/`List.IsSuffix`/`List.IsInfix` and add `Decidable` instances, [#4855](https://github.com/leanprover/lean4/pull/4855) upstreams `List.tail`, `List.findIdx`, `List.indexOf`, `List.countP`, `List.count`, and `List.range'`, [#4856](https://github.com/leanprover/lean4/pull/4856) upstreams more List lemmas, [#4866](https://github.com/leanprover/lean4/pull/4866) upstreams `List.pairwise_iff_getElem`, [#4865](https://github.com/leanprover/lean4/pull/4865) upstreams `List.eraseIdx` lemmas.
  * [#4687](https://github.com/leanprover/lean4/pull/4687) adjusts `List.replicate` simp lemmas and simprocs.
  * [#4704](https://github.com/leanprover/lean4/pull/4704) adds characterizations of `List.Sublist`.
  * [#4707](https://github.com/leanprover/lean4/pull/4707) adds simp normal form tests for `List.Pairwise` and `List.Nodup`.
  * [#4708](https://github.com/leanprover/lean4/pull/4708) and [#4815](https://github.com/leanprover/lean4/pull/4815) reorganize lemmas on list getters.
  * [#4765](https://github.com/leanprover/lean4/pull/4765) adds simprocs for literal array accesses such as `#[1,2,3,4,5][2]`.
  * [#4790](https://github.com/leanprover/lean4/pull/4790) removes typeclass assumptions for `List.Nodup.eraseP`.
  * [#4801](https://github.com/leanprover/lean4/pull/4801) adds efficient `usize` functions for array types.
  * [#4820](https://github.com/leanprover/lean4/pull/4820) changes `List.filterMapM` to run left-to-right.
  * [#4835](https://github.com/leanprover/lean4/pull/4835) fills in and cleans up gaps in List API.
  * [#4843](https://github.com/leanprover/lean4/pull/4843), [#4868](https://github.com/leanprover/lean4/pull/4868), and [#4877](https://github.com/leanprover/lean4/pull/4877) correct `List.Subset` lemmas.
  * [#4863](https://github.com/leanprover/lean4/pull/4863) splits `Init.Data.List.Lemmas` into function-specific files.
  * [#4875](https://github.com/leanprover/lean4/pull/4875) fixes statement of `List.take_takeWhile`.
  * Lemmas: [#4602](https://github.com/leanprover/lean4/pull/4602), [#4627](https://github.com/leanprover/lean4/pull/4627), [#4678](https://github.com/leanprover/lean4/pull/4678) for `List.head` and `list.getLast`, [#4723](https://github.com/leanprover/lean4/pull/4723) for `List.erase`, [#4742](https://github.com/leanprover/lean4/pull/4742)
* `ByteArray`
  * [#4582](https://github.com/leanprover/lean4/pull/4582) eliminates `partial` from `ByteArray.toList` and `ByteArray.findIdx?`.
* `BitVec`
  * [#4568](https://github.com/leanprover/lean4/pull/4568) adds recurrence theorems for bitblasting multiplication.
  * [#4571](https://github.com/leanprover/lean4/pull/4571) adds `shiftLeftRec` lemmas.
  * [#4872](https://github.com/leanprover/lean4/pull/4872) adds `ushiftRightRec` and lemmas.
  * [#4873](https://github.com/leanprover/lean4/pull/4873) adds `getLsb_replicate`.
* `Std.HashMap` added:
  * [#4583](https://github.com/leanprover/lean4/pull/4583) **adds `Std.HashMap`** as a verified replacement for `Lean.HashMap`. See the PR for naming differences, but [#4725](https://github.com/leanprover/lean4/pull/4725) renames `HashMap.remove` to `HashMap.erase`.
  * [#4682](https://github.com/leanprover/lean4/pull/4682) adds `Inhabited` instances.
  * [#4732](https://github.com/leanprover/lean4/pull/4732) improves `BEq` argument order in hash map lemmas.
  * [#4759](https://github.com/leanprover/lean4/pull/4759) makes lemmas resolve instances via unification.
  * [#4771](https://github.com/leanprover/lean4/pull/4771) documents that hash maps should be used linearly to avoid expensive copies.
  * [#4791](https://github.com/leanprover/lean4/pull/4791) removes `bif` from hash map lemmas, which is inconvenient to work with in practice.
  * [#4803](https://github.com/leanprover/lean4/pull/4803) adds more lemmas.
* `SMap`
  * [#4690](https://github.com/leanprover/lean4/pull/4690) upstreams `SMap.foldM`.
* `BEq`
  * [#4607](https://github.com/leanprover/lean4/pull/4607) adds `PartialEquivBEq`, `ReflBEq`, `EquivBEq`, and `LawfulHashable` classes.
* `IO`
  * [#4660](https://github.com/leanprover/lean4/pull/4660) adds `IO.Process.Child.tryWait`.
* [#4747](https://github.com/leanprover/lean4/pull/4747), [#4730](https://github.com/leanprover/lean4/pull/4730), and [#4756](https://github.com/leanprover/lean4/pull/4756) add `×'` syntax for `PProd`. Adds a delaborator for `PProd` and `MProd` values to pretty print as flattened angle bracket tuples.
* **Other fixes or improvements**
  * [#4604](https://github.com/leanprover/lean4/pull/4604) adds lemmas for cond.
  * [#4619](https://github.com/leanprover/lean4/pull/4619) changes some definitions into theorems.
  * [#4616](https://github.com/leanprover/lean4/pull/4616) fixes some names with duplicated namespaces.
  * [#4620](https://github.com/leanprover/lean4/pull/4620) fixes simp lemmas flagged by the simpNF linter.
  * [#4666](https://github.com/leanprover/lean4/pull/4666) makes the `Antisymm` class be a `Prop`.
  * [#4621](https://github.com/leanprover/lean4/pull/4621) cleans up unused arguments flagged by linter.
  * [#4680](https://github.com/leanprover/lean4/pull/4680) adds imports for orphaned `Init` modules.
  * [#4679](https://github.com/leanprover/lean4/pull/4679) adds imports for orphaned `Std.Data` modules.
  * [#4688](https://github.com/leanprover/lean4/pull/4688) adds forward and backward directions of `not_exists`.
  * [#4689](https://github.com/leanprover/lean4/pull/4689) upstreams `eq_iff_true_of_subsingleton`.
  * [#4709](https://github.com/leanprover/lean4/pull/4709) fixes precedence handling for `Repr` instances for negative numbers for `Int` and `Float`.
  * [#4760](https://github.com/leanprover/lean4/pull/4760) renames `TC` ("transitive closure") to `Relation.TransGen`.
  * [#4842](https://github.com/leanprover/lean4/pull/4842) fixes `List` deprecations.
  * [#4852](https://github.com/leanprover/lean4/pull/4852) upstreams some Mathlib attributes applied to lemmas.
  * [93ac63](https://github.com/leanprover/lean4/commit/93ac635a89daa5a8e8ef33ec96b0bcbb5d7ec1ea) improves proof.
  * [#4862](https://github.com/leanprover/lean4/pull/4862) and [#4878](https://github.com/leanprover/lean4/pull/4878) generalize the universe for `PSigma.exists` and rename it to `Exists.of_psigma_prop`.
  * Typos: [#4737](https://github.com/leanprover/lean4/pull/4737), [7d2155](https://github.com/leanprover/lean4/commit/7d2155943c67c743409420b4546d47fadf73af1c)
  * Docs: [#4782](https://github.com/leanprover/lean4/pull/4782), [#4869](https://github.com/leanprover/lean4/pull/4869), [#4648](https://github.com/leanprover/lean4/pull/4648)

### Lean internals
* **Elaboration**
  * [#4596](https://github.com/leanprover/lean4/pull/4596) enforces `isDefEqStuckEx` at `unstuckMVar` procedure, causing isDefEq to throw a stuck defeq exception if the metavariable was created in a previous level. This results in some better error messages, and it helps `rw` succeed in synthesizing instances (see issue [#2736](https://github.com/leanprover/lean4/issues/2736)).
  * [#4713](https://github.com/leanprover/lean4/pull/4713) fixes deprecation warnings when there are overloaded symbols.
  * `elab_as_elim` algorithm:
    * [#4722](https://github.com/leanprover/lean4/pull/4722) adds check that inferred motive is type-correct.
    * [#4800](https://github.com/leanprover/lean4/pull/4800) elaborates arguments for parameters appearing in the types of targets.
    * [#4817](https://github.com/leanprover/lean4/pull/4817) makes the algorithm correctly handle eliminators with explicit motive arguments.
  * [#4792](https://github.com/leanprover/lean4/pull/4792) adds term elaborator for `Lean.Parser.Term.namedPattern` (e.g. `n@(n' + 1)`) to report errors when used in non-pattern-matching contexts.
  * [#4818](https://github.com/leanprover/lean4/pull/4818) makes anonymous dot notation work when the expected type is a pi-type-valued type synonym.
* **Typeclass inference**
  * [#4646](https://github.com/leanprover/lean4/pull/4646) improves `synthAppInstances`, the function responsible for synthesizing instances for the `rw` and `apply` tactics. Adds a synthesis loop to handle functions whose instances need to be synthesized in a complex order.
* **Inductive types**
  * [#4684](https://github.com/leanprover/lean4/pull/4684) (backported as [98ee78](https://github.com/leanprover/lean4/commit/98ee789990f91ff5935627787b537911ef8773c4)) refactors `InductiveVal` to have a `numNested : Nat` field instead of `isNested : Bool`. This modifies the kernel.
* **Definitions**
  * [#4776](https://github.com/leanprover/lean4/pull/4776) improves performance of `Replacement.apply`.
  * [#4712](https://github.com/leanprover/lean4/pull/4712) fixes `.eq_def` theorem generation with messy universes.
  * [#4841](https://github.com/leanprover/lean4/pull/4841) improves success of finding `T.below x` hypothesis when transforming `match` statements for `IndPredBelow`.
* **Diagnostics and profiling**
  * [#4611](https://github.com/leanprover/lean4/pull/4611) makes kernel diagnostics appear when `diagnostics` is enabled even if it is the only section.
  * [#4753](https://github.com/leanprover/lean4/pull/4753) adds missing `profileitM` functions.
  * [#4754](https://github.com/leanprover/lean4/pull/4754) adds `Lean.Expr.numObjs` to compute the number of allocated sub-expressions in a given expression, primarily for diagnosing performance issues.
  * [#4769](https://github.com/leanprover/lean4/pull/4769) adds missing `withTraceNode`s to improve `trace.profiler` output.
  * [#4781](https://github.com/leanprover/lean4/pull/4781) and [#4882](https://github.com/leanprover/lean4/pull/4882) make the "use `set_option diagnostics true`" message be conditional on current setting of `diagnostics`.
* **Performance**
  * [#4767](https://github.com/leanprover/lean4/pull/4767), [#4775](https://github.com/leanprover/lean4/pull/4775), and [#4887](https://github.com/leanprover/lean4/pull/4887) add `ShareCommon.shareCommon'` for sharing common terms. In an example with 16 million subterms, it is 20 times faster than the old `shareCommon` procedure.
  * [#4779](https://github.com/leanprover/lean4/pull/4779) ensures `Expr.replaceExpr` preserves DAG structure in `Expr`s.
  * [#4783](https://github.com/leanprover/lean4/pull/4783) documents performance issue in `Expr.replaceExpr`.
  * [#4794](https://github.com/leanprover/lean4/pull/4794), [#4797](https://github.com/leanprover/lean4/pull/4797), [#4798](https://github.com/leanprover/lean4/pull/4798) make `for_each` use precise cache.
  * [#4795](https://github.com/leanprover/lean4/pull/4795) makes `Expr.find?` and `Expr.findExt?` use the kernel implementations.
  * [#4799](https://github.com/leanprover/lean4/pull/4799) makes `Expr.replace` use the kernel implementation.
  * [#4871](https://github.com/leanprover/lean4/pull/4871) makes `Expr.foldConsts` use a precise cache.
  * [#4890](https://github.com/leanprover/lean4/pull/4890) makes `expr_eq_fn` use a precise cache.
* **Utilities**
  * [#4453](https://github.com/leanprover/lean4/pull/4453) upstreams `ToExpr FilePath` and `compile_time_search_path%`.
* **Module system**
  * [#4652](https://github.com/leanprover/lean4/pull/4652) fixes handling of `const2ModIdx` in `finalizeImport`, making it prefer the original module for a declaration when a declaration is re-declared.
* **Kernel**
  * [#4637](https://github.com/leanprover/lean4/pull/4637) adds a check to prevent large `Nat` exponentiations from evaluating. Elaborator reduction is controlled by the option `exponentiation.threshold`.
  * [#4683](https://github.com/leanprover/lean4/pull/4683) updates comments in `kernel/declaration.h`, making sure they reflect the current Lean 4 types.
  * [#4796](https://github.com/leanprover/lean4/pull/4796) improves performance by using `replace` with a precise cache.
  * [#4700](https://github.com/leanprover/lean4/pull/4700) improves performance by fixing the implementation of move constructors and move assignment operators. Expression copying was taking 10% of total runtime in some workloads. See issue [#4698](https://github.com/leanprover/lean4/issues/4698).
  * [#4702](https://github.com/leanprover/lean4/pull/4702) improves performance in `replace_rec_fn::apply` by avoiding expression copies. These copies represented about 13% of time spent in `save_result` in some workloads. See the same issue.
* **Other fixes or improvements**
  * [#4590](https://github.com/leanprover/lean4/pull/4590) fixes a typo in some constants and `trace.profiler.useHeartbeats`.
  * [#4617](https://github.com/leanprover/lean4/pull/4617) add 'since' dates to `deprecated` attributes.
  * [#4625](https://github.com/leanprover/lean4/pull/4625) improves the robustness of the constructor-as-variable test.
  * [#4740](https://github.com/leanprover/lean4/pull/4740) extends test with nice example reported on Zulip.
  * [#4766](https://github.com/leanprover/lean4/pull/4766) moves `Syntax.hasIdent` to be available earlier and shakes dependencies.
  * [#4881](https://github.com/leanprover/lean4/pull/4881) splits out `Lean.Language.Lean.Types`.
  * [#4893](https://github.com/leanprover/lean4/pull/4893) adds `LEAN_EXPORT` for `sharecommon` functions.
  * Typos: [#4635](https://github.com/leanprover/lean4/pull/4635), [#4719](https://github.com/leanprover/lean4/pull/4719), [af40e6](https://github.com/leanprover/lean4/commit/af40e618111581c82fc44de922368a02208b499f)
  * Docs: [#4748](https://github.com/leanprover/lean4/pull/4748) (`Command.Scope`)

### Compiler, runtime, and FFI
* [#4661](https://github.com/leanprover/lean4/pull/4661) moves `Std` from `libleanshared` to much smaller `libInit_shared`. This fixes the Windows build.
* [#4668](https://github.com/leanprover/lean4/pull/4668) fixes initialization, explicitly initializing `Std` in `lean_initialize`.
* [#4746](https://github.com/leanprover/lean4/pull/4746) adjusts `shouldExport` to exclude more symbols to get below Windows symbol limit. Some exceptions are added by [#4884](https://github.com/leanprover/lean4/pull/4884) and [#4956](https://github.com/leanprover/lean4/pull/4956) to support Verso.
* [#4778](https://github.com/leanprover/lean4/pull/4778) adds `lean_is_exclusive_obj` (`Lean.isExclusiveUnsafe`) and `lean_set_external_data`.
* [#4515](https://github.com/leanprover/lean4/pull/4515) fixes calling programs with spaces on Windows.

### Lake

* [#4735](https://github.com/leanprover/lean4/pull/4735) improves a number of elements related to Git checkouts, cloud releases,
and related error handling.

  * On error, Lake now prints all top-level logs. Top-level logs are those produced by Lake outside of the job monitor (e.g., when cloning dependencies).
  * When fetching a remote for a dependency, Lake now forcibly fetches tags. This prevents potential errors caused by a repository recreating tags already fetched.
  * Git error handling is now more informative.
  * The builtin package facets `release`, `optRelease`, `extraDep` are now captions in the same manner as other facets.
  * `afterReleaseSync` and `afterReleaseAsync` now fetch `optRelease` rather than `release`.
  * Added support for optional jobs, whose failure does not cause the whole build to failure. Now `optRelease` is such a job.

* [#4608](https://github.com/leanprover/lean4/pull/4608) adds draft CI workflow when creating new projects.
* [#4847](https://github.com/leanprover/lean4/pull/4847) adds CLI options to control log levels. The `--log-level=<lv>` controls the minimum log level Lake should output. For instance, `--log-level=error` will only print errors (not warnings or info). Also, adds an analogous `--fail-level` option to control the minimum log level for build failures. The existing `--iofail` and `--wfail` options are respectively equivalent to `--fail-level=info` and `--fail-level=warning`.

* Docs: [#4853](https://github.com/leanprover/lean4/pull/4853)


### DevOps/CI

* **Workflows**
  * [#4531](https://github.com/leanprover/lean4/pull/4531) makes release trigger an update of `release.lean-lang.org`.
  * [#4598](https://github.com/leanprover/lean4/pull/4598) adjusts `pr-release` to the new `lakefile.lean` syntax.
  * [#4632](https://github.com/leanprover/lean4/pull/4632) makes `pr-release` use the correct tag name.
  * [#4638](https://github.com/leanprover/lean4/pull/4638) adds ability to manually trigger nightly release.
  * [#4640](https://github.com/leanprover/lean4/pull/4640) adds more debugging output for `restart-on-label` CI.
  * [#4663](https://github.com/leanprover/lean4/pull/4663) bumps up waiting for 10s to 30s for `restart-on-label`.
  * [#4664](https://github.com/leanprover/lean4/pull/4664) bumps versions for `actions/checkout` and `actions/upload-artifacts`.
  * [582d6e](https://github.com/leanprover/lean4/commit/582d6e7f7168e0dc0819099edaace27d913b893e) bumps version for `actions/download-artifact`.
  * [6d9718](https://github.com/leanprover/lean4/commit/6d971827e253a4dc08cda3cf6524d7f37819eb47) adds back dropped `check-stage3`.
  * [0768ad](https://github.com/leanprover/lean4/commit/0768ad4eb9020af0777587a25a692d181e857c14) adds Jira sync (for FRO).
  * [#4830](https://github.com/leanprover/lean4/pull/4830) adds support to report CI errors on FRO Zulip.
  * [#4838](https://github.com/leanprover/lean4/pull/4838) adds trigger for `nightly_bump_toolchain` on mathlib4 upon nightly release.
  * [abf420](https://github.com/leanprover/lean4/commit/abf4206e9c0fcadf17b6f7933434fd1580175015) fixes msys2.
  * [#4895](https://github.com/leanprover/lean4/pull/4895) deprecates Nix-based builds and removes interactive components. Users who prefer the flake build should maintain it externally.
* [#4693](https://github.com/leanprover/lean4/pull/4693), [#4458](https://github.com/leanprover/lean4/pull/4458), and [#4876](https://github.com/leanprover/lean4/pull/4876) update the **release checklist**.
* [#4669](https://github.com/leanprover/lean4/pull/4669) fixes the "max dynamic symbols" metric per static library.
* [#4691](https://github.com/leanprover/lean4/pull/4691) improves compatibility of `tests/list_simp` for retesting simp normal forms with Mathlib.
* [#4806](https://github.com/leanprover/lean4/pull/4806) updates the quickstart guide.
* [c02aa9](https://github.com/leanprover/lean4/commit/c02aa98c6a08c3a9b05f68039c071085a4ef70d7) documents the **triage team** in the contribution guide.


### Breaking changes

* For `@[ext]`-generated `ext` and `ext_iff` lemmas, the `x` and `y` term arguments are now implicit. Furthermore these two lemmas are now protected ([#4543](https://github.com/leanprover/lean4/pull/4543)).

* Now `trace.profiler.useHearbeats` is `trace.profiler.useHeartbeats` ([#4590](https://github.com/leanprover/lean4/pull/4590)).

* A bugfix in the structural recursion code may in some cases break existing code, when a parameter of the type of the recursive argument is bound behind indices of that type. This can usually be fixed by reordering the parameters of the function ([#4672](https://github.com/leanprover/lean4/pull/4672)).

* Now `List.filterMapM` sequences monadic actions left-to-right ([#4820](https://github.com/leanprover/lean4/pull/4820)).

* The effect of the `variable` command on proofs of `theorem`s has been changed. Whether such section variables are accessible in the proof now depends only on the theorem signature and other top-level commands, not on the proof itself. This change ensures that
  * the statement of a theorem is independent of its proof. In other words, changes in the proof cannot change the theorem statement.
  * tactics such as `induction` cannot accidentally include a section variable.
  * the proof can be elaborated in parallel to subsequent declarations in a future version of Lean.

  The effect of `variable`s on the theorem header as well as on other kinds of declarations is unchanged.

  Specifically, section variables are included if they
  * are directly referenced by the theorem header,
  * are included via the new `include` command in the current section and not subsequently mentioned in an `omit` statement,
  * are directly referenced by any variable included by these rules, OR
  * are instance-implicit variables that reference only variables included by these rules.

  For porting, a new option `deprecated.oldSectionVars` is included to locally switch back to the old behavior.

````
