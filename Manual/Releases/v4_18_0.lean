/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: investigate why this is needed in the new compiler
set_option maxRecDepth 9900

#doc (Manual) "Lean 4.18.0 (2025-04-02)" =>
%%%
tag := "release-v4.18.0"
file := "v4.18.0"
%%%

````markdown
For this release, 344 changes landed. In addition to the 166 feature additions and 38 fixes listed below there were 13 refactoring changes, 10 documentation improvements, 3 performance improvements, 4 improvements to the test suite and 109 other changes.

## Highlights

Lean v4.18 release brings a number of exciting new features:

* Inlay hints for auto implicits

  The Language Server now uses inlay hints to show which variables are brought into scope implicitly, and where. The hint
  reveals its type upon hover, and double-clicking the hint will insert the variable binding explicitly.

  See the description of [#6768](https://github.com/leanprover/lean4/pull/6768/files) for a screenshort.

  Note that this feature is only visible when `set_option autoImplicit true`, which is the default in plain Lean projects,
  but not in mathlib

* [#6935](https://github.com/leanprover/lean4/pull/6935) adds the tactic `expose_names`. It creates a new goal whose
  local context has been "exposed" so that every local declaration has a
  clear, accessible name. If no local declarations require renaming, the
  original goal is returned unchanged.

  ```lean
  /--
  info: α : Sort u_1
  a b : α
  h_1 : a = b
  h_2 : True
  h_3 : True ∨ False
  h : b = a
  ⊢ b = a
  -/
  #guard_msgs (info) in
  example (a b : α) (h : a = b) (_ : True) (_ : True ∨ False) (h : b = a) : b = a := by
    expose_names
    trace_state
    rw [h]
  ```

  This tactic intended for use in auto-generated tactic suggestions, and can also be useful
  during proof exploration. It is still best practice to name variables where they are
  brought into scope (`intro`, `case` etc.), and not use `expose_names` in a finished,
  polished proof.

* [#7069](https://github.com/leanprover/lean4/pull/7069) adds the `fun_induction` and `fun_cases` tactics, which add
  convenience around using functional induction and functional cases
  principles.

  ```lean
  fun_induction foo  x y z
  ```

  elaborates `foo x y z`, then looks up `foo.induct`, and then essentially does

  ```lean
  induction z using foo.induct y
  ```

  including and in particular figuring out which arguments are parameters,
  targets or dropped. This only works for non-mutual functions so far.

  Likewise there is the `fun_cases` tactic using `foo.fun_cases`.

* [#6744](https://github.com/leanprover/lean4/pull/6744) extend the preprocessing of well-founded recursive definitions
  to bring assumptions like `h✝ : x ∈ xs`, if a recursive call is in the
  argument of a higher-order function like `List.map`, into scope automatically.
  In many cases this removes the need to use functions like `List.attach`.

  This feature can be disabled with `set_option wf.preprocess false`.

* [#6634](https://github.com/leanprover/lean4/pull/6634) adds support for changing the binder annotations of existing
  variables to and from strict-implicit and instance-implicit using the
  `variable` command.

* [#7100](https://github.com/leanprover/lean4/pull/7100) modifies the `structure` syntax so that parents can be named,
  like in
  ```lean
  structure S extends toParent : P
  ```
  **Breaking change:** The syntax is also modified so that the resultant
  type comes *before* the `extends` clause, for example `structure S :
  Prop extends P`. This is necessary to prevent a parsing ambiguity, but
  also this is the natural place for the resultant type. Implements RFC
  [#7099](https://github.com/leanprover/lean4/issues/7099).

* [#7103](https://github.com/leanprover/lean4/pull/7103) gives the `induction` tactic the ability to name hypotheses to
  use when generalizing targets, just like in `cases`. For example,
  `induction h : xs.length` leads to goals with hypotheses `h : xs.length
  = 0` and `h : xs.length = n + 1`. Target handling is also slightly
  modified for multi-target induction principles: it used to be that if
  any target was not a free variable, all of the targets would be
  generalized (thus causing free variables to lose their connection to the
  local hypotheses they appear in); now only the non-free-variable targets
  are generalized.

* [#6869](https://github.com/leanprover/lean4/pull/6869) adds a `recommended_spelling` command, which can be used for
  recording the recommended spelling of a notation (for example, that the
  recommended spelling of `∧` in identifiers is `and`). This information
  is then appended to the relevant docstrings for easy lookup.

* [#6893](https://github.com/leanprover/lean4/pull/6893) adds support for plugins to the frontend and server.

* [#7061](https://github.com/leanprover/lean4/pull/7061) provides a basic API for a premise selection tool, which can be
  provided in downstream libraries. It does not implement premise
  selection itself!

And many more! Check out the *Language* section below.

Notably, a line of work has been carried out on the following
(see the corresponding subsections in the *Language* section for the details):
- the `try?` tactic, which has been re-implemented using `evalAndSuggest` tactic.
  `try?` now supports referencing inaccessible local names and can provide
  more complex suggestions, involving `exact?` and `fun_induction` tactics.
  New configuration options have been added: `-only`, `+missing`, and `max:=<num>`,
  as well as `merge`.
- `bv_decide` tactic. There are new features in preprocessing, added support
  for enum inductives, `IntX` and `ISize`, and improved performance in LRAT trimming.
- normalization for linear integer arithmetic expressions has been implemented
  and connected to `simp +arith`. [#7043](https://github.com/leanprover/lean4/pull/7043) deprecates the tactics `simp_arith`,
  `simp_arith!`, `simp_all_arith` and `simp_all_arith!` in favor of `simp +arith`.

Important Library updates include:

* [#6914](https://github.com/leanprover/lean4/pull/6914) introduces ordered map data structures, namely `DTreeMap`,
  `TreeMap`, `TreeSet` and their `.Raw` variants, into the standard
  library.  A collection of lemmas about the operations on these data structures has
  been added in the subsequent PRs.

* [#7255](https://github.com/leanprover/lean4/pull/7255) fixes the definition of `Min (Option α)`. This is a **breaking
  change**. This treats `none` as the least element,
  so `min none x = min x none = none` for all `x : Option α`. Prior to
  nightly-2025-02-27, we instead had `min none (some x) = min (some x)
  none = some x`. Also adds basic lemmas relating `min`, `max`, `≤` and
  `<` on `Option`.

Significant development has been made in the verification APIs of `BitVec`
and fixed-width integer types (`IntX`), along with ongoing work to align
`List/Array/Vector` APIs. Several lemmas about `Int.ediv/fdiv/tdiv` have
been strengthened.

[#6950](https://github.com/leanprover/lean4/pull/6950) adds [a style guide](https://github.com/leanprover/lean4/blob/master/doc/std/style.md) and [a naming convention](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md) for the standard library.

_This summary of highlights was contributed by Violetta Sim._

## Language

* [#6634](https://github.com/leanprover/lean4/pull/6634) adds support for changing the binder annotations of existing
  variables to and from strict-implicit and instance-implicit using the
  `variable` command.

* [#6744](https://github.com/leanprover/lean4/pull/6744) extends the preprocessing of well-founded recursive definitions,
  see the highlights section for details.

* [#6823](https://github.com/leanprover/lean4/pull/6823) adds a builtin tactic and a builtin attribute that are required
  for the tree map. The tactic, `as_aux_lemma`, can generally be used to
  wrap the proof term generated by a tactic sequence into a separate
  auxiliary lemma in order to keep the proof term small. This can, in rare
  cases, be necessary if the proof term will appear multiple times in the
  encompassing term. The new attribute, `Std.Internal.tree_tac`, is
  internal and should not be used outside of `Std`.

* [#6853](https://github.com/leanprover/lean4/pull/6853) adds support for anonymous equality proofs in `match`
  expressions of the form `match _ : e with ...`.

* [#6869](https://github.com/leanprover/lean4/pull/6869) adds a `recommended_spelling` command; see the highlights
  section for details.

* [#6891](https://github.com/leanprover/lean4/pull/6891) modifies `rewrite`/`rw` to abort rewriting if the elaborated
  lemma has any immediate elaboration errors (detected by presence of
  synthetic sorries). Rewriting still proceeds if there are elaboration
  issues arising from pending synthetic metavariables, like instance
  synthesis failures. The purpose of the change is to avoid obscure
  "tactic 'rewrite' failed, equality or iff proof expected ?m.5" errors
  when for example a lemma does not exist.

* [#6893](https://github.com/leanprover/lean4/pull/6893) adds support for plugins to the frontend and server.

* [#6935](https://github.com/leanprover/lean4/pull/6935) adds the tactic `expose_names`; see the highlights section
  for details.

* [#6936](https://github.com/leanprover/lean4/pull/6936) fixes the `#discr_tree_simp_key` command, because it displays
  the keys for just `lhs` in `lhs ≠ rhs`, but it should be `lhs = rhs`,
  since that is what simp indexes.

* [#6939](https://github.com/leanprover/lean4/pull/6939) adds error messages for `inductive` declarations with
  conflicting constructor names and `mutual` declarations with conflicting
  names.

* [#6947](https://github.com/leanprover/lean4/pull/6947) adds the `binderNameHint` gadget. It can be used in rewrite and
  simp rules to preserve a user-provided name where possible.

  The expression `binderNameHint v binder e` defined to be `e`.

  If it is used on the right-hand side of an equation that is applied by
  a tactic like `rw` or `simp`, and `v` is a local variable, and `binder`
  is an expression that (after beta-reduction) is a binder (so `fun w => …` or `∀ w, …`),
  then it will rename `v` to the name used in the binder, and remove the `binderNameHint`.

  A typical use of this gadget would be as follows; the gadget ensures
  that after rewriting, the local variable is still `name`, and not `x`:

  ```lean
  theorem all_eq_not_any_not (l : List α) (p : α → Bool) :
      l.all p = !l.any fun x => binderNameHint x p (!p x) := sorry

  example (names : List String) : names.all (fun name => "Waldo".isPrefixOf name) = true := by
    rw [all_eq_not_any_not]
    -- ⊢ (!names.any fun name => !"Waldo".isPrefixOf name) = true
  ```

  This gadget is supported by `simp`, `dsimp` and `rw` in the right-hand-side
  of an equation, but not in hypotheses or by other tactics.

* [#6951](https://github.com/leanprover/lean4/pull/6951) adds line breaks and indentations to simp's trace messages to
  make them easier to read (IMHO).

* [#6964](https://github.com/leanprover/lean4/pull/6964) adds a convenience command `#info_trees in`, which prints the
  info trees generated by the following command. It is useful for
  debugging or learning about `InfoTree`.

* [#7039](https://github.com/leanprover/lean4/pull/7039) improves the well-founded definition preprocessing to propagate
  `wfParam` through let expressions.

* [#7053](https://github.com/leanprover/lean4/pull/7053) makes `simp` heed the `binderNameHint` also in the assumptions
  of congruence rules. Fixes #7052.

* [#7055](https://github.com/leanprover/lean4/pull/7055) improves array and vector literal syntax by allowing trailing
  commas. For example, `#[1, 2, 3,]`.

* [#7061](https://github.com/leanprover/lean4/pull/7061) provides a basic API for a premise selection tool; see the
  highlights section for details.

* [#7078](https://github.com/leanprover/lean4/pull/7078) implements simprocs for `Int` and `Nat` divides predicates.

* [#7088](https://github.com/leanprover/lean4/pull/7088) fixes the behavior of the indexed-access notation `xs[i]` in
  cases where the proof of `i`'s validity is filled in during unification.

* [#7090](https://github.com/leanprover/lean4/pull/7090) strips `lib` prefixes and `_shared` suffixes from plugin names.
  It also moves most of the dynlib processing code to Lean to make such
  preprocessing more standard.

* [#7100](https://github.com/leanprover/lean4/pull/7100) modifies the `structure` syntax; see the highlights section for details.

* [#7103](https://github.com/leanprover/lean4/pull/7103) gives the `induction` tactic the ability to name hypotheses; see
  the highlights section for details.

* [#7119](https://github.com/leanprover/lean4/pull/7119) makes linter names clickable in the `trace.profiler` output.

* [#7191](https://github.com/leanprover/lean4/pull/7191) fixes the indentation of "Try this" suggestions in widget-less
  multiline messages, as they appear in `#guard_msgs` outputs.

* [#7192](https://github.com/leanprover/lean4/pull/7192) prevents `exact?` and `apply?` from suggesting tactics that
  correspond to correct proofs but do not elaborate, and it allows these
  tactics to suggest `expose_names` when needed.

* [#7200](https://github.com/leanprover/lean4/pull/7200) allows the debug form of DiscrTree.Key to line-wrap.

* [#7213](https://github.com/leanprover/lean4/pull/7213) adds `SetConsoleOutputCP(CP_UTF8)` during runtime initialization
  to properly display Unicode on the Windows console. This effects both
  the Lean executable itself and user executables (including Lake).

* [#7224](https://github.com/leanprover/lean4/pull/7224) make `induction … using` and `cases … using` complain if more
  targets were given than expected by that eliminator.

* [#7294](https://github.com/leanprover/lean4/pull/7294) fixes bugs in `Std.Internal.Rat.floor` and
  `Std.Internal.Rat.ceil`.

### Updates to the `try?` Tactic

* [#6961](https://github.com/leanprover/lean4/pull/6961) adds the auxiliary tactic `evalAndSuggest`. It will be used to
  refactor `try?`.

* [#6965](https://github.com/leanprover/lean4/pull/6965) re-implements the `try?` tactic using the new `evalAndSuggest`
  infrastructure.

* [#6967](https://github.com/leanprover/lean4/pull/6967) ensures `try?` can suggest tactics that need to reference
  inaccessible local names.
  Example:
    ```lean
    /--
    info: Try these:
    • · expose_names; induction as, bs_1 using app.induct <;> grind [= app]
    • · expose_names; induction as, bs_1 using app.induct <;> grind only [app]
    -/
    #guard_msgs (info) in
    example : app (app as bs) cs = app as (app bs cs) := by
      have bs := 20 -- shadows `bs` in the target
      try?
    ```

* [#6979](https://github.com/leanprover/lean4/pull/6979) adds support for more complex suggestions in `try?`.
  Example:
    ```lean
    example (as : List α) (a : α) : concat as a = as ++ [a] := by
      try?
    ```
    suggestion
    ```
    Try this: · induction as, a using concat.induct
      · rfl
      · simp_all
    ```

* [#6980](https://github.com/leanprover/lean4/pull/6980) improves the `try?` tactic runtime validation and error
  messages. It also simplifies the implementation, and removes unnecessary
  code.

* [#6981](https://github.com/leanprover/lean4/pull/6981) adds new configuration options to `try?`.
  - `try? -only` omits `simp only` and `grind only` suggestions
  - `try? +missing` enables partial solutions where some subgoals are
  "solved" using `sorry`, and must be manually proved by the user.
  - `try? (max:=<num>)` sets the maximum number of suggestions produced
  (default is 8).

* [#6991](https://github.com/leanprover/lean4/pull/6991) improves how suggestions for the `<;>` combinator are generated.

* [#6994](https://github.com/leanprover/lean4/pull/6994) adds the `Try.Config.merge` flag (`true` by default) to the
  `try?` tactic. When set to `true`, `try?` compresses suggestions such
  as:
  ```lean
  · induction xs, ys using bla.induct
      · grind only [List.length_reverse]
      · grind only [bla]
  ```
  into:
  ```lean
  induction xs, ys using bla.induct <;> grind only [List.length_reverse, bla]
  ```

* [#6995](https://github.com/leanprover/lean4/pull/6995) implements support for `exact?` in the `try?` tactic.

* [#7082](https://github.com/leanprover/lean4/pull/7082) makes `try?` use `fun_induction` instead of `induction … using
  foo.induct`. It uses the argument-free short-hand `fun_induction foo` if
  that is unambiguous. Avoids `expose_names` if not necessary by simply
  trying without first.

### Functional Induction Tactic

* [#7069](https://github.com/leanprover/lean4/pull/7069) adds the `fun_induction` and `fun_cases` tactics, which add
  convenience around using functional induction and functional cases
  principles.

* [#7101](https://github.com/leanprover/lean4/pull/7101) implements `fun_induction foo`, which is like `fun_induction foo
  x y z`, only that it picks the arguments to use from a unique suitable
  call to `foo` in the goal.

* [#7127](https://github.com/leanprover/lean4/pull/7127) follows up on #7103 which changes the generaliziation behavior
  of `induction`, to keep `fun_induction` in sync. Also fixes a `Syntax`
  indexing off-by-one error.

### `bv_decide` Tactic

* [#6741](https://github.com/leanprover/lean4/pull/6741) implements two rules for bv_decide's preprocessor, lowering
  `|||` to `&&&` in order to enable more term sharing + application of
  rules about `&&&` as well as rewrites of the form `(a &&& b == -1#w) =
  (a == -1#w && b == -1#w)` in order to preserve rewriting behavior that
  already existed before this lowering.

* [#6924](https://github.com/leanprover/lean4/pull/6924) adds the EQUAL_ITE rules from Bitwuzla to the preprocessor of
  bv_decide.

* [#6926](https://github.com/leanprover/lean4/pull/6926) adds the BV_EQUAL_CONST_NOT rules from Bitwuzla to the
  preprocessor of bv_decide.

* [#6946](https://github.com/leanprover/lean4/pull/6946) implements basic support for handling of enum inductives in
  `bv_decide`. It now supports equality on enum inductive variables (or
  other uninterpreted atoms) and constants.

* [#7009](https://github.com/leanprover/lean4/pull/7009) ensures users get an error message saying which module to import
  when they try to use `bv_decide`.

* [#7019](https://github.com/leanprover/lean4/pull/7019) properly spells out the trace nodes in bv_decide so they are
  visible with just `trace.Meta.Tactic.bv` and `trace.Meta.Tactic.sat`
  instead of always having to enable the profiler.

* [#7021](https://github.com/leanprover/lean4/pull/7021) adds theorems for interactions of extractLsb with `&&&`, `^^^`,
  `~~~` and `bif` to bv_decide's preprocessor.

* [#7029](https://github.com/leanprover/lean4/pull/7029) adds simprocs to bv_decide's preprocessor that rewrite
  multiplication with powers of two to constant shifts.

* [#7033](https://github.com/leanprover/lean4/pull/7033) improves presentation of counter examples for UIntX and enum
  inductives in bv_decide.

* [#7242](https://github.com/leanprover/lean4/pull/7242) makes sure bv_decide can work with projections applied to `ite`
  and `cond` in its structures pass.

* [#7257](https://github.com/leanprover/lean4/pull/7257) improves performance of LRAT trimming in bv_decide.

* [#7269](https://github.com/leanprover/lean4/pull/7269) implements support for `IntX` and `ISize` in `bv_decide`.

* [#7275](https://github.com/leanprover/lean4/pull/7275) adds all level 1 rewrites from Bitwuzla to the preprocessor of
  bv_decide.

### Parallelizing Elaboration

* [#6770](https://github.com/leanprover/lean4/pull/6770) enables code generation to proceed in parallel to further
  elaboration.

* [#6988](https://github.com/leanprover/lean4/pull/6988) ensures interrupting the kernel does not lead to wrong, sticky
  error messages in the editor

* [#7047](https://github.com/leanprover/lean4/pull/7047) removes the `save` and `checkpoint` tactics that have been
  superseded by incremental elaboration

* [#7076](https://github.com/leanprover/lean4/pull/7076) introduces the central parallelism API for ensuring that helper
  declarations can be generated lazily without duplicating work or
  creating conflicts across threads.

### Linear Integer Normalization in `simp +arith`

* [#7000](https://github.com/leanprover/lean4/pull/7000) adds helper theorems for justifying the linear integer
  normalizer.

* [#7002](https://github.com/leanprover/lean4/pull/7002) implements the normalizer for linear integer arithmetic
  expressions. It is not connect to `simp +arith` yet because of some
  spurious `[simp]` attributes.

* [#7011](https://github.com/leanprover/lean4/pull/7011) adds `simp +arith` for integers. It uses the new `grind`
  normalizer for linear integer arithmetic. We still need to implement
  support for dividing the coefficients by their GCD. It also fixes
  several bugs in the normalizer.

* [#7015](https://github.com/leanprover/lean4/pull/7015) makes sure `simp +arith` normalizes coefficients in linear
  integer polynomials. There is still one todo: tightening the bound of
  inequalities.

* [#7030](https://github.com/leanprover/lean4/pull/7030) adds completes the linear integer inequality normalizer for
  `grind`. The missing normalization step replaces a linear inequality of
  the form `a_1*x_1 + ... + a_n*x_n + b <= 0` with `a_1/k * x_1 + ... +
  a_n/k * x_n + ceil(b/k) <= 0` where `k = gcd(a_1, ..., a_n)`.
  `ceil(b/k)` is implemented using the helper `cdiv b k`.

* [#7040](https://github.com/leanprover/lean4/pull/7040) ensures that terms such as `f (2*x + y)` and `f (y + x + x)`
  have the same normal form when using `simp +arith`

* [#7043](https://github.com/leanprover/lean4/pull/7043) deprecates the tactics `simp_arith`, `simp_arith!`,
  `simp_all_arith` and `simp_all_arith!`. Users can just use the `+arith`
  option.

### `grind` Tactic

The `grind` tactic is still is experimental and still under development. Avoid using it in production projects

* [#6902](https://github.com/leanprover/lean4/pull/6902) ensures `simp` diagnostic information in included in the `grind`
  diagnostic message.

* [#6937](https://github.com/leanprover/lean4/pull/6937) improves `grind` error and trace messages by cleaning up local
  declaration names.

* [#6940](https://github.com/leanprover/lean4/pull/6940) improves how the `grind` tactic performs case splits on `p <->
  q`.

* [#7102](https://github.com/leanprover/lean4/pull/7102) modifies `grind` to run with the `reducible` transparency
  setting. We do not want `grind` to unfold arbitrary terms during
  definitional equality tests. also fixes several issues
  introduced by this change. The most common problem was the lack of a
  hint in proofs, particularly in those constructed using proof by
  reflection. also introduces new sanity checks when `set_option
  grind.debug true` is used.

* [#7231](https://github.com/leanprover/lean4/pull/7231) implements functions for constructing disequality proofs in
  `grind`.

#### Cutsat Procedure (Solver for Linear Integer Arithmetic Problems)

* [#7077](https://github.com/leanprover/lean4/pull/7077) proves the helper theorems for justifying the "Div-Solve" rule
  in the cutsat procedure.

* [#7091](https://github.com/leanprover/lean4/pull/7091) adds helper theorems for normalizing divisibility constraints.
  They are going to be used to implement the cutsat procedure in the
  `grind` tactic.

* [#7092](https://github.com/leanprover/lean4/pull/7092) implements divisibility constraint normalization in `simp
  +arith`.

* [#7097](https://github.com/leanprover/lean4/pull/7097) implements several modifications for the cutsat procedure in
  `grind`.
  - The maximal variable is now at the beginning of linear polynomials.
  - The old `LinearArith.Solver` was deleted, and the normalizer was moved
  to `Simp`.
  - cutsat first files were created, and basic infrastructure for
  representing divisibility constraints was added.

* [#7122](https://github.com/leanprover/lean4/pull/7122) implements the divisibility constraint solver for the cutsat
  procedure in the `grind` tactic.

* [#7124](https://github.com/leanprover/lean4/pull/7124) adds the helper theorems for justifying the divisibility
  constraint solver in the cutsat procedure used by the `grind` tactic.

* [#7138](https://github.com/leanprover/lean4/pull/7138) implements proof generation for the divisibility constraint
  solver in `grind`.

* [#7139](https://github.com/leanprover/lean4/pull/7139) uses a `let`-expression for storing the (shared) context in
  proofs produced by the cutsat procedure in `grind`.

* [#7152](https://github.com/leanprover/lean4/pull/7152) implements the infrastructure for supporting integer inequality
  constraints in the cutsat procedure.

* [#7155](https://github.com/leanprover/lean4/pull/7155) implements some infrastructure for the model search procedure in
  cutsat.

* [#7156](https://github.com/leanprover/lean4/pull/7156) adds a helper theorem that will be used in divisibility
  constraint conflict resolution during model construction.

* [#7176](https://github.com/leanprover/lean4/pull/7176) implements model construction for divisibility constraints in
  the cutsat procedure.

* [#7183](https://github.com/leanprover/lean4/pull/7183) improves the cutsat model search procedure.

* [#7186](https://github.com/leanprover/lean4/pull/7186) simplifies the proofs and data structures used by cutsat.

* [#7193](https://github.com/leanprover/lean4/pull/7193) adds basic infrastructure for adding support for equalities in
  cutsat.

* [#7194](https://github.com/leanprover/lean4/pull/7194) adds support theorems for solving equality in cutsat.

* [#7202](https://github.com/leanprover/lean4/pull/7202) adds support for internalizing terms relevant to the cutsat
  module. This is required to implement equality propagation.

* [#7203](https://github.com/leanprover/lean4/pull/7203) improves the support for equalities in cutsat. It also
  simplifies a few support theorems used to justify cutsat rules.

* [#7217](https://github.com/leanprover/lean4/pull/7217) improves the support for equalities in cutsat.

* [#7220](https://github.com/leanprover/lean4/pull/7220) implements the missing cases for equality propagation from the
  `grind` core to the cutsat module.

* [#7234](https://github.com/leanprover/lean4/pull/7234) implements dIsequality propagation from `grind` core module to
  cutsat.

* [#7244](https://github.com/leanprover/lean4/pull/7244) adds support for disequalities in the cutsat procedure used in
  `grind`.

* [#7248](https://github.com/leanprover/lean4/pull/7248) implements simple equality propagation in cutsat `p <= 0 -> -p <= 0 -> p = 0`

* [#7252](https://github.com/leanprover/lean4/pull/7252) implements inequality refinement using disequalities. It
  minimizes the number of case splits cutsat will have to perform.

* [#7267](https://github.com/leanprover/lean4/pull/7267) improves the cutsat search procedure. It adds support for find
  an approximate rational solution, checks disequalities, and adds stubs
  for all missing cases.

* [#7278](https://github.com/leanprover/lean4/pull/7278) adds counterexamples for linear integer constraints in the
  `grind` tactic. This feature is implemented in the cutsat procedure.

* [#7279](https://github.com/leanprover/lean4/pull/7279) adds support theorems for the **Cooper-Dvd-Left** conflict
  resolution rule used in the cutsat procedure. During model construction,
  when attempting to extend the model to a variable `x`, cutsat may find a
  conflict that involves two inequalities (the lower and upper bounds for
  `x`) and a divisibility constraint:

  ```lean
  a * x + p ≤ 0
  b * x + q ≤ 0
  d ∣ c * x + s
  ```

* [#7284](https://github.com/leanprover/lean4/pull/7284) implements non-choronological backtracking for the cutsat
  procedure. The procedure has two main kinds of case-splits:
  disequalities and Cooper resolvents. focus on the first kind.

* [#7290](https://github.com/leanprover/lean4/pull/7290) adds support theorems for the **Cooper-Left** conflict
  resolution rule used in the cutsat procedure. During model
  construction,when attempting to extend the model to a variable `x`,
  cutsat may find a conflict that involves two inequalities (the lower and
  upper bounds for `x`). This is a special case of Cooper-Dvd-Left when
  there is no divisibility constraint.

* [#7292](https://github.com/leanprover/lean4/pull/7292) adds support theorems for the **Cooper-Dvd-Right** conflict
  resolution rule used in the cutsat procedure. During model construction,
  when attempting to extend the model to a variable `x`, cutsat may find a
  conflict that involves two inequalities (the lower and upper bounds for
  `x`) and a divisibility constraint.

* [#7293](https://github.com/leanprover/lean4/pull/7293) adds support theorems for the Cooper-Right conflict resolution
  rule used in the cutsat procedure. During model construction, when
  attempting to extend the model to a variable x, cutsat may find a
  conflict that involves two inequalities (the lower and upper bounds for
  x). This is a special case of Cooper-Dvd-Right when there is no
  divisibility constraint.


* [#7409](https://github.com/leanprover/lean4/pull/7409) allows the use of `dsimp` during preprocessing of well-founded
  definitions. This fixes regressions when using `if-then-else` without
  giving a name to the condition, but where the condition is needed for
  the termination proof, in cases where that subexpression is reachable
  only by dsimp, but not by simp (e.g. inside a dependent let)

## Library

* [#5498](https://github.com/leanprover/lean4/pull/5498) makes `BitVec.getElem` the simp normal form in case a proof is
  available and changes `ext` to return `x[i]` + a hypothesis that proves
  that we are in-bounds. This aligns `BitVec` further with the API
  conventions of the Lean standard datatypes.

* [#6326](https://github.com/leanprover/lean4/pull/6326) adds `BitVec.(getMsbD, msb)_replicate, replicate_one` theorems,
  corrects a non-terminal `simp` in `BitVec.getLsbD_replicate` and
  simplifies the proof of `BitVec.getElem_replicate` using the `cases`
  tactic.

* [#6628](https://github.com/leanprover/lean4/pull/6628) adds SMT-LIB operators to detect overflow
  `BitVec.(uadd_overflow, sadd_overflow)`, according to the definitions
  [here](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2),
  and the theorems proving equivalence of such definitions with the
  `BitVec` library functions (`uaddOverflow_eq`, `saddOverflow_eq`).
  Support theorems for these proofs are `BitVec.toNat_mod_cancel_of_lt,
  BitVec.toInt_lt, BitVec.le_toInt, Int.bmod_neg_iff`. The PR also
  includes a set of tests.

* [#6792](https://github.com/leanprover/lean4/pull/6792) adds theorems `BitVec.(getMsbD, msb)_(extractLsb', extractLsb),
  getMsbD_extractLsb'_eq_getLsbD`.

* [#6795](https://github.com/leanprover/lean4/pull/6795) adds theorems `BitVec.(getElem_umod_of_lt, getElem_umod,
  getLsbD_umod, getMsbD_umod)`. For the defiition of these theorems we
  rely on `divRec`, excluding the case where `d=0#w`, which is treated
  separately because there is no infrastructure to reason about this case
  within `divRec`. In particular, our implementation follows the mathlib
  standard [where division by 0 yields
  0](https://github.com/leanprover/lean4/blob/c7c1e091c9f07ae6f8e8ff7246eb7650e2740dcb/src/Init/Data/BitVec/Basic.lean#L217),
  while in [SMTLIB this yields
  `allOnes`](https://github.com/leanprover/lean4/blob/c7c1e091c9f07ae6f8e8ff7246eb7650e2740dcb/src/Init/Data/BitVec/Basic.lean#L237).

* [#6830](https://github.com/leanprover/lean4/pull/6830) improves some files separation and standardize error messages in
  UV modules

* [#6850](https://github.com/leanprover/lean4/pull/6850) adds some lemmas about the new tree map. These lemmas are about
  the interactions of `empty`, `isEmpty`, `insert`, `contains`. Some
  lemmas about the interaction of `contains` with the others will follow
  in a later PR.

* [#6866](https://github.com/leanprover/lean4/pull/6866) adds missing `Hashable` instances for `PUnit` and `PEmpty`.

* [#6914](https://github.com/leanprover/lean4/pull/6914) introduces ordered map data structures, namely `DTreeMap`,
  `TreeMap`, `TreeSet` and their `.Raw` variants, into the standard
  library. There are still some operations missing that the hash map has.
  As of now, the operations are unverified, but the corresponding lemmas
  will follow in subsequent PRs. While the tree map has already been
  optimized, more micro-optimization will follow as soon as the new code
  generator is ready.

* [#6922](https://github.com/leanprover/lean4/pull/6922) adds `LawfulBEq` instances for `Array` and `Vector`.

* [#6948](https://github.com/leanprover/lean4/pull/6948) completes the alignment of `List/Array/Vectors` lemmas for
  `insertIdx`.

* [#6954](https://github.com/leanprover/lean4/pull/6954) verifies the `toList`function for hash maps and dependent hash
  maps.

* [#6958](https://github.com/leanprover/lean4/pull/6958) improves the `Promise` API by considering how dropped promises
  can lead to never-finished tasks.

* [#6966](https://github.com/leanprover/lean4/pull/6966) adds an internal-use-only strict linter for the variable names
  of `List`/`Array`/`Vector` variables, and begins cleaning up.

* [#6982](https://github.com/leanprover/lean4/pull/6982) improves some lemmas about monads and monadic operations on
  Array/Vector, using @Rob23oa's work in
  https://github.com/leanprover-community/batteries/pull/1109, and
  adding/generalizing some additional lemmas.

* [#7013](https://github.com/leanprover/lean4/pull/7013) makes improvements to the simp set for List/Array/Vector/Option
  to improve confluence, in preparation for `simp_lc`.

* [#7017](https://github.com/leanprover/lean4/pull/7017) renames the simp set `boolToPropSimps` to `bool_to_prop` and
  `bv_toNat` to `bitvec_to_nat`. I'll be adding more similarly named simp
  sets.

* [#7034](https://github.com/leanprover/lean4/pull/7034) adds `wf_preprocess` theorems for
  `{List,Array}.{foldlM,foldrM,mapM,filterMapM,flatMapM}`

* [#7036](https://github.com/leanprover/lean4/pull/7036) adds some deprecated function aliases to the tree map in order
  to ease the transition from the `RBMap` to the tree map.

* [#7046](https://github.com/leanprover/lean4/pull/7046) renames `UIntX.mk` to `UIntX.ofBitVec` and adds deprecations.

* [#7048](https://github.com/leanprover/lean4/pull/7048) adds the functions `IntX.ofBitVec`.

* [#7050](https://github.com/leanprover/lean4/pull/7050) renames the functions `UIntX.val` to `UIntX.toFin`.

* [#7051](https://github.com/leanprover/lean4/pull/7051) implements the methods `insertMany`, `ofList`, `ofArray`,
  `foldr` and `foldrM` on the tree map.

* [#7056](https://github.com/leanprover/lean4/pull/7056) adds the `UIntX.ofFin` conversion functions.

* [#7057](https://github.com/leanprover/lean4/pull/7057) adds the function `UIntX.ofNatLT`. This is supposed to be a
  replacement for `UIntX.ofNatCore` and `UIntX.ofNat'`, but for
  bootstrapping reasons we need this function to exist in stage0 before we
  can proceed with the renaming and deprecations, so this PR just adds the
  function.

* [#7059](https://github.com/leanprover/lean4/pull/7059) moves away from using `List.get` / `List.get?` / `List.get!` and
  `Array.get!`, in favour of using the `GetElem` mediated getters. In
  particular it deprecates `List.get?`, `List.get!` and `Array.get?`. Also
  adds `Array.back`, taking a proof, matching `List.getLast`.

* [#7062](https://github.com/leanprover/lean4/pull/7062) introduces the functions `UIntX.toIntX` as the public API to
  obtain the `IntX` that is 2's complement equivalent to a given `UIntX`.

* [#7063](https://github.com/leanprover/lean4/pull/7063) adds `ISize.toInt8`, `ISize.toInt16`, `Int8.toISize`,
  `Int16.toISize`.

* [#7064](https://github.com/leanprover/lean4/pull/7064) renames `BitVec.ofNatLt` to `BitVec.ofNatLT` and sets up
  deprecations for the old name.

* [#7066](https://github.com/leanprover/lean4/pull/7066) renames `IntX.toNat` to `IntX.toNatClampNeg` (to reduce
  surprises) and sets up a deprecation.

* [#7068](https://github.com/leanprover/lean4/pull/7068) is a follow-up to #7057 and adds a builtin dsimproc for
  `UIntX.ofNatLT` which it turns out we need in stage0 before we can get
  the deprecation of `UIntX.ofNatCore` in favor of `UIntX.ofNatLT` off the
  ground.

* [#7070](https://github.com/leanprover/lean4/pull/7070) implements the methods `min`, `max`, `minKey`, `maxKey`,
  `atIndex`, `getEntryLE`, `getKeyLE` and consorts on the tree map.

* [#7071](https://github.com/leanprover/lean4/pull/7071) unifies the existing functions `UIntX.ofNatCore` and
  `UIntX.ofNat'` under a new name, `UIntX.ofNatLT`.

* [#7079](https://github.com/leanprover/lean4/pull/7079) introduces `Fin.toNat` as an alias for `Fin.val`. We add this
  function for discoverability and consistency reasons. The normal form
  for proofs remains `Fin.val`, and there is a `simp` lemma rewriting
  `Fin.toNat` to `Fin.val`.

* [#7080](https://github.com/leanprover/lean4/pull/7080) adds the functions `UIntX.ofNatTruncate` (the version for
  `UInt32` already exists).

* [#7081](https://github.com/leanprover/lean4/pull/7081) adds functions `IntX.ofIntLE`, `IntX.ofIntTruncate`, which are
  analogous to the unsigned counterparts `UIntX.ofNatLT` and
  `UInt.ofNatTruncate`.

* [#7083](https://github.com/leanprover/lean4/pull/7083) adds (value-based, not bitfield-based) conversion functions
  between `Float`/`Float32` and `IntX`/`UIntX`.

* [#7105](https://github.com/leanprover/lean4/pull/7105) completes aligning `Array/Vector.extract` lemmas with the lemmas
  for `List.take` and `List.drop`.

* [#7106](https://github.com/leanprover/lean4/pull/7106) completes the alignment of `List/Array/Vector.finRange` lemmas.

* [#7109](https://github.com/leanprover/lean4/pull/7109) implements the `getThenInsertIfNew?` and `partition` functions
  on the tree map.

* [#7114](https://github.com/leanprover/lean4/pull/7114) implements the methods `values` and `valuesArray` on the tree
  map.

* [#7116](https://github.com/leanprover/lean4/pull/7116) implements the `getKey` functions on the tree map. It also fixes
  the naming of the `entryAtIdx` function on the tree set, which should
  have been called `atIdx`.

* [#7118](https://github.com/leanprover/lean4/pull/7118) implements the functions `modify` and `alter` on the tree map.

* [#7128](https://github.com/leanprover/lean4/pull/7128) adds `Repr` and `Hashable` instances for `IntX`.

* [#7131](https://github.com/leanprover/lean4/pull/7131) adds `IntX.abs` functions. These are specified by `BitVec.abs`,
  so they map `IntX.minValue` to `IntX.minValue`, similar to Rust's
  `i8::abs`. In the future we might also have versions which take values
  in `UIntX` and/or `Nat`.

* [#7137](https://github.com/leanprover/lean4/pull/7137) verifies the various fold and for variants for hashmaps.

* [#7151](https://github.com/leanprover/lean4/pull/7151) fixes a memory leak in `IO.FS.createTempFile`

* [#7158](https://github.com/leanprover/lean4/pull/7158) strengthens `Int.tdiv_eq_ediv`, by dropping an unnecessary
  hypothesis, in preparation for further work on `ediv`/`tdiv`/`fdiv`
  lemmas.

* [#7161](https://github.com/leanprover/lean4/pull/7161) adds all missing tree map lemmas about the interactions of the
  functions `empty`, `isEmpty`, `contains`, `size`, `insert(IfNew)` and
  `erase`.

* [#7162](https://github.com/leanprover/lean4/pull/7162) splits `Int.DivModLemmas` into a `Bootstrap` and `Lemmas` file,
  where it is possible to use `omega` in `Lemmas`.

* [#7163](https://github.com/leanprover/lean4/pull/7163) gives an unconditional theorem expressing `Int.tdiv` in terms of
  `Int.ediv`, not just for non-negative arguments.

* [#7165](https://github.com/leanprover/lean4/pull/7165) provides tree map lemmas about the interaction of
  `containsThenInsert(IfNew)` with `contains` and `insert(IfNew)`.

* [#7167](https://github.com/leanprover/lean4/pull/7167) provides tree map lemmas for the interaction of `get?` with the
  other operations for which lemmas already exist.

* [#7174](https://github.com/leanprover/lean4/pull/7174) adds the first batch of lemmas about iterated conversions
  between finite types starting with something of type `UIntX`.

* [#7199](https://github.com/leanprover/lean4/pull/7199) adds theorems comparing `Int.ediv` with `tdiv` and `fdiv`, for
  all signs of arguments. (Previously we just had the statements about the
  cases in which they agree.)

* [#7201](https://github.com/leanprover/lean4/pull/7201) adds `Array/Vector.left/rightpad`. These will not receive any
  verification theorems; simp just unfolds them to an `++` operation.

* [#7205](https://github.com/leanprover/lean4/pull/7205) completes alignment of
  `List.getLast`/`List.getLast!`/`List.getLast?` lemmas with the
  corresponding lemmas for Array and Vector.

* [#7206](https://github.com/leanprover/lean4/pull/7206) adds theorem `BitVec.toFin_abs`, completing the API for
  `BitVec.*_abs`.

* [#7207](https://github.com/leanprover/lean4/pull/7207) provides lemmas for the tree map functions `get`, `get!` and
  `getD` in relation to the other operations for which lemmas already
  exist.

* [#7208](https://github.com/leanprover/lean4/pull/7208) aligns lemmas for `List.dropLast` / `Array.pop` / `Vector.pop`.

* [#7210](https://github.com/leanprover/lean4/pull/7210) adds the remaining lemmas about iterated conversions between
  finite types starting with something of type `UIntX`.

* [#7214](https://github.com/leanprover/lean4/pull/7214) adds a `ForIn` instance for the `PersistentHashSet` type.

* [#7221](https://github.com/leanprover/lean4/pull/7221) provides lemmas about the tree map functions `getKey?`,
  `getKey`, `getKey!`, `getKeyD` and `insertIfNew` and their interaction
  with other functions for which lemmas already exist.

* [#7222](https://github.com/leanprover/lean4/pull/7222) removes the `simp` attribute from `ReflCmp.compare_self` because
  it matches arbitrary function applications. Instead, a new `simp` lemma
  `ReflOrd.compare_self` is introduced, which only matches applications of
  `compare`.

* [#7229](https://github.com/leanprover/lean4/pull/7229) provides lemmas for the tree map function `getThenInsertIfNew?`.

* [#7235](https://github.com/leanprover/lean4/pull/7235) adds `Array.replace` and `Vector.replace`, proves the
  correspondences with `List.replace`, and reproduces the basic API. In
  order to do so, it fills in some gaps in the `List.findX` APIs.

* [#7237](https://github.com/leanprover/lean4/pull/7237) provides proofs that the raw tree map operations are well-formed
  and refactors the file structure of the tree map, introducing new
  modules `Std.{DTreeMap,TreeMap,TreeSet}.Raw` and splittting
  `AdditionalOperations` into separate files for bundled and raw types.

* [#7245](https://github.com/leanprover/lean4/pull/7245) adds missing `@[specialize]` annotations to the `alter` and
  `modify` functions in `Std.Data.DHashMap.Internal.AssocList`, which are
  used by the corresponding hash map functions.

* [#7249](https://github.com/leanprover/lean4/pull/7249) completes alignment of theorems about
  `List/Array/Vector.any/all`.

* [#7255](https://github.com/leanprover/lean4/pull/7255) fixes the definition of `Min (Option α)`. This is a breaking
  change. This treats `none` as the least element,
  so `min none x = min x none = none` for all `x : Option α`. Prior to
  nightly-2025-02-27, we instead had `min none (some x) = min (some x)
  none = some x`. Also adds basic lemmas relating `min`, `max`, `≤` and
  `<` on `Option`.

* [#7259](https://github.com/leanprover/lean4/pull/7259) contains theorems about `IntX` that are required for `bv_decide`
  and the `IntX` simprocs.

* [#7260](https://github.com/leanprover/lean4/pull/7260) provides lemmas about the tree map functions `keys` and `toList`
  and their interactions with other functions for which lemmas already
  exist. Moreover, a bug in `foldr` (calling `foldlM` instead of `foldrM`)
  is fixed.

* [#7266](https://github.com/leanprover/lean4/pull/7266) begins the alignment of `Int.ediv/fdiv/tdiv` theorems.

* [#7268](https://github.com/leanprover/lean4/pull/7268) implements `Lean.ToExpr` for finite signed integers.

* [#7271](https://github.com/leanprover/lean4/pull/7271) changes the order of arguments of the folding function expected
  by the tree map's `foldr` and `foldrM` functions so that they are
  consistent with the API of `List`.

* [#7273](https://github.com/leanprover/lean4/pull/7273) fixes the statement of a `UIntX` conversion lemma.

* [#7277](https://github.com/leanprover/lean4/pull/7277) fixes a bug in Float32.ofInt, which previously returned a
  Float(64).

## Compiler

* [#6928](https://github.com/leanprover/lean4/pull/6928) makes extern decls evaluate as ⊤ rather than the default value
  of ⊥ in the LCNF elimDeadBranches analysis.

* [#6930](https://github.com/leanprover/lean4/pull/6930) changes the name generation of specialized LCNF decls so they
  don't strip macro scopes. This avoids name collisions for
  specializations created in distinct macro scopes. Since the normal
  Name.append function checks for the presence of macro scopes, we need to
  use appendCore.

* [#6976](https://github.com/leanprover/lean4/pull/6976) extends the behavior of the `sync` flag for `Task.map/bind` etc.
  to encompass synchronous execution even when they first have to wait on
  completion of the first task, drastically lowering the overhead of such
  tasks. Thus the flag is now equivalent to e.g. .NET's
  `TaskContinuationOptions.ExecuteSynchronously`.

* [#7037](https://github.com/leanprover/lean4/pull/7037) relaxes the minimum required glibc version for Lean and Lean
  executables to 2.26 on x86-64 Linux

* [#7041](https://github.com/leanprover/lean4/pull/7041) marks several LCNF-specific environment extensions as having an
  asyncMode of .sync rather than the default of .mainOnly, so they work
  correctly even in async contexts.

* [#7086](https://github.com/leanprover/lean4/pull/7086) makes the arity reduction pass in the new code generator match
  the old one when it comes to the behavior of decls with no used
  parameters. This is important, because otherwise we might create a
  top-level decl with no params that contains unreachable code, which
  would get evaluated unconditionally during initialization. This actually
  happens when initializing Init.Core built with the new code generator.

## Pretty Printing

* [#7074](https://github.com/leanprover/lean4/pull/7074) modifies the signature pretty printer to add hover information
  for parameters in binders. This makes the binders be consistent with the
  hovers in pi types.

## Documentation

* [#6886](https://github.com/leanprover/lean4/pull/6886) adds recommended spellings for many notations defined in Lean
  core, using the `recommended_spelling` command from #6869.

* [#6950](https://github.com/leanprover/lean4/pull/6950) adds a style guide and a naming convention for the standard
  library.

* [#6962](https://github.com/leanprover/lean4/pull/6962) improves the doc-string for `List.toArray`.

* [#6998](https://github.com/leanprover/lean4/pull/6998) modifies the `Prop` docstring to point out that every
  proposition is propositionally equal to either `True` or `False`. This
  will help point users toward seeing that `Prop` is like `Bool`.

* [#7026](https://github.com/leanprover/lean4/pull/7026) clarifies the styling of `do` blocks, and enhanes the naming
  conventions with information about the `ext` and `mono` name components
  as well as advice about primed names and naming of simp sets.

* [#7111](https://github.com/leanprover/lean4/pull/7111) extends the standard library style guide with guidance on
  universe variables, notations and Unicode usage, and structure
  definitions.

## Server

* [#6329](https://github.com/leanprover/lean4/pull/6329) enables the language server to present multiple disjoint line
  ranges as being worked on. Even before parallelism lands, we make use of
  this feature to show post-elaboration tasks such as kernel checking on
  the first line of a declaration to distinguish them from the final
  tactic step.

* [#6768](https://github.com/leanprover/lean4/pull/6768) adds preliminary support for inlay hints, as well as support for
  inlay hints that denote the auto-implicits of a function. Hovering over
  an auto-implicit displays its type and double-clicking the auto-implicit
  inserts it into the text document.

  **Breaking Change**: The semantic highlighting request handler is not a pure
  request handler anymore, but a stateful one. Notably, this means that clients
  that extend the semantic highlighting of the Lean language server with the
  `chainLspRequestHandler` function must now use the `chainStatefulLspRequestHandler`
  function instead.

* [#6887](https://github.com/leanprover/lean4/pull/6887) fixes a bug where the goal state selection would sometimes
  select incomplete incremental snapshots on whitespace, leading to an
  incorrect "no goals" response. Fixes #6594, a regression that was
  originally introduced in 4.11.0 by #4727.

* [#6959](https://github.com/leanprover/lean4/pull/6959) implements a number of refinements for the auto-implicit inlay
  hints implemented in #6768.
  Specifically:
  - In #6768, there was a bug where the inlay hint edit delay could
  accumulate on successive edits, which meant that it could sometimes take
  much longer for inlay hints to show up. implements the basic
  infrastructure for request cancellation and implements request
  cancellation for semantic tokens and inlay hints to resolve the issue.
  With this edit delay bug fixed, it made more sense to increase the edit
  delay slightly from 2000ms to 3000ms.
  - In #6768, we applied the edit delay to every single inlay hint request
  in order to reduce the amount of inlay hint flickering. This meant that
  the edit delay also had a significant effect on how far inlay hints
  would lag behind the file progress bar. adjusts the edit delay
  logic so that it only affects requests sent directly after a
  corresponding `didChange` notification. Once the edit delay is used up,
  all further semantic token requests are responded to without delay, so
  that the only latency that affects how far the inlay hints lag behind
  the progress bar is how often we emit refresh requests and how long VS
  Code takes to respond to them.
  - For inlay hints, refresh requests are now emitted 500ms after a
  response to an inlay hint request, not 2000ms, which means that after
  the edit delay, inlay hints should only lag behind the progress bar by
  about up to 500ms. This is justifiable for inlay hints because the
  response should be much smaller than e.g. is the case for semantic
  tokens.
  - In #6768, 'Restart File' did not prompt a refresh, but it does now.
  - VS Code does not immediately remove old inlay hints from the document
  when they are applied. In #6768, this meant that inlay hints would
  linger around for a bit once applied. To mitigate this issue, this PR
  adjusts the inlay hint edit delay logic to identify edits sent from the
  client as being inlay hint applications, and sets the edit delay to 0ms
  for the inlay hint requests following it. This means that inlay hints
  are now applied immediately.
  - In #6768, hovering over single-letter auto-implicit inlay hints was a
  bit finicky because VS Code uses the regular cursor icon on inlay hints,
  not the thin text cursor icon, which means that it is easy to put the
  cursor in the wrong spot. We now add the separation character (` ` or
  `{`) preceding an auto-implicit to the hover range as well, which makes
  hovering over inlay hints much smoother.

* [#6978](https://github.com/leanprover/lean4/pull/6978) fixes a bug where both the inlay hint change invalidation logic
  and the inlay hint edit delay logic were broken in untitled files.
  Thanks to @Julian for spotting this!


* [#7054](https://github.com/leanprover/lean4/pull/7054) adds language server support for request cancellation to the
  following expensive requests: Code actions, auto-completion, document
  symbols, folding ranges and semantic highlighting. This means that when
  the client informs the language server that a request is stale (e.g.
  because it belongs to a previous state of the document), the language
  server will now prematurely cancel the computation of the response in
  order to reduce the CPU load for requests that will be discarded by the
  client anyways.

* [#7087](https://github.com/leanprover/lean4/pull/7087) ensures that all tasks in the language server either use
  dedicated tasks or reuse an existing thread from the thread pool. This
  ensures that elaboration tasks cannot prevent language server tasks from
  being scheduled. This is especially important with parallelism right
  around the corner and elaboration becoming more likely to starve the
  language server of computation, which could drive up language server
  latencies significantly on machines with few cores.

* [#7112](https://github.com/leanprover/lean4/pull/7112) adds a tooltip describing what the auto-implicit inlay hints
  denote, as well as auto-implicit inlay hints for instances.

* [#7134](https://github.com/leanprover/lean4/pull/7134) significantly improves the performance of auto-completion by
  optimizing individual requests by a factor of ~2 and by giving language
  clients like VS Code the opportunity to reuse the state of previous
  completion requests, thus greatly reducing the latency for the
  auto-completion list to update when adding more characters to an
  identifier.

* [#7143](https://github.com/leanprover/lean4/pull/7143) makes the server consistently not report newlines between trace
  nodes to the info view, enabling it to render them on dedicates lines
  without extraneous spacing between them in all circumstances.

* [#7149](https://github.com/leanprover/lean4/pull/7149) adds a fast path to the inlay hint request that makes it re-use
  already computed inlay hints from previous requests instead of
  re-computing them. This is necessary because for some reason VS Code
  emits an inlay hint request for every line you scroll, so we need to be
  able to respond to these requests against the same document state
  quickly. Otherwise, every single scrolled line would result in a request
  that can take a few dozen ms to be responded to in long files, putting
  unnecessary pressure on the CPU.
  It also filters the result set by the inlay hints that have been
  requested.

* [#7153](https://github.com/leanprover/lean4/pull/7153) changes the server to run `lake setup-file` on Lake
  configuration files (e.g., `lakefile.lean`).

* [#7175](https://github.com/leanprover/lean4/pull/7175) fixes an `Elab.async` regression where elaboration tasks are
  cancelled on document edit even though their result may be reused in the
  new document version, reporting an incomplete result.

## Lake

* [#6829](https://github.com/leanprover/lean4/pull/6829) changes the error message for Lake configuration failure to
  reflect that issues do not always arise from an invalid lakefile, but
  sometimes arise from other issues like network errors. The new error
  message encompasses all of these possibilities.

* [#6929](https://github.com/leanprover/lean4/pull/6929) passes the shared library of the previous stage's Lake as a
  plugin to the next stage's Lake in the CMake build. This enables Lake to
  use its own builtin elaborators / initializers at build time.

* [#7001](https://github.com/leanprover/lean4/pull/7001) adds support for plugins to Lake. Precompiled modules are now
  loaded as plugins rather than via `--load-dynlib`.

* [#7024](https://github.com/leanprover/lean4/pull/7024) documents how to use Elan's `+` option with `lake new|init`. It
  also provides an more informative error message if a `+` option leaks
  into Lake (e.g., if a user provides the option to a Lake run without
  Elan).

* [#7157](https://github.com/leanprover/lean4/pull/7157) changes `lake setup-file` to now use Lake as a plugin for files
  which import Lake (or one of its submodules). Thus, the server will now
  load Lake as a plugin when editing a Lake configuration written in Lean.
  This further enables the use of builtin language extensions in Lake.

* [#7171](https://github.com/leanprover/lean4/pull/7171) changes the Lake DSL to use builtin elaborators, macros, and
  initializers.

* [#7182](https://github.com/leanprover/lean4/pull/7182) makes `lake setup-file` succeed on an invalid Lean configuration
  file.

* [#7209](https://github.com/leanprover/lean4/pull/7209) fixes broken Lake tests on Windows' new MSYS2. As of MSYS2
  0.0.20250221, `OSTYPE` is now reported as `cygwin` instead of `msys`,
  which must be accounted for in a few Lake tests.

* [#7211](https://github.com/leanprover/lean4/pull/7211) changes the job monitor to perform run job computation itself as
  a separate job. Now progress will be reported eagerly, even before all
  outstanding jobs have been discovered. Thus, the total job number
  reported can now grow while jobs are still being computed (e.g., the `Y`
  in `[X/Y[` may increase).

* [#7233](https://github.com/leanprover/lean4/pull/7233) uses the Lake plugin when Lake is built with Lake via
  `USE_LAKE`.

* [#7291](https://github.com/leanprover/lean4/pull/7291) changes the Lake job monitor to display the last (i.e., newest)
  running/unfinished job rather than the first. This avoids the monitor
  focusing too long on any one job (e.g., "Running job computation").

* [#7399](https://github.com/leanprover/lean4/pull/7399) reverts the new builtin initializers, elaborators, and macros in
  Lake back to non-builtin.

* [#7608](https://github.com/leanprover/lean4/pull/7608) removes the use of the Lake plugin in the Lake build and in
  configuration files.

## Other

* [#7129](https://github.com/leanprover/lean4/pull/7129) optimizes the performance of the unused variables linter in the
  case of a definition with a huge `Expr` representation

* [#7173](https://github.com/leanprover/lean4/pull/7173) introduces a trace node for each deriving handlers invocation
  for the benefit of `trace.profiler`

* [#7184](https://github.com/leanprover/lean4/pull/7184) adds support for LEAN_BACKTRACE on macOS. This previously only
  worked with glibc, but it can not be enabled for all Unix-like systems,
  since e.g. Musl does not support it.

* [#7190](https://github.com/leanprover/lean4/pull/7190) makes the stage2 Leanc build use the stage2 oleans rather than
  stage1 oleans. This was happening because Leanc's own OLEAN_OUT is at
  the build root rather than the lib/lean subdirectory, so when the build
  added this OLEAN_OUT to LEAN_PATH no oleans were found there and the
  search fell back to the stage1 installation location.

````
