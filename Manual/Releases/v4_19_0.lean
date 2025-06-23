/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: figure out why this is needed with the new compiler
set_option maxRecDepth 11000

#doc (Manual) "Lean 4.19.0 (2025-05-01)" =>
%%%
tag := "release-v4.19.0"
file := "v4.19.0"
%%%

````markdown
For this release, 420 changes landed. In addition to the 164 feature additions and 78 fixes listed below there were 13 refactoring changes, 29 documentation improvements, 31 performance improvements, 9 improvements to the test suite and 94 other changes.

## Highlights

Lean v4.19.0 introduces a number of features, bug fixes, performance gains, library developments,
along with quality-of-life improvements across documentation, the language server, and Lake.

### New Decorations in VS Code

Visual feedback in VS Code has been improved, with the extension now featuring:

* Gutter decorations for errors and warnings. These make the full range of errors/warnings clear,
  which is especially useful when the corresponding squigglies are small.
* End-of-line markers for 'unsolved goals'. These are displayed at the line where
  'unsolved goals' error ends and indicate where the proof needs to be continued.
* 'Goals accomplished!' message. When a theorem or a `Prop`-typed `example` contains no errors or `sorry`s anymore,
  two blue checkmarks appear next to the start of the declaration as a gutter decoration.
  Additionally, a 'Goals accomplished!' message appears under 'Messages' in the InfoView.

Gutter decorations for errors and warnings are available for all Lean 4 versions.
Decorations for 'unsolved goals' and 'goals accomplished' rely on server-side support,
which is added in this version via [#7366](https://github.com/leanprover/lean4/pull/7366).

All of these features can be disabled, and 'Goals accomplished!' icon can be configured in VS Code extension settings.
See [leanprover/vscode-lean4#585](https://github.com/leanprover/vscode-lean4/pull/585) for the details.

### Parallel Elaboration

* [#7084](https://github.com/leanprover/lean4/pull/7084) enables the elaboration of theorem bodies, i.e. proofs, to
  happen in parallel to each other as well as to other elaboration tasks.

### Language Features

* [#5182](https://github.com/leanprover/lean4/pull/5182) makes functions defined by well-founded recursion use an
  `opaque` well-founded proof by default. This reliably prevents kernel
  reduction of such definitions and proofs, which tends to be
  prohibitively slow (fixes [#2171](https://github.com/leanprover/lean4/issues/2171)), and which regularly causes
  hard-to-debug kernel type-checking failures. This change renders
  `unseal` ineffective for such definitions. To avoid the opaque proof,
  annotate the function definition with `@[semireducible]`.

* [#7166](https://github.com/leanprover/lean4/pull/7166) extends the notion of “fixed parameter” of a recursive function
  also to parameters that come after varying function. The main benefit is
  that we get nicer induction principles.

  Before, the definition

  ```lean
  def app (as : List α) (bs : List α) : List α :=
    match as with
    | [] => bs
    | a::as => a :: app as bs
  ```

  produced

  ```lean
  app.induct.{u_1} {α : Type u_1} (motive : List α → List α → Prop) (case1 : ∀ (bs : List α), motive [] bs)
    (case2 : ∀ (bs : List α) (a : α) (as : List α), motive as bs → motive (a :: as) bs) (as bs : List α) : motive as bs
  ```

  and now you get

  ```lean
  app.induct.{u_1} {α : Type u_1} (motive : List α → Prop) (case1 : motive [])
    (case2 : ∀ (a : α) (as : List α), motive as → motive (a :: as)) (as : List α) : motive as
  ```

  because `bs` is fixed throughout the recursion (and can completely be dropped from the principle).

  This is a **breaking change** when such an induction principle is used explicitly. Using `fun_induction` makes proof tactics robust against this change.

  See the PR description for the rules for when a parameter is considered fixed.

  Note that in a definition like

  ```lean
  def app : List α → List α → List α
    | [], bs => bs
    | a::as, bs => a :: app as bs
  ```

  the `bs` is not considered fixed, as it goes through the matcher machinery.

* [#7431](https://github.com/leanprover/lean4/pull/7431) changes the syntax of location modifiers for tactics like `simp`
  and `rw` (e.g., `simp at h ⊢`) to allow the turnstile `⊢` to appear
  anywhere in the sequence of locations.

* [#7457](https://github.com/leanprover/lean4/pull/7457) ensures info tree users such as linters and request handlers
  have access to info subtrees created by async elab task by introducing
  API to leave holes filled by such tasks.

  **Breaking change**: other metaprogramming users of `Command.State.infoState` may need to call `InfoState.substituteLazy` on it manually to fill all holes.

### Updates to structures and classes

* [#7302](https://github.com/leanprover/lean4/pull/7302) changes how fields are elaborated in the `structure`/`class`
  commands and also makes default values respect the structure resolution
  order when there is diamond inheritance. Before, the details of
  subobjects were exposed during elaboration, and in the local context any
  fields that came from a subobject were defined to be projections of the
  subobject field. Now, every field is represented as a local variable.
  All parents (not just subobject parents) are now represented in the
  local context, and they are now local variables defined to be parent
  constructors applied to field variables (inverting the previous
  relationship). See the PR description for further details.

* [#7640](https://github.com/leanprover/lean4/pull/7640) implements the main logic for inheriting and overriding
  autoParam fields in the `structure`/`class` commands, pending being
  enabled in the structure instance notation elaborator. Adds term info to
  overridden fields, so they now can be hovered over, and "go to
  definition" goes to the structure the field is originally defined in.

* [#7717](https://github.com/leanprover/lean4/pull/7717) changes how `{...}`/`where` notation ("structure instance
  notation") elaborates. The notation now tries to simulate a flat
  representation as much as possible, without exposing the details of
  subobjects.
  This is a **breaking change**, see the PR description for further details and mitigation strategies.

* [#7742](https://github.com/leanprover/lean4/pull/7742) adds a feature to `structure`/`class` where binders without
  types on a field definition are interpreted as overriding the type's
  parameters binder kinds in that field's projection function. See the PR description for further details.

### Library Updates

* Developments in the async machinery;
* Standardization of the integer division API;
* Conversions between finite types;
* API expansion of `BitVec` and tree maps;
* Proofs of Bitwuzla rewrite rules;
* Improvements to `List`/`Array`/`Vector`, as well as `HashMap` and `Int`/`Nat`.

See the Library section below for details.

### Other Highlights

* Documentation has been significantly expanded. See the Documentation section below for details.

* [#7185](https://github.com/leanprover/lean4/pull/7185) refactors Lake's build internals to enable the introduction of
  targets and facets beyond packages, modules, and libraries. Facets,
  build keys, build info, and CLI commands have been generalized to
  arbitrary target types.

## Language

* [#5182](https://github.com/leanprover/lean4/pull/5182) makes functions defined by well-founded recursion use an
  `opaque` well-founded proof by default; see highlights section for details.

* [#5998](https://github.com/leanprover/lean4/pull/5998) lets `omega` always abstract its own proofs into an auxiliary
  definition. The size of the olean of Vector.Extract goes down from 20MB
  to 5MB with this, overall stdlib olean size and build instruction count
  go down 5%.

* [#6325](https://github.com/leanprover/lean4/pull/6325) ensures that environments can be loaded, repeatedly, without
  executing arbitrary code

* [#7075](https://github.com/leanprover/lean4/pull/7075) ensures that names suggested by tactics like `simp?` are not
  shadowed by auxiliary declarations in the local context and that names
  of `let rec` and `where` declarations are correctly resolved in tactic
  blocks.

* [#7166](https://github.com/leanprover/lean4/pull/7166) extends the notion of “fixed parameter” of a recursive function
  also to parameters that come after varying function; see highlights section for details.

* [#7256](https://github.com/leanprover/lean4/pull/7256) introduces the `assert!` variant `debug_assert!` that is
  activated when compiled with `buildType` `debug`.

* [#7304](https://github.com/leanprover/lean4/pull/7304) fixes an issue where nested `let rec` declarations within
  `match` expressions or tactic blocks failed to compile if they were
  nested within, and recursively called, a `let rec` that referenced a
  variable bound by a containing declaration.

* [#7324](https://github.com/leanprover/lean4/pull/7324) changes the internal construction of well-founded recursion, to
  not change the type of `fix`’s induction hypothesis in non-defeq ways.

* [#7333](https://github.com/leanprover/lean4/pull/7333) allows aux decls (like generated by `match`) to be generated by
  decreasing_by tactics.

* [#7335](https://github.com/leanprover/lean4/pull/7335) modifies `elabTerminationByHints` in a way that the type of the
  recursive function used for elaboration of the termination measure is
  striped of from optional parameters. It prevents introducing
  dependencies between the default values for arguments, that can cause
  the termination checker to fail.

* [#7353](https://github.com/leanprover/lean4/pull/7353) changes `abstractNestedProofs` so that it also visits the
  subterms in the head of an application.

* [#7362](https://github.com/leanprover/lean4/pull/7362) allows simp dischargers to add aux decls to the environment.
  This enables tactics like `native_decide` to be used here, and unblocks
  improvements to omega in #5998.

* [#7387](https://github.com/leanprover/lean4/pull/7387) uses `-implicitDefEqProofs` in `bv_omega` to ensure it is not
  affected by the change in #7386.

* [#7397](https://github.com/leanprover/lean4/pull/7397) ensures that `Poly.mul p 0` always returns `Poly.num 0`.

* [#7409](https://github.com/leanprover/lean4/pull/7409) allows the use of `dsimp` during preprocessing of well-founded
  definitions. This fixes regressions when using `if-then-else` without
  giving a name to the condition, but where the condition is needed for
  the termination proof, in cases where that subexpression is reachable
  only by dsimp, but not by simp (e.g. inside a dependent let)

* [#7431](https://github.com/leanprover/lean4/pull/7431) changes the syntax of location modifiers for tactics like `simp`
  and `rw` (e.g., `simp at h ⊢`) to allow the turnstile `⊢` to appear
  anywhere in the sequence of locations.

* [#7509](https://github.com/leanprover/lean4/pull/7509) disables the `implicitDefEqProofs` simp option in the
  preprocessor of `bv_decide` in order to account for regressions caused
  by #7387.

* [#7511](https://github.com/leanprover/lean4/pull/7511) fixes two bugs in `simp +arith` that were preventing specific
  subterms from being normalized.

* [#7515](https://github.com/leanprover/lean4/pull/7515) fixes another bug in `simp +arith`. This bug was affecting
  `grind`. See new test for an example.

* [#7551](https://github.com/leanprover/lean4/pull/7551) changes `isNatCmp` to ignore optional arguments annotations,
  when checking for `<`-like comparison between elements of `Nat`. That
  previously caused `guessLex` to fail when checking termination of a
  function, whose signature involved an optional argument of the type
  `Nat`.

* [#7560](https://github.com/leanprover/lean4/pull/7560) ensures that we use the same ordering to normalize linear `Int`
  terms and relations. This change affects `simp +arith` and `grind`
  normalizer.

* [#7622](https://github.com/leanprover/lean4/pull/7622) fixes `fun_induction` when used on structurally recursive
  functions where there are targets occurring before fixed parameters.

* [#7630](https://github.com/leanprover/lean4/pull/7630) fixes a performance issue in the `whnfCore` procedure.

* [#7728](https://github.com/leanprover/lean4/pull/7728) fixes an issue in `abstractNestedProofs`.
  We should abstract proofs occurring in the inferred proposition too.

### Structures

* [#7302](https://github.com/leanprover/lean4/pull/7302) changes how fields are elaborated in the `structure`/`class`
  commands and also makes default values respect the structure resolution
  order when there is diamond inheritance. Before, the details of
  subobjects were exposed during elaboration, and in the local context any
  fields that came from a subobject were defined to be projections of the
  subobject field. Now, every field is represented as a local variable.
  All parents (not just subobject parents) are now represented in the
  local context, and they are now local variables defined to be parent
  constructors applied to field variables (inverting the previous
  relationship). Other notes:
  - The entire collection of parents is processed, and all parent
  projection names are checked for consistency. Every parent appears in
  the local context now.
  - For classes, every parent now contributes an instance, not just the
  parents represented as subobjects.
  - Default values are now processed according to the parent resolution
  order. Default value definition/override auxiliary definitions are
  stored at `StructName.fieldName._default`, and inherited values are
  stored at `StructName.fieldName._inherited_default`. Metaprograms no
  longer need to look at parents when doing calculations on default
  values.
  - Default value omission for structure instance notation pretty printing
  has been updated in consideration of this.
  - Now the elaborator generates a `_flat_ctor` constructor that will be
  used for structure instance elaboration. All types in this constructor
  are put in "field normal form" (projections of parent constructors are
  reduced, and parent constructors are eta reduced), and all fields with
  autoParams are annotated as such. This is not meant for users, but it
  may be useful for metaprogramming.
  - While elaborating fields, any metavariables whose type is one of the
  parents is assigned to that parent. The hypothesis is that, for the
  purpose of elaborating structure fields, parents are fixed: there is
  only *one* instance of any given parent under consideration. See the
  `Magma` test for an example of this being necessary. The hypothesis may
  not be true when there are recursive structures, since different values
  of the structure might not agree on parent fields.

* [#7314](https://github.com/leanprover/lean4/pull/7314) changes elaboration of `structure` parents so that each must be
  fully elaborated before the next one is processed.

* [#7640](https://github.com/leanprover/lean4/pull/7640) implements the main logic for inheriting and overriding
  autoParam fields in the `structure`/`class` commands, pending being
  enabled in the structure instance notation elaborator. Adds term info to
  overridden fields, so they now can be hovered over, and "go to
  definition" goes to the structure the field is originally defined in.

* [#7652](https://github.com/leanprover/lean4/pull/7652) gives `#print` for structures the ability to show the default
  values and auto-param tactics for fields.

* [#7717](https://github.com/leanprover/lean4/pull/7717) changes how `{...}`/`where` notation ("structure instance
  notation") elaborates. The notation now tries to simulate a flat
  representation as much as possible, without exposing the details of
  subobjects. Features:
  - When fields are elaborated, their expected types now have a couple
  reductions applied. For all projections and constructors associated to
  the structure and its parents, projections of constructors are reduced
  and constructors of projections are eta reduced, and also implementation
  detail local variables are zeta reduced in propositions (so tactic
  proofs should never see them anymore). Furthermore, field values are
  beta reduced automatically in successive field types. The example in
  [mathlib4#12129](https://github.com/leanprover-community/mathlib4/issues/12129#issuecomment-2056134533)
  now shows a goal of `0 = 0` rather than `{ toFun := fun x => x }.toFun 0
  = 0`.
  - All parents can now be used as field names, not just the subobject
  parents. These are like additional sources but with three constraints:
  every field of the value must be used, the fields must not overlap with
  other provided fields, and every field of the specified parent must be
  provided for. Similar to sources, the values are hoisted to `let`s if
  they are not already variables, to avoid multiple evaluation. They are
  implementation detail local variables, so they get unfolded for
  successive fields.
  - All class parents are now used to fill in missing fields, not just the
  subobject parents. Closes #6046. Rules: (1) only those parents whose
  fields are a subset of the remaining fields are considered, (2) parents
  are considered only before any fields are elaborated, and (3) only those
  parents whose type can be computed are considered (this can happen if a
  parent depends on another parent, which is possible since #7302).
  - Default values and autoparams now respect the resolution order
  completely: each field has at most one default value definition that can
  provide for it. The algorithm that tries to unstick default values by
  walking up the subobject hierarchy has been removed. If there are
  applications of default value priorities, we might consider it in a
  future release.
  - The resulting constructors are now fully packed. This is implemented
  by doing structure eta reduction of the elaborated expressions.
  - "Magic field definitions" (as reported [on
  Zulip](https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Where.20is.20sSup.20defined.20on.20submodules.3F/near/499578795))
  have been eliminated. This was where fields were being solved for by
  unification, tricking the default value system into thinking they had
  actually been provided. Now the default value system keeps track of
  which fields it has actually solved for, and which fields the user did
  not provide. Explicit structure fields (the default kind) without any
  explicit value definition will result in an error. If it was solved for
  by unification, the error message will include the inferred value, like
  "field 'f' must be explicitly provided, its synthesized value is v"
  - When the notation is used in patterns, it now no longer inserts fields
  using class parents, and it no longer applies autoparams or default
  values. The motivation is that one expects patterns to match only the
  given fields. This is still imperfect, since fields might be solved for
  indirectly.
  - Elaboration now attempts error recovery. Extraneous fields log errors
  and are ignored, missing fields are filled with `sorry`.

* [#7742](https://github.com/leanprover/lean4/pull/7742) adds a feature to `structure`/`class` where binders without
  types on a field definition are interpreted as overriding the type's
  parameters binder kinds in that field's projection function. The rules
  are (1) only a prefix of the binders are interpreted this way, (2)
  multi-identifier binders are allowed but they must all be for
  parameters, (3) only parameters that appear in the declaration itself
  (not from `variables`) can be overridden and (4) the updates will be
  applied after parameter binder kind inference is done. Binder updates
  are not allowed in default value redefinitions. Example application: In
  the following, `(R p)` causes the `R` and `p` parameters to be explicit,
  where normally they would be implicit.
  ```
  class CharP (R : Type u) [AddMonoidWithOne R] (p : Nat) : Prop where
    cast_eq_zero_iff (R p) : ∀ x : Nat, (x : R) = 0 ↔ p ∣ x

  #guard_msgs in #check CharP.cast_eq_zero_iff
  /-
  info: CharP.cast_eq_zero_iff.{u} (R : Type u) {inst✝ : AddMonoidWithOne R} (p : Nat) [self : CharP R p] (x : Nat) :
    ↑x = 0 ↔ p ∣ x
  -/
  ```

* [#7746](https://github.com/leanprover/lean4/pull/7746) adds declaration ranges to structure fields that were copied
  from parents that aren't represented as subobjects, supporting "go to
  definition". The declaration range is the parent in the `extends`
  clause.

### Parallel Elaboration

* [#7084](https://github.com/leanprover/lean4/pull/7084) enables the elaboration of theorem bodies, i.e. proofs, to
  happen in parallel to each other as well as to other elaboration tasks.

* [#7247](https://github.com/leanprover/lean4/pull/7247) makes generation of `match` equations and splitters compatible
  with parallelism.

* [#7261](https://github.com/leanprover/lean4/pull/7261) ensures all equation, unfold, induction, and partial fixpoint
  theorem generators in core are compatible with parallelism.

* [#7348](https://github.com/leanprover/lean4/pull/7348) ensures all equation and unfold theorem generators in core are
  compatible with parallelism.

* [#7457](https://github.com/leanprover/lean4/pull/7457) ensures info tree users such as linters and request handlers
  have access to info subtrees created by async elab task by introducing
  API to leave holes filled by such tasks.

* [#8101](https://github.com/leanprover/lean4/pull/8101) fixes a parallelism regression where linters that e.g. check for
  errors in the command would no longer find such messages.

### bv_decide

* [#7298](https://github.com/leanprover/lean4/pull/7298) adds rewrites to bv_decide's preprocessing that concern
  combinations of if-then-else and operation such as multiplication or
  negation.

* [#7309](https://github.com/leanprover/lean4/pull/7309) fixes a bug where bv_decide's new structure support would
  sometimes not case split on all available structure fvars as their type
  was an mvar.

* [#7329](https://github.com/leanprover/lean4/pull/7329) adds support to bv_decide for simple pattern matching on enum
  inductives. By simple we mean non dependent match statements with all
  arms written out.

* [#7347](https://github.com/leanprover/lean4/pull/7347) upgrades the CaDiCal we ship and use for bv_decide to version
  2.1.2. Additionally it enables binary LRAT proofs on windows by default
  as https://github.com/arminbiere/cadical/issues/112 has been fixed.

* [#7381](https://github.com/leanprover/lean4/pull/7381) refactors the AIG datastructures that underly bv_decide in order
  to allow a better tracking of negations in the circuit. This refactor
  has two effects, for one adding full constant folding to the AIG
  framework and secondly enabling us to add further simplifications from
  the Brummayer Biere paper in the future which was previously
  architecturally impossible.

* [#7390](https://github.com/leanprover/lean4/pull/7390) makes bv_decide's preprocessing handle casts, as we are in the
  constant BitVec fragment we should be able to always remove them using
  BitVec.cast_eq.

* [#7407](https://github.com/leanprover/lean4/pull/7407) adds rules for `-1#w * a = -a` and `a * -1#w = -a` to
  bv_normalize as seen in Bitwuzla's BV_MUL_SPECIAL_CONST.

* [#7417](https://github.com/leanprover/lean4/pull/7417) adds support for enum inductive matches with default branches to
  bv_decide.

* [#7429](https://github.com/leanprover/lean4/pull/7429) adds the BV_EXTRACT_FULL preprocessing rule from Bitwuzla to
  bv_decide.

* [#7436](https://github.com/leanprover/lean4/pull/7436) adds simprocs that turn left and right shifts by constants into
  extracts to bv_decide.

* [#7438](https://github.com/leanprover/lean4/pull/7438) adds the EQUAL_CONST_BV_ADD and BV_AND_CONST rules to
  bv_decide's preprocessor.

* [#7441](https://github.com/leanprover/lean4/pull/7441) adds the BV_CONCAT_CONST, BV_CONCAT_EXTRACT and ELIM_ZERO_EXTEND
  rule from Bitwuzla to bv_decide.

* [#7477](https://github.com/leanprover/lean4/pull/7477) ensures that bv_decide doesn't accidentally operate on terms
  underneath binders. As there is currently no binder construct that is in
  the supported fragment of bv_decide this changes nothing about the proof
  power.

* [#7480](https://github.com/leanprover/lean4/pull/7480) adds the necessary rewrites for the Bitwuzla rules
  BV_ULT_SPECIAL_CONST, BV_SIGN_EXTEND_ELIM, TODO.

* [#7486](https://github.com/leanprover/lean4/pull/7486) adds the BitVec.add_neg_mul rule introduced in #7481 to
  bv_decide's preprocessor.

* [#7491](https://github.com/leanprover/lean4/pull/7491) achieves a speed up in bv_decide's LRAT checker by improving its
  input validation.

* [#7521](https://github.com/leanprover/lean4/pull/7521) adds the equivalent of `Array.emptyWithCapacity` to the AIG
  framework and applies it to `bv_decide`. This is particularly useful as
  we are only working with capacities that are always known at run time so
  we should never have to reallocate a `RefVec`.

* [#7527](https://github.com/leanprover/lean4/pull/7527) adds the BV_EXTRACT_CONCAT_LHS_RHS, NORM_BV_ADD_MUL and
  NORM_BV_SHL_NEG rewrite from Bitwuzla as well as a reduction from
  getLsbD to extractLsb' to bv_decide.

* [#7615](https://github.com/leanprover/lean4/pull/7615) adds the ADD part of bitwuzlas BV_EXTRACT_ADD_MUL rule to
  bv_decide's preprocessor.

* [#7617](https://github.com/leanprover/lean4/pull/7617) adds the known bits optimization from the multiplication circuit
  to the add one, allowing us to discover potentially even more symmetries
  before going to the SAT solver.

* [#7636](https://github.com/leanprover/lean4/pull/7636) makes sure that the expression level cache in bv_decide is
  maintained across the entire bitblaster instead of just locally per
  BitVec expression.

* [#7644](https://github.com/leanprover/lean4/pull/7644) adds a cache to the reflection procedure of bv_decide.

* [#7649](https://github.com/leanprover/lean4/pull/7649) changes the AIG representation of constants from `const (b :
  Bool)` to a single constructor `false`. Since #7381 `Ref` contains an
  `invert` flag meaning the constant `true` can be represented as a `Ref`
  to `false` with `invert` set, so no expressivity is lost.

* [#7655](https://github.com/leanprover/lean4/pull/7655) adds the preprocessing rule for extraction over multiplication
  to bv_decide.

* [#7663](https://github.com/leanprover/lean4/pull/7663) uses computed fields to store the hash code and pointer equality
  to increase performance of comparison and hashmap lookups on the core
  data structure used by the bitblaster.

* [#7670](https://github.com/leanprover/lean4/pull/7670) improves the caching computation of the atoms assignment in
  bv_decide's reflection procedure.

* [#7698](https://github.com/leanprover/lean4/pull/7698) adds more sharing and caching procedures to bv_decide's
  reflection step.

* [#7720](https://github.com/leanprover/lean4/pull/7720) compresses the AIG representation by storing the inverter bit in
  the lowest bit of the gate descriptor instead of as a separate `Bool`.

* [#7727](https://github.com/leanprover/lean4/pull/7727) avoids some unnecessary allocations in the CNF to dimacs
  conversion

* [#7733](https://github.com/leanprover/lean4/pull/7733) ensures that in the AIG the constant circuit node is always
  stored at the first spot. This allows us to skip performing a cache
  lookup when we require a constant node.

### Grind

* [#7355](https://github.com/leanprover/lean4/pull/7355) fixes a bug in the `markNestedProofs` preprocessor used in the
  `grind` tactic.

* [#7392](https://github.com/leanprover/lean4/pull/7392) fixes an issue in the `grind` tactic when case splitting on
  if-then-else expressions.

* [#7510](https://github.com/leanprover/lean4/pull/7510) ensures that `grind` can be used as a more powerful
  `contradiction` tactic, sparing the user from having to type `exfalso;
  grind` or `intros; exfalso; grind`.

* [#7512](https://github.com/leanprover/lean4/pull/7512) adds missing normalization rules for `Nat` div and mod to the
  `grind` tactic.

* [#7514](https://github.com/leanprover/lean4/pull/7514) adds more missing normalization rules for `div` and `mod` to
  `grind`.

* [#7532](https://github.com/leanprover/lean4/pull/7532) fixes the procedure for putting new facts into the `grind`
  "to-do" list. It ensures the new facts are preprocessed. also
  removes some of the clutter in the `Nat.sub` support.

* [#7540](https://github.com/leanprover/lean4/pull/7540) adds `[grind cases eager]` attribute to `Subtype`. See new test.

* [#7553](https://github.com/leanprover/lean4/pull/7553) removes a bad normalization rule in `grind`, and adds a missing
  dsimproc.

* [#7641](https://github.com/leanprover/lean4/pull/7641) implements basic model-based theory combination in `grind`.
  `grind` can now solve examples such as
  ```lean
  example (f : Int → Int) (x : Int)
      : 0 ≤ x → x ≠ 0 → x ≤ 1 → f x = 2 → f 1 = 2 := by
    grind
  ```

* [#7712](https://github.com/leanprover/lean4/pull/7712) ensures `grind` always abstract its own proofs into an auxiliary
  definition/theorem. This is similar to #5998 but for `grind`

* [#7714](https://github.com/leanprover/lean4/pull/7714) fixes an assertion violation in the `grind` model-based theory
  combination module.

* [#7723](https://github.com/leanprover/lean4/pull/7723) adds the configuration options `zeta` and `zetaDelta` in
  `grind`. Both are set to `true` by default.

* [#7724](https://github.com/leanprover/lean4/pull/7724) adds `dite_eq_ite` normalization rule to `grind`. This rule is
  important to adjust mismatches between a definition and its function
  induction principle.

* [#7726](https://github.com/leanprover/lean4/pull/7726) fixes the `markNestedProofs` procedure used in `grind`. It was
  missing the case where the type of a nested proof may contain other
  nested proofs.

* [#7760](https://github.com/leanprover/lean4/pull/7760) ensures `grind` is using the default transparency setting when
  computing auxiliary congruence lemmas.

* [#7765](https://github.com/leanprover/lean4/pull/7765) improves how `grind` normalizes dependent implications during
  introduction.
  Previously, `grind` would introduce a hypothesis `h : p` for a goal of
  the form `.. ⊢ (h : p) → q h`, and then normalize and assert a
  non-dependent copy of `p`. As a result, the local context would contain
  both `h : p` and a separate `h' : p'`, where `p'` is the normal form of
  `p`. Moreover, `q` would still depend on the original `h`.

* [#7776](https://github.com/leanprover/lean4/pull/7776) improves the equality proof discharger used by the E-matching
  procedure in `grind`.

* [#7777](https://github.com/leanprover/lean4/pull/7777) fixes the introduction procedure used in `grind`. It was not
  registering local instances that are also propositions. See new test.

* [#7778](https://github.com/leanprover/lean4/pull/7778) adds missing propagation rules for `LawfulBEq A` to `grind`.
  They are needed in a context where the instance `DecidableEq A` is not
  available. See new test.

* [#7781](https://github.com/leanprover/lean4/pull/7781) adds a new propagation rule for `Bool` disequalities to `grind`.
  It now propagates `x = true` (`x = false`) from the disequality `x =
  false` (`x = true`). It ensures we don't have to perform case analysis
  on `x` to learn this fact. See tests.

### CutSat

* [#7312](https://github.com/leanprover/lean4/pull/7312) implements proof term generation for `cooper_dvd_left` and its
  variants in the cutsat procedure for linear integer arithmetic.

* [#7315](https://github.com/leanprover/lean4/pull/7315) implements the Cooper conflict resolution in cutsat. We still
  need to implement the backtracking and disequality case.

* [#7339](https://github.com/leanprover/lean4/pull/7339) implements cooper conflict resolution in the cutsat procedure.
  It also fixes several bugs in the proof term construction. We still need
  to add more tests, but we can already solve the following example that
  `omega` fails to solve:
  ```lean
  example (x y : Int) :
      27 ≤ 11*x + 13*y →
      11*x + 13*y ≤ 45 →
      -10 ≤ 7*x - 9*y →
      7*x - 9*y ≤ 4 → False := by
    grind
  ```

* [#7351](https://github.com/leanprover/lean4/pull/7351) ensures cutsat does not have to perform case analysis in the
  univariate polynomial case. That it, it can close a goal whenever there
  is no solution for a divisibility constraint in an interval. Example of
  theorem that is now proved in a single step by cutsat:
  ```lean
  example (x : Int) : 100 ≤ x → x ≤ 10000 → 20000 ∣ 3*x → False := by
    grind
  ```

* [#7357](https://github.com/leanprover/lean4/pull/7357) adds support for `/` and `%` to the cutsat procedure.

* [#7369](https://github.com/leanprover/lean4/pull/7369) uses `let`-declarations for each polynomial occurring in a proof
  term generated by the cutsat procedure.

* [#7370](https://github.com/leanprover/lean4/pull/7370) simplifies the proof term due to the Cooper's conflict
  resolution in cutsat.

* [#7373](https://github.com/leanprover/lean4/pull/7373) implements the last missing case for the cutsat procedure and
  fixes a bug. During model construction, we may encounter a bounded
  interval containing integer solutions that satisfy the divisibility
  constraint but fail to satisfy known disequalities.

* [#7394](https://github.com/leanprover/lean4/pull/7394) adds infrastructure necessary for supporting `Nat` in the cutsat
  procedure. It also makes the `grind` more robust.

* [#7396](https://github.com/leanprover/lean4/pull/7396) fixes a bug in the cutsat model construction. It was searching
  for a solution in the wrong direction.

* [#7401](https://github.com/leanprover/lean4/pull/7401) improves the cutsat model search procedure by tightening
  inequalities using divisibility constraints.

* [#7494](https://github.com/leanprover/lean4/pull/7494) implements support for `Nat` inequalities in the cutsat
  procedure.

* [#7495](https://github.com/leanprover/lean4/pull/7495) implements support for `Nat` divisibility constraints in the
  cutsat procedure.

* [#7501](https://github.com/leanprover/lean4/pull/7501) implements support for `Nat` equalities and disequalities in the
  cutsat procedure.

* [#7502](https://github.com/leanprover/lean4/pull/7502) implements support for `Nat` div and mod in the cutsat
  procedure.

* [#7503](https://github.com/leanprover/lean4/pull/7503) implements support for `Nat.sub` in cutsat

* [#7536](https://github.com/leanprover/lean4/pull/7536) implements support for `¬ d ∣ p` in the cutsat procedure.

* [#7537](https://github.com/leanprover/lean4/pull/7537) implements support for `Int.natAbs` and `Int.toNat` in the
  cutsat procedure.

* [#7538](https://github.com/leanprover/lean4/pull/7538) fixes a bug in the cutsat model construction. It was not
  resetting the decision stack at the end of the search.

* [#7561](https://github.com/leanprover/lean4/pull/7561) fixes the support for nonlinear `Nat` terms in cutsat. For
  example, cutsat was failing in the following example
  ```lean
  example (i j k l : Nat) : i / j + k + l - k = i / j + l := by grind
  ```
  because we were not adding the fact that `i / j` is non negative when we
  inject the `Nat` expression into `Int`.

* [#7579](https://github.com/leanprover/lean4/pull/7579) improves the counterexamples produced by the cutsat procedure,
  and adds proper support for `Nat`. Before this PR, the assignment for an
  natural variable `x` would be represented as `NatCast.natCast x`.

## Library

* [#6496](https://github.com/leanprover/lean4/pull/6496) adds short-circuit support to bv_decide to accelerate
  multiplications with shared coefficients. In particular, `a * x = b * x`
  can be extended to `a = b v (a * x = b * x)`. The latter is faster if `a
  = b` is true, as `a = b` may be evaluated without considering the
  multiplication circuit. On the other hand, we require the multiplication
  circuit, as `a * x = b * x -> a = b` is not always true due to two's
  complement wrapping.

* [#7141](https://github.com/leanprover/lean4/pull/7141) generalizes `cond` to allow the motive to be in `Sort u`, not
  just `Type u`.

* [#7289](https://github.com/leanprover/lean4/pull/7289) adds `getKey_beq`, `getKey_congr` and variants to the hashmap
  api.

* [#7319](https://github.com/leanprover/lean4/pull/7319) continues alignment of lemmas about `Int.ediv/fdiv/tdiv`,
  including adding notes about "missing" lemmas that do not apply in one
  case. Also lemmas about `emod/fmod/tmod`. There's still more to do.

* [#7338](https://github.com/leanprover/lean4/pull/7338) adds @[simp] to `Int.neg_inj`.

* [#7341](https://github.com/leanprover/lean4/pull/7341) adds an equivalence relation to the hash map with several lemmas
  for it.

* [#7356](https://github.com/leanprover/lean4/pull/7356) adds lemmas reducing monadic operations with `pure` to the
  non-monadic counterparts.

* [#7358](https://github.com/leanprover/lean4/pull/7358) fills further gaps in the integer division API, and mostly
  achieves parity between the three variants of integer division. There
  are still some inequality lemmas about `tdiv` and `fdiv` that are
  missing, but as they would have quite awkward statements I'm hoping that
  for now no one is going to miss them.

* [#7378](https://github.com/leanprover/lean4/pull/7378) adds lemmas about `Int` that will be required in #7368.

* [#7380](https://github.com/leanprover/lean4/pull/7380) moves `DHashMap.Raw.foldRev(M)` into `DHashMap.Raw.Internal`.

* [#7406](https://github.com/leanprover/lean4/pull/7406) makes the instance for `Subsingleton (Squash α)` work for `α :
  Sort u`.

* [#7418](https://github.com/leanprover/lean4/pull/7418) renames several hash map lemmas (`get` -> `getElem`) and uses
  `m[k]?` instead of `get? m k` (and also for `get!` and `get`).

* [#7432](https://github.com/leanprover/lean4/pull/7432) adds a consequence of `Nat.add_div` using a divisibility
  hypothesis.

* [#7433](https://github.com/leanprover/lean4/pull/7433) makes `simp` able to simplify basic `for` loops in monads other
  than `Id`.

* [#7435](https://github.com/leanprover/lean4/pull/7435) reviews the `Nat` and `Int` API, making the interfaces more
  consistent.

* [#7445](https://github.com/leanprover/lean4/pull/7445) renames `Array.mkEmpty` to `emptyWithCapacity`. (Similarly for
  `ByteArray` and `FloatArray`.)

* [#7446](https://github.com/leanprover/lean4/pull/7446) prefers using `∅` instead of `.empty` functions. We may later
  rename `.empty` functions to avoid the naming clash with
  `EmptyCollection`, and to better express semantics of functions which
  take an optional capacity argument.

* [#7451](https://github.com/leanprover/lean4/pull/7451) renames the member `insert_emptyc_eq` of the `LawfulSingleton`
  typeclass to `insert_empty_eq` to conform to the recommended spelling of
  `∅` as `empty`.

* [#7466](https://github.com/leanprover/lean4/pull/7466) further cleans up simp lemmas for `Int`.

* [#7516](https://github.com/leanprover/lean4/pull/7516) changes the order of arguments for `List.modify` and
  `List.insertIdx`, making them consistent with `Array`.

* [#7522](https://github.com/leanprover/lean4/pull/7522) splits off the required theory about `Nat`, `Fin` and `BitVec`
  from #7484.

* [#7529](https://github.com/leanprover/lean4/pull/7529) upstreams `bind_congr` from Mathlib and proves that the minimum
  of a sorted list is its head and weakens the antisymmetry condition of
  `min?_eq_some_iff`. Instead of requiring an `Std.Antisymm` instance,
  `min?_eq_some_iff` now only expects a proof that the relation is
  antisymmetric *on the elements of the list*. If the new premise is left
  out, an autoparam will try to derive it from `Std.Antisymm`, so existing
  usages of the theorem will most likely continue to work.

* [#7541](https://github.com/leanprover/lean4/pull/7541) corrects names of a number of lemmas, where the incorrect name
  was identified automatically by a
  [tool](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/automatic.20spelling.20generation.20.26.20comparison/near/505760384)
  written by @Rob23oba.

* [#7554](https://github.com/leanprover/lean4/pull/7554) adds SMT-LIB operators to detect overflow `BitVec.negOverflow`,
  according to the [SMTLIB
  standard](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2),
  and the theorem proving equivalence of such definition with the `BitVec`
  library functions (`negOverflow_eq`).

* [#7558](https://github.com/leanprover/lean4/pull/7558) changes the definition of `Nat.div` and `Nat.mod` to use a
  structurally recursive, fuel-based implementation rather than
  well-founded recursion. This leads to more predicable reduction behavior
  in the kernel.

* [#7565](https://github.com/leanprover/lean4/pull/7565) adds `BitVec.toInt_sdiv` plus a lot of related bitvector theory
  around divisions.

* [#7614](https://github.com/leanprover/lean4/pull/7614) marks `Nat.div` and `Nat.modCore` as `irreducible`, to recover
  the behavior from from before #7558.

* [#7672](https://github.com/leanprover/lean4/pull/7672) reviews the implicitness of arguments across List/Array/Vector,
  generally trying to make arguments implicit where possible, although
  sometimes correcting propositional arguments which were incorrectly
  implicit to explicit.

* [#7687](https://github.com/leanprover/lean4/pull/7687) provides `Inhabited`, `Ord` (if missing), `TransOrd`,
  `LawfulEqOrd` and `LawfulBEqOrd` instances for various types, namely
  `Bool`, `String`, `Nat`, `Int`, `UIntX`, `Option`, `Prod` and date/time
  types. It also adds a few related theorems, especially about how the
  `Ord` instance for `Int` relates to `LE` and `LT`.

* [#7692](https://github.com/leanprover/lean4/pull/7692) upstreams a small number of ordering lemmas for `Fin` from
  mathlib.

* [#7700](https://github.com/leanprover/lean4/pull/7700) provides `Ord`-related instances such as `TransOrd` for `IntX`,
  `Ordering`, `BitVec`, `Array`, `List` and `Vector`.

* [#7704](https://github.com/leanprover/lean4/pull/7704) adds lemmas about the modulo operation defined on signed bounded
  integers.

* [#7706](https://github.com/leanprover/lean4/pull/7706) performs various cleanup tasks on `Init/Data/UInt/*` and
  `Init/Data/SInt/*`.

* [#7729](https://github.com/leanprover/lean4/pull/7729) replaces `assert!` with `assertBEq` to fix issues where asserts
  didn't trigger the `ctest` due to being in a separate task. This was
  caused by panics not being caught in tasks, while IO errors were handled
  by the `AsyncTask` if we use the `block` function on them.

* [#7756](https://github.com/leanprover/lean4/pull/7756) adds lemmas about `Nat.gcd` (some of which are currently present
  in mathlib).

  **BREAKING CHANGE:** While many lemmas were renamed and the lemma with the old signature was simply deprecated, some lemmas were changed without renaming them. They now use the `getElem` variants instead of `get`.

### Async

* [#6683](https://github.com/leanprover/lean4/pull/6683) introduces TCP socket support using the LibUV library, enabling
  asynchronous I/O operations with it.

* [#7571](https://github.com/leanprover/lean4/pull/7571) fixes #7478 by modifying `number` specifiers from `atLeast size`
  to `flexible size` for parsing. This change allows:
  - 1 repetition to accept 1 or more characters
  - More than 1 repetition to require exactly that many characters

* [#7574](https://github.com/leanprover/lean4/pull/7574) introduces UDP socket support using the LibUV library, enabling
  asynchronous I/O operations with it.

* [#7578](https://github.com/leanprover/lean4/pull/7578) introduces a function called `interfaceAddresses` that retrieves
  an array of system’s network interfaces.

* [#7584](https://github.com/leanprover/lean4/pull/7584) introduces a structure called `FormatConfig`, which provides
  additional configuration options for `GenericFormat`, such as whether
  leap seconds should be allowed during parsing. By default, this option
  is set to `false`.

* [#7751](https://github.com/leanprover/lean4/pull/7751) adds `Std.BaseMutex.tryLock` and `Std.Mutex.tryAtomically` as
  well as unit tests for our locking and condition variable primitives.

* [#7755](https://github.com/leanprover/lean4/pull/7755) adds `Std.RecursiveMutex` as a recursive/reentrant equivalent to
  `Std.Mutex`.

* [#7771](https://github.com/leanprover/lean4/pull/7771) adds a barrier primitive as `Std.Barrier`.

### Finite Types

* [#7228](https://github.com/leanprover/lean4/pull/7228) adds simprocs to reduce expressions involving `IntX`.

* [#7274](https://github.com/leanprover/lean4/pull/7274) adds lemmas about iterated conversions between finite types,
  starting with something of type `IntX`.

* [#7340](https://github.com/leanprover/lean4/pull/7340) adds lemmas for iterated conversions between finite types which
  start with `Nat`/`Int`/`Fin`/`BitVec` and then go through `UIntX`.

* [#7368](https://github.com/leanprover/lean4/pull/7368) adds lemmas for iterated conversions between finite types,
  starting with something of type `Nat`/`Int`/`Fin`/`BitVec` and going
  through `IntX`.

* [#7414](https://github.com/leanprover/lean4/pull/7414) adds the remaining lemmas about iterated conversions of finite
  type that go through signed or unsigned bounded integers.

* [#7484](https://github.com/leanprover/lean4/pull/7484) adds some lemmas about operations defined on `UIntX`

* [#7487](https://github.com/leanprover/lean4/pull/7487) adds the instance `Neg UInt8`.

* [#7592](https://github.com/leanprover/lean4/pull/7592) adds theory about signed finite integers relating operations and
  conversion functions.

* [#7598](https://github.com/leanprover/lean4/pull/7598) adds miscellaneous results about `Nat` and `BitVec` that will be
  required for `IntX` theory (#7592).

* [#7685](https://github.com/leanprover/lean4/pull/7685) contains additional material about `BitVec` and `Int` spun off
  from #7592.

* [#7694](https://github.com/leanprover/lean4/pull/7694) contains additional material on `BitVec`, `Int` and `Nat`, split
  off from #7592.

### Tree Map

* [#7270](https://github.com/leanprover/lean4/pull/7270) provides lemmas about the tree map functions `foldlM`, `foldl`,
  `foldrM` and `foldr` and their interactions with other functions for
  which lemmas already exist. Additionally, it generalizes the
  `fold*`/`keys` lemmas to arbitrary tree maps, which were previously
  stated only for the `DTreeMap α Unit` case.

* [#7331](https://github.com/leanprover/lean4/pull/7331) provides lemmas about the tree map function `insertMany` and its
  interaction with other functions for which lemmas already exist. Most
  lemmas about `ofList`, which is related to `insertMany`, are not
  included.

* [#7360](https://github.com/leanprover/lean4/pull/7360) provides lemmas about the tree map function `ofList` and
  interactions with other functions for which lemmas already exist.

* [#7367](https://github.com/leanprover/lean4/pull/7367) provides lemmas for the tree map functions `alter` and `modify`
  and their interactions with other functions for which lemmas already
  exist.

  **BREAKING CHANGE:** The signature of `size_alter` was corrected for all four hash map types. Instead of relying on the boolean operations `contains` and `&&` in the if statements, we now use the `Prop`-based operations `Membership` and `And`.

* [#7412](https://github.com/leanprover/lean4/pull/7412) provides lemmas about the tree map that have been introduced to
  the hash map in #7289.

* [#7419](https://github.com/leanprover/lean4/pull/7419) provides lemmas about the tree map function `modify` and its
  interactions with other functions for which lemmas already exist.

* [#7437](https://github.com/leanprover/lean4/pull/7437) provides (some but not all) lemmas about the tree map function
  `minKey?`.

* [#7556](https://github.com/leanprover/lean4/pull/7556) provides lemmas about the tree map function `minKey?` and its
  interaction with other functions for which lemmas already exist.

* [#7600](https://github.com/leanprover/lean4/pull/7600) provides lemmas about the tree map function `minKey!` and its
  interactions with other functions for which lemmas already exist.

* [#7626](https://github.com/leanprover/lean4/pull/7626) provides lemmas for the tree map function `minKeyD` and its
  interations with other functions for which lemmas already exist.

* [#7657](https://github.com/leanprover/lean4/pull/7657) provides lemmas for the tree map function `maxKey?` and its
  interations with other functions for which lemmas already exist.

* [#7660](https://github.com/leanprover/lean4/pull/7660) provides lemmas for the tree map function `minKey` and its
  interations with other functions for which lemmas already exist.

* [#7664](https://github.com/leanprover/lean4/pull/7664) fixes a bug in the definition of the tree map functions `maxKey`
  and `maxEntry`. Moreover, it provides lemmas for this function and its
  interactions with other function for which lemmas already exist.

* [#7674](https://github.com/leanprover/lean4/pull/7674) add missing lemmas about the tree map: `minKey*` variants return
  the head of `keys`, `keys` and `toList` are ordered and `getKey*
  t.minKey?` equals the minimum.

* [#7675](https://github.com/leanprover/lean4/pull/7675) provides lemmas about the tree map function `maxKeyD` and its
  interactions with other functions for which lemmas already exist.

* [#7686](https://github.com/leanprover/lean4/pull/7686) provides lemmas for the tree map function `maxKey!` and its
  interactions with other functions for which lemmas already exist.

* [#7695](https://github.com/leanprover/lean4/pull/7695) removes simp lemmas about the tree map with a metavariable in
  the head of the discrimination pattern.

* [#7697](https://github.com/leanprover/lean4/pull/7697) is a follow-up to #7695, which removed `simp` attributes from
  tree map lemmas with bad discrimination patterns. In this PR, we
  introduce some `Ord`-based lemmas that are more simp-friendly.

### BitVec API

* [#7104](https://github.com/leanprover/lean4/pull/7104) adds `BitVec.[toNat|toFin|toInt]_[sshiftRight|sshiftRight']`
  plus variants with `of_msb_*`. While at it, we also add
  `toInt_zero_length` and `toInt_of_zero_length`. In support of our main
  theorem we add `toInt_shiftRight_lt` and `le_toInt_shiftRight`, which
  make the main theorem automatically derivable via omega.

* [#7225](https://github.com/leanprover/lean4/pull/7225) contains `BitVec.(toInt, toFin)_twoPow` theorems, completing the
  API for `BitVec.*_twoPow`. It also expands the `toNat_twoPow` API with
  `toNat_twoPow_of_le`, `toNat_twoPow_of_lt`, as well as
  `toNat_twoPow_eq_if` and moves `msb_twoPow` up, as it is used in the
  `toInt_msb` proof.

* [#7415](https://github.com/leanprover/lean4/pull/7415) adds a few lemmas about the interactions of `BitVec` with `Fin`
  and `Nat`.

* [#7420](https://github.com/leanprover/lean4/pull/7420) generalizes `BitVec.toInt_[lt|le]'` to not require `0 < w`.

* [#7465](https://github.com/leanprover/lean4/pull/7465) adds the theorem:
  ```lean
  theorem lt_allOnes_iff {x : BitVec w} : x < allOnes w ↔ x ≠ allOnes w
  ```
  to simplify comparisons against `-1#w`. This is a corollary of the
  existing lemma:
  ```lean
  theorem allOnes_le_iff {x : BitVec w} : allOnes w ≤ x ↔ x = allOnes w
  ```

* [#7599](https://github.com/leanprover/lean4/pull/7599) adds SMT-LIB operators to detect overflow `BitVec.(usubOverflow,
  ssubOverflow)`, according to the [SMTLIB
  standard](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2),
  and the theorems proving equivalence of such definition with the
  `BitVec` library functions `BittVec.(usubOverflow_eq, ssubOverflow_eq)`.

* [#7604](https://github.com/leanprover/lean4/pull/7604) adds bitvector theorems that to push negation into other
  operations, following Hacker's Delight: Ch2.1.

* [#7605](https://github.com/leanprover/lean4/pull/7605) adds theorems `BitVec.[(toInt, toFin)_(extractLsb,
  extractLsb')]`, completing the API for `BitVec.(extractLsb,
  extractLsb')`.

* [#7616](https://github.com/leanprover/lean4/pull/7616) introduces `BitVec.(toInt, toFin)_rotate(Left, Right)`,
  completing the API for `BitVec.rotate(Left, Right)`

* [#7658](https://github.com/leanprover/lean4/pull/7658) introduces `BitVec.(toFin_signExtend_of_le, toFin_signExtend)`,
  completing the API for `BitVec.signExtend`.

* [#7661](https://github.com/leanprover/lean4/pull/7661) adds theorems `BitVec.[(toFin, toInt)_setWidth',
  msb_setWidth'_of_lt, toNat_lt_twoPow_of_le, toInt_setWidth'_of_lt]`,
  completing the API for `BitVec.setWidth'`.

* [#7699](https://github.com/leanprover/lean4/pull/7699) adds the `BitVec.toInt_srem` lemma, relating `BitVec.srem` with
  `Int.tmod`.

### Bitwuzla Rewrite Rules

* [#7424](https://github.com/leanprover/lean4/pull/7424) proves Bitwuzla's rule
  [`BV_ZERO_EXTEND_ELIM`](https://github.com/bitwuzla/bitwuzla/blob/6a1a768987cca77f36ebfe06f3a786348a481bbd/src/rewrite/rewrites_bv.cpp#L4021-L4033):

  ```lean
  theorem setWidth_eq_append {v : Nat} {x : BitVec v} {w : Nat} (h : v ≤ w) :
      x.setWidth w = ((0#(w - v)) ++ x).cast (by omega) := by
  ```

* [#7426](https://github.com/leanprover/lean4/pull/7426) adds the Bitwuzla rewrite rule
  [`BV_EXTRACT_FULL`](https://github.com/bitwuzla/bitwuzla/blob/6a1a768987cca77f36ebfe06f3a786348a481bbd/src/rewrite/rewrites_bv.cpp#L1236-L1253),
  which is useful for the bitblaster to simplify `extractLsb'` based
  expressions.

* [#7427](https://github.com/leanprover/lean4/pull/7427) implements the bitwuzla rule
  [`BV_CONCAT_EXTRACT`](https://github.com/bitwuzla/bitwuzla/blob/main/src/rewrite/rewrites_bv.cpp#L1146-L1176).
  This will be used by the bitblaster to simplify adjacent `extract`s
  into a single `extract`.

* [#7454](https://github.com/leanprover/lean4/pull/7454) implements the bitwuzla rule
  [BV_SIGN_EXTEND_ELIM](https://github.com/bitwuzla/bitwuzla/blob/main/src/rewrite/rewrites_bv.cpp#L3638-L3663),
  which rewrites a `signExtend x` as an `append` of the appropriate sign
  bits, followed by the bits of `x`.

* [#7461](https://github.com/leanprover/lean4/pull/7461) introduces a bitvector associativity/commutativity normalization
  on bitvector terms of the form `(a * b) = (c * d)` for `a, b, c, d`
  bitvectors. This mirrors Bitwuzla's `PassNormalize::process`'s
  `PassNormalize::normalize_eq_add_mul`.

* [#7481](https://github.com/leanprover/lean4/pull/7481) implements the Bitwuzla rewrites [BV_ADD_NEG_MUL](), and
  associated lemmas to make the proof streamlined. ```bvneg (bvadd a
  (bvmul a b)) = (bvmul a (bvnot b))```, or spelled as lean:

  ```lean
  theorem neg_add_mul_eq_mul_not {x y : BitVec w} :
      - (x + x * y) = (x * ~~~ y)
  ```

* [#7482](https://github.com/leanprover/lean4/pull/7482) implements the
  [BV_EXTRACT_CONCAT](https://github.com/bitwuzla/bitwuzla/blob/6a1a768987cca77f36ebfe06f3a786348a481bbd/src/rewrite/rewrites_bv.cpp#L1264)
  rule from Bitwuzla, which explains how to extract bits from an append.
  We first prove a 'master theorem' which has the full case analysis, from
  which we rapidly derive the necessary `BV_EXTRACT_CONCAT` theorems:

  ```lean
  theorem extractLsb'_append_eq_ite {v w} {xhi : BitVec v} {xlo : BitVec w} {start len : Nat} :
      extractLsb' start len (xhi ++ xlo) =
      if hstart : start < w
      then
        if hlen : start + len < w
        then extractLsb' start len xlo
        else
          (((extractLsb' (start - w) (len - (w - start)) xhi) ++
              extractLsb' start (w - start) xlo)).cast (by omega)
      else
        extractLsb' (start - w) len xhi

* [#7493](https://github.com/leanprover/lean4/pull/7493) implements the Bitwuzla rewrite rule
  [NORM_BV_ADD_MUL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv_norm.cpp#L19-L23),
  and the associated lemmas to allow for expedient rewriting:

  ```lean
  theorem neg_add_mul_eq_mul_not {x y : BitVec w} : - (x + x * y) = x * ~~~ y
  ```

* [#7508](https://github.com/leanprover/lean4/pull/7508) shows that negation commutes with left shift, which is the
  Bitwuzla rewrite
  [NORM_BV_SHL_NEG](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv_norm.cpp#L142-L148).

* [#7594](https://github.com/leanprover/lean4/pull/7594) implements the Bitwuzla rewrites
  [BV_EXTRACT_ADD_MUL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L1495-L1510),
  which witness that the high bits at `i >= len` do not affect the bits of
  the product upto `len`.

* [#7595](https://github.com/leanprover/lean4/pull/7595) implements the addition rewrite from the Bitwuzla rewrite
  [BV_EXTRACT_ADD_MUL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L1495-L1510),
  which witness that the high bits at `i >= len` do not affect the bits of
  the sum upto `len`:

  ```lean
  theorem extractLsb'_add {w len} {x y : BitVec w} (hlen : len ≤ w) :
      (x + y).extractLsb' 0 len = x.extractLsb' 0 len + y.extractLsb' 0 len
  ```

* [#7757](https://github.com/leanprover/lean4/pull/7757) adds the Bitwuzla rewrite `NORM_BV_ADD_CONCAT` for symbolic
  simplification of add-of-append.

## Compiler

* [#7398](https://github.com/leanprover/lean4/pull/7398) fixes a scoping error in the cce (Common Case Elimination) pass
  of the old code generator. This pass would create a join point for
  common minor premises even if some of those premises were in the bodies
  of locally defined functions, which results in an improperly scoped
  reference to a join point. The fix is to save/restore candidates when
  visiting a lambda.

* [#7710](https://github.com/leanprover/lean4/pull/7710) improves memory use of Lean, especially for longer-running
  server processes, by up to 60%

## Pretty Printing

* [#7589](https://github.com/leanprover/lean4/pull/7589) changes the structure instance notation pretty printer so that
  fields are omitted if their value is definitionally equal to the default
  value for the field (up to reducible transparancy). Setting
  `pp.structureInstances.defaults` to true forces such fields to be pretty
  printed anyway.

## Documentation

* [#7198](https://github.com/leanprover/lean4/pull/7198) makes the docstrings in the `Char` namespace follow the
  documentation conventions.

* [#7204](https://github.com/leanprover/lean4/pull/7204) adds docstrings for the `Id` monad.

* [#7246](https://github.com/leanprover/lean4/pull/7246) updates existing docstrings for Bool and adds the missing ones.

* [#7288](https://github.com/leanprover/lean4/pull/7288) fixes the doc of `List.removeAll`

* [#7365](https://github.com/leanprover/lean4/pull/7365) updates docstrings and adds some that are missing.

* [#7452](https://github.com/leanprover/lean4/pull/7452) makes the style of all `List` docstrings that appear in the
  language reference consistent.

* [#7476](https://github.com/leanprover/lean4/pull/7476) adds missing docstrings for `IO` and related code and makes the
  style of the existing docstrings consistent.

* [#7492](https://github.com/leanprover/lean4/pull/7492) adds missing `Array` docstrings and makes their style
  consistent.

* [#7506](https://github.com/leanprover/lean4/pull/7506) adds missing `String` docstrings and makes the existing ones
  consistent in style.

* [#7523](https://github.com/leanprover/lean4/pull/7523) adds missing docstrings and makes docstring style consistent for
  `System` and `System.FilePath`.

* [#7528](https://github.com/leanprover/lean4/pull/7528) makes the docstrings for `Thunk` consistent with the style of
  the others.

* [#7534](https://github.com/leanprover/lean4/pull/7534) adds missing `Syntax`-related docstrings and makes the existing
  ones consistent in style with the others.

* [#7535](https://github.com/leanprover/lean4/pull/7535) revises the docstring for `funext`, making it more concise and
  adding a reference to the manual for more details.

* [#7548](https://github.com/leanprover/lean4/pull/7548) adds missing monad transformer docstrings and makes their style
  consistent.

* [#7552](https://github.com/leanprover/lean4/pull/7552) adds missing `Nat` docstrings and makes their style consistent.

* [#7564](https://github.com/leanprover/lean4/pull/7564) updates the docstrings for `ULift` and `PLift`, making their
  style consistent with the others.

* [#7568](https://github.com/leanprover/lean4/pull/7568) adds missing `Int` docstrings and makes the style of all of them
  consistent.

* [#7602](https://github.com/leanprover/lean4/pull/7602) adds missing docstrings for fixed-width integer operations and
  makes their style consistent.

* [#7607](https://github.com/leanprover/lean4/pull/7607) adds docstrings for `String.drop` and `String.dropRight`.

* [#7613](https://github.com/leanprover/lean4/pull/7613) adds a variety of docstrings for names that appear in the
  manual.

* [#7635](https://github.com/leanprover/lean4/pull/7635) adds missing docstrings for `Substring` and makes the style of
  `Substring` docstrings consistent.

* [#7642](https://github.com/leanprover/lean4/pull/7642) reviews the docstrings for `Float` and `Float32`, adding missing
  ones and making their format consistent.

* [#7645](https://github.com/leanprover/lean4/pull/7645) adds missing docstrings and makes docstring style consistent for
  `ForM`, `ForIn`, `ForIn'`, `ForInStep`, `IntCast`, and `NatCast`.

* [#7711](https://github.com/leanprover/lean4/pull/7711) adds the last few missing docstrings that appear in the manual.

* [#7713](https://github.com/leanprover/lean4/pull/7713) makes the BitVec docstrings match each other and the rest of the
  API in style.

## Server

* [#7178](https://github.com/leanprover/lean4/pull/7178) fixes a race condition in the language server that would
  sometimes cause it to drop requests and never respond to them when
  editing the header of a file. This in turn could cause semantic
  highlighting to stop functioning in VS Code, as VS Code would stop
  emitting requests when a prior request was dropped, and also cause the
  InfoView to become defective. It would also cause import auto-completion
  to feel a bit wonky, since these requests were sometimes dropped. This
  race condition has been present in the language server since its first
  version in 2020.

* [#7223](https://github.com/leanprover/lean4/pull/7223) implements parallel watchdog request processing so that requests
  that are processed by the watchdog cannot block the main thread of the
  watchdog anymore.

* [#7240](https://github.com/leanprover/lean4/pull/7240) adds a canonical syntax for linking to sections in the language
  reference along with formatting of examples in docstrings according to
  the docstring style guide.

* [#7343](https://github.com/leanprover/lean4/pull/7343) mitigates an issue where inserting an inlay hint in VS Code by
  double-clicking would insert the inlay hint at the wrong position right
  after an edit.

* [#7344](https://github.com/leanprover/lean4/pull/7344) combines the auto-implicit inlay hint tooltips into a single
  tooltip. This works around an issue in VS Code where VS Code fails to
  update hovers for tooltips in adjacent inlay hint parts when moving the
  mouse.

* [#7346](https://github.com/leanprover/lean4/pull/7346) fixes an issue where the language server would run into an inlay
  hint assertion violation when deleting a file that is still open in the
  language server.

* [#7366](https://github.com/leanprover/lean4/pull/7366) adds server-side support for dedicated 'unsolved goals' and
  'goals accomplished' diagnostics that will have special support in the
  Lean 4 VS Code extension. The special 'unsolved goals' diagnostic is
  adapted from the 'unsolved goals' error diagnostic, while the 'goals
  accomplished' diagnostic is issued when a `theorem` or `Prop`-typed
  `example` has no errors or `sorry`s. The Lean 4 VS Code extension
  companion PR is at leanprover/vscode-lean4#585.

* [#7376](https://github.com/leanprover/lean4/pull/7376) ensures `weak` options do not have to be repeated in both Lake
  `leanOptions` and `moreServerOptions`.

* [#7882](https://github.com/leanprover/lean4/pull/7882) fixes a regression where elaboration of a previous document
  version is not cancelled on changes to the document.

## Lake

* [#7185](https://github.com/leanprover/lean4/pull/7185) refactors Lake's build internals to enable the introduction of
  targets and facets beyond packages, modules, and libraries. Facets,
  build keys, build info, and CLI commands have been generalized to
  arbitrary target types.

* [#7393](https://github.com/leanprover/lean4/pull/7393) adds autocompletion support for Lake configuration fields in the
  Lean DSL at the indented whitespace after an existing field.
  Autocompletion in the absence of any fields is currently still not
  supported.

  **Breaking change:** The nonstandard braced configuration syntax now uses a semicolon `;` rather than a comma `,` as a separator. Indentation can still be used as an alternative to the separator.

* [#7399](https://github.com/leanprover/lean4/pull/7399) reverts the new builtin initializers, elaborators, and macros in
  Lake back to non-builtin.

* [#7504](https://github.com/leanprover/lean4/pull/7504) augments the Lake configuration data structures declarations
  (e.g., `PackageConfig`, `LeanLibConfig`) to produce additional metadata
  which is used to automatically generate the Lean & TOML encoders and
  decoders via metaprograms.

* [#7543](https://github.com/leanprover/lean4/pull/7543) unifies the configuration declarations of dynamic targets,
  external libraries, Lean libraries, and Lean executables into a single
  data type stored in a unified map within a package.

  **Breaking change:** Users can no longer define multiple targets with the same name but different kinds (e.g., a Lean executable and a Lean library both named `foo`). This should not effect most users as the Lake DSL already discouraged this.

* [#7576](https://github.com/leanprover/lean4/pull/7576) changes Lake to produce and use response files on Windows when
  building executables and libraries (static and shared). This is done to
  avoid potentially exceeding Windows command line length limits.

* [#7586](https://github.com/leanprover/lean4/pull/7586) changes the `static.export` facet for Lean libraries to produce
  thin static libraries.

* [#7608](https://github.com/leanprover/lean4/pull/7608) removes the use of the Lake plugin in the Lake build and in
  configuration files.

* [#7667](https://github.com/leanprover/lean4/pull/7667) changes Lake to log messages from a Lean configuration the same
  way it logs message from a Lean build. This, for instance, removes
  redundant severity captions.

* [#7703](https://github.com/leanprover/lean4/pull/7703) adds `input_file` and `input_dir` as new target types. It also
  adds the `needs` configuration option for Lean libraries and
  executables. This option generalizes `extraDepTargets` (which will be
  deprecated in the future), providing much richer support for declaring
  dependencies across package and target type boundaries.

* [#7716](https://github.com/leanprover/lean4/pull/7716) adds the `moreLinkObjs` and `moreLinkLibs` options for Lean
  packages, libraries, and executables. These serves as functional
  replacements for `extern_lib` and provided additional flexibility.

  **Breaking change:** `precompileModules` now only loads modules of the current library individually. Modules of other libraries are loaded together via that library's shared library.

* [#7732](https://github.com/leanprover/lean4/pull/7732) deprecates `extraDepTargets` and fixes a bug caused by the
  configuration refactor.

* [#7758](https://github.com/leanprover/lean4/pull/7758) removes the `-lstdcpp` extra link argument from the FFI example.
  It is not actually necessary.

* [#7763](https://github.com/leanprover/lean4/pull/7763) corrects build key fetches to produce jobs with the proper data
  kinds and fixes a failed coercion from key literals to targets.

## Other

* [#7326](https://github.com/leanprover/lean4/pull/7326) updates the release notes script to better indent PR
  descriptions.

* [#7453](https://github.com/leanprover/lean4/pull/7453) adds "(kernel)" to the message for the kernel-level application
  type mismatch error.

* [#7769](https://github.com/leanprover/lean4/pull/7769) fixes a number of bugs in the release automation scripts, adds a
  script to merge tags into remote `stable` branches, and makes the main
  `release_checklist.py` script give suggestions to call the
  `merge_remote.py` and `release_steps.py` scripts when needed.


````
