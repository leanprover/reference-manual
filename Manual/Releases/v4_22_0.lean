/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.22.0-rc2 (2025-07-01)" =>
%%%
tag := "release-v4.22.0"
file := "v4.22.0"
%%%

````markdown
For this release, 468 changes landed. In addition to the 185 feature additions and 85 fixes listed below there were 15 refactoring changes, 5 documentation improvements, 4 performance improvements, 0 improvements to the test suite and 174 other changes.

## Language

* [#6672](https://github.com/leanprover/lean4/pull/6672) filters out all declarations from `Lean.*`, `*.Tactic.*`, and
  `*.Linter.*` from the results of `exact?` and `rw?`.

* [#7395](https://github.com/leanprover/lean4/pull/7395) changes the `show t` tactic to match its documentation.
  Previously it was a synonym for `change t`, but now it finds the first
  goal that unifies with the term `t` and moves it to the front of the
  goal list.

* [#7639](https://github.com/leanprover/lean4/pull/7639) changes the generated `below` and `brecOn` implementations for
  reflexive inductive types to support motives in `Sort u` rather than
  `Type u`.

* [#8337](https://github.com/leanprover/lean4/pull/8337) adjusts the experimental module system to not export any private
  declarations from modules.

* [#8373](https://github.com/leanprover/lean4/pull/8373) enables transforming nondependent `let`s into `have`s in a
  number of contexts: the bodies of nonrecursive definitions, equation
  lemmas, smart unfolding definitions, and types of theorems. A motivation
  for this change is that when zeta reduction is disabled, `simp` can only
  effectively rewrite `have` expressions (e.g. `split` uses `simp` with
  zeta reduction disabled), and so we cache the nondependence calculations
  by transforming `let`s to `have`s. The transformation can be disabled
  using `set_option cleanup.letToHave false`.

* [#8387](https://github.com/leanprover/lean4/pull/8387) improves the error messages produced by `end` and prevents
  invalid `end` commands from closing scopes on failure.

* [#8419](https://github.com/leanprover/lean4/pull/8419) introduces an explicit `defeq` attribute to mark theorems that
  can be used by `dsimp`. The benefit of an explicit attribute over the
  prior logic of looking at the proof body is that we can reliably omit
  theorem bodies across module boundaries. It also helps with intra-file
  parallelism.

* [#8519](https://github.com/leanprover/lean4/pull/8519) makes the equational theorems of non-exposed defs private. If
  the author of a module chose not to expose the body of their function,
  then they likely don't want that implementation to leak through
  equational theorems. Helps with #8419.

* [#8543](https://github.com/leanprover/lean4/pull/8543) adds typeclasses for `grind` to embed types into `Int`, for
  cutsat. This allows, for example, treating `Fin n`, or Mathlib's `ℕ+` in
  a uniform and extensible way.

* [#8568](https://github.com/leanprover/lean4/pull/8568) modifies the `structure` elaborator to add local terminfo for
  structure fields and explicit parent projections, enabling "go to
  definition" when there are dependent fields.

* [#8574](https://github.com/leanprover/lean4/pull/8574) adds an additional diff mode to the error-message hint
  suggestion widget that displays diffs per word rather than per
  character.

* [#8596](https://github.com/leanprover/lean4/pull/8596) makes `guard_msgs.diff=true` the default. The main usage of
  `#guard_msgs` is for writing tests, and this makes staring at altered
  test outputs considerably less tiring.

* [#8609](https://github.com/leanprover/lean4/pull/8609) uses `grind` to shorten some proofs in the LRAT checker. The
  intention is not particularly to improve the quality or maintainability
  of these proofs (although hopefully this is a side effect), but just to
  give `grind` a work out.

* [#8619](https://github.com/leanprover/lean4/pull/8619) fixes an internalization (aka preprocessing) issue in `grind`
  when applying injectivity theorems.

* [#8621](https://github.com/leanprover/lean4/pull/8621) fixes a bug in the equality-resolution procedure used by
  `grind`.
  The procedure now performs a topological sort so that every simplified
  theorem declaration is emitted **before** any place where it is
  referenced.
  Previously, applying equality resolution to
  ```lean
  h : ∀ x, p x a → ∀ y, p y b → x ≠ y
  ```
  in the example
  ```lean
  example
    (p : Nat → Nat → Prop)
    (a b c : Nat)
    (h  : ∀ x, p x a → ∀ y, p y b → x ≠ y)
    (h₁ : p c a)
    (h₂ : p c b) :
    False := by
    grind
  ```
  caused `grind` to produce the incorrect term
  ```lean
  p ?y a → ∀ y, p y b → False
  ```
  The patch eliminates this error, and the following correct simplified
  theorem is generated
  ```lean
  ∀ y, p y a → p y b → False
  ```

* [#8622](https://github.com/leanprover/lean4/pull/8622) adds a test case / use case example for `grind`, setting up the
  very basics of `IndexMap`, modelled on Rust's
  [`indexmap`](https://docs.rs/indexmap/latest/indexmap/). It is not
  intended as a complete implementation: just enough to exercise `grind`.

* [#8625](https://github.com/leanprover/lean4/pull/8625) improves the diagnostic information produced by `grind` when it
  succeeds. We now include the list of case-splits performed, and the
  number of application per function symbol.

* [#8633](https://github.com/leanprover/lean4/pull/8633) implements case-split tracking in `grind`. The information is
  displayed when `grind` fails or diagnostic information is requested.
  Examples:

  - Failure

* [#8637](https://github.com/leanprover/lean4/pull/8637) adds background theorems for normalizing `IntModule` expressions
  using reflection.

* [#8638](https://github.com/leanprover/lean4/pull/8638) improves the diagnostic information produced by `grind`. It now
  sorts the equivalence classes by generation and then `Expr. lt`.

* [#8639](https://github.com/leanprover/lean4/pull/8639) completes the `ToInt` family of typeclasses which `grind` will
  use to embed types into the integers for `cutsat`. It contains instances
  for the usual concrete data types (`Fin`, `UIntX`, `IntX`, `BitVec`),
  and is extensible (e.g. for Mathlib's `PNat`).

* [#8641](https://github.com/leanprover/lean4/pull/8641) adds the `#print sig $ident` variant of the `#print` command,
  which omits the body. This is useful for testing meta-code, in the
  ```
  #guard_msgs (drop trace, all) in #print sig foo
  ```
  idiom. The benefit over `#check` is that it shows the declaration kind,
  reducibility attributes (and in the future more built-in attributes,
  like `@[defeq]` in #8419). (One downside is that `#check` shows unused
  function parameter names, e.g. in induction principles; this could
  probably be refined.)

* [#8645](https://github.com/leanprover/lean4/pull/8645) adds many helper theorems for the future `IntModule` linear
  arithmetic procedure in `grind`.
  It also adds helper theorems for normalizing input atoms and support for
  disequality in the new linear arithmetic procedure in `grind`.

* [#8650](https://github.com/leanprover/lean4/pull/8650) adds helper theorems for coefficient normalization and equality
  detection. This theorems are for the linear arithmetic procedure in
  `grind`.

* [#8662](https://github.com/leanprover/lean4/pull/8662) adds a `warn.sorry` option (default true) that logs the
  "declaration uses 'sorry'" warning when declarations contain `sorryAx`.
  When false, the warning is not logged.

* [#8670](https://github.com/leanprover/lean4/pull/8670) adds helper theorems that will be used to interface the
  `CommRing` module with the linarith procedure in `grind`.

* [#8671](https://github.com/leanprover/lean4/pull/8671) allow structures to have non-bracketed binders, making it
  consistent with `inductive`.

* [#8677](https://github.com/leanprover/lean4/pull/8677) adds the basic infrastructure for the linarith module in
  `grind`.

* [#8680](https://github.com/leanprover/lean4/pull/8680) adds the `reify?` and `denoteExpr` for the new linarith module
  in `grind`.

* [#8682](https://github.com/leanprover/lean4/pull/8682) uses the `CommRing` module to normalize linarith inequalities.

* [#8687](https://github.com/leanprover/lean4/pull/8687) implements the infrastructure for constructing proof terms in
  the linarith procedure in `grind`. It also adds the `ToExpr` instances
  for the reified objects.

* [#8689](https://github.com/leanprover/lean4/pull/8689) implements proof term generation for the `CommRing` and
  `linarith` interface. It also fixes the `CommRing` helper theorems.

* [#8690](https://github.com/leanprover/lean4/pull/8690) implements the main framework of the model search procedure for
  the linarith component in grind. It currently handles only inequalities.
  It can already solve simple goals such as
  ```lean
  example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b c : α)
      : a < b → b < c → c < a → False := by
    grind

* [#8693](https://github.com/leanprover/lean4/pull/8693) fixes the denotation functions used to interface the ring and
  linarith modules in grind.

* [#8694](https://github.com/leanprover/lean4/pull/8694) implements special support for `One.one` in linarith when the
  structure is a ordered ring. It also fixes bugs during initialization.

* [#8697](https://github.com/leanprover/lean4/pull/8697) implements support for inequalities in the `grind` linear
  arithmetic procedure and simplifies its design. Some examples that can
  already be solved:
  ```lean
  open Lean.Grind
  example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b c d : α)
      : a + d < c → b = a + (2:Int)*d → b - d > c → False := by
    grind

* [#8708](https://github.com/leanprover/lean4/pull/8708) fixes an internalization bug in the interface between linarith
  and ring modules in `grind`. The `CommRing` module may create new terms
  during normalization.

* [#8713](https://github.com/leanprover/lean4/pull/8713) fixes a bug in the commutative ring module used in `grind`. It
  was missing simplification opportunities.

* [#8715](https://github.com/leanprover/lean4/pull/8715) implements the basic infrastructure for processing disequalities
  in the `grind linarith` module. We still have to implement backtracking.

* [#8723](https://github.com/leanprover/lean4/pull/8723) implements a `finally` section following a (potentially empty)
  `where` block. `where ... finally` opens a tactic sequence block in
  which the goals are the unassigned metavariables from the definition
  body and its auxiliary definitions that arise from use of `let rec` and
  `where`.

* [#8730](https://github.com/leanprover/lean4/pull/8730) adds support for throwing named errors with associated error
  explanations. In particular, it adds elaborators for the syntax defined
  in #8649, which use the error-explanation infrastructure added in #8651.
  This includes completions, hovers, and jump-to-definition for error
  names.

* [#8733](https://github.com/leanprover/lean4/pull/8733) implements disequality splitting and non-chronological
  backtracking for the `grind` linarith procedure.
  ```lean
  example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b c d : α)
      : a ≤ b → a - c ≥ 0 + d → d ≤ 0 → d ≥ 0 → b = c → a ≠ b → False := by
    grind
  ```

* [#8751](https://github.com/leanprover/lean4/pull/8751) adds the `nondep` field of `Expr.letE` to the C++ data model.
  Previously this field has been unused, and in followup PRs the
  elaborator will use it to encode `have` expressions (non-dependent
  `let`s). The kernel does not verify that `nondep` is correctly applied
  during typechecking. The `letE` delaborator now prints `have`s when
  `nondep` is true, though `have` still elaborates as `letFun` for now.
  Breaking change: `Expr.updateLet!` is renamed to `Expr.updateLetE!`.

* [#8753](https://github.com/leanprover/lean4/pull/8753) fixes a bug in `simp` where it was not resetting the set of
  zeta-delta reduced let definitions between `simp` calls. It also fixes a
  bug where `simp` would report zeta-delta reduced let definitions that
  weren't given as simp arguments (these extraneous let definitions appear
  due to certain processes temporarily setting `zetaDelta := true`). This
  PR also modifies the metaprogramming interface for the zeta-delta
  tracking functions to be re-entrant and to prevent this kind of no-reset
  bug from occurring again. Closes #6655.

* [#8756](https://github.com/leanprover/lean4/pull/8756) implements counterexamples for grind linarith. Example:
  ```lean
  example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c d : α)
      : b ≥ 0 → c > b → d > b → a ≠ b + c → a > b + c → a < b + d →  False := by
    grind
  ```
  produces the counterexample
  ```
  a := 7/2
  b := 1
  c := 2
  d := 3
  ```

* [#8759](https://github.com/leanprover/lean4/pull/8759) implements model-based theory combination for grind linarith.
  Example:
  ```lean
  example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (f : α → α → α) (x y z : α)
      : z ≤ x → x ≤ 1 → z = 1 → f x y = 2 → f 1 y = 2 := by
    grind
  ```

* [#8763](https://github.com/leanprover/lean4/pull/8763) corrects the handling of explicit `monotonicity` proofs for
  mutual `partial_fixpoint` definitions.

* [#8773](https://github.com/leanprover/lean4/pull/8773) implements support for the heterogeneous `(k : Nat) * (a : R)`
  in ordered modules. Example:
  ```lean
  variable (R : Type u) [IntModule R] [LinearOrder R] [IntModule.IsOrdered R]

* [#8774](https://github.com/leanprover/lean4/pull/8774) adds an option for disabling the cutsat procedure in `grind`.
  The linarith module takes over linear integer/nat constraints. Example:

  ```lean
  set_option trace.grind.cutsat.assert true in -- cutsat should **not** process the following constraints
  example (x y z : Int) (h1 : 2 * x < 3 * y) (h2 : -4 * x + 2 * z < 0) : ¬ 12*y - 4* z < 0 := by
    grind -cutsat -- `linarith` module solves it
  ```

* [#8775](https://github.com/leanprover/lean4/pull/8775) adds a `grind` normalization theorem for `Int.negSucc`. Example:

  ```lean
  example (p : Int) (n : Nat) (hmp : Int.negSucc (n + 1) + 1 = p)
      (hnm : Int.negSucc (n + 1 + 1) + 1 = Int.negSucc (n + 1)) : p = Int.negSucc n := by
    grind
  ```

* [#8776](https://github.com/leanprover/lean4/pull/8776) ensures that user provided `natCast` application are properly
  internalized in the grind cutsat module.

* [#8777](https://github.com/leanprover/lean4/pull/8777) implements basic `Field` support in the commutative ring module
  in `grind`. It is just division by numerals for now. Examples:
  ```lean
  open Lean Grind

* [#8780](https://github.com/leanprover/lean4/pull/8780) makes Lean code generation respect the module name provided
  through `lean --setup`.

* [#8786](https://github.com/leanprover/lean4/pull/8786) improves the support for fields in `grind`. New supported
  examples:
  ```lean
  example [Field α] [IsCharP α 0] (x : α) : x ≠ 0 → (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by grind
  example [Field α] (a : α) : 2 * a ≠ 0 → 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind
  example [Field α] [IsCharP α 0] (a : α) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind
  example [Field α] [IsCharP α 0] (a b : α) : 2*b - a = a + b → 1 / a + 1 / (2 * a) = 3 / b := by grind
  example [Field α] [NoNatZeroDivisors α] (a : α) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind
  example [Field α] {x y z w : α} : x / y = z / w → y ≠ 0 → w ≠ 0 → x * w = z * y := by grind
  example [Field α] (a : α) : a = 0 → a ≠ 1 := by grind
  example [Field α] (a : α) : a = 0 → a ≠ 1 - a := by grind
  ```

* [#8789](https://github.com/leanprover/lean4/pull/8789) implements the Rabinowitsch transformation for `Field`
  disequalities in `grind`. For example, this transformation is necessary
  for solving:
  ```lean
  example [Field α] (a : α) : a^2 = 0 → a = 0 := by
    grind
  ```

* [#8791](https://github.com/leanprover/lean4/pull/8791) ensures the `grind linarith` module is activated for any type
  that implements only `IntModule`. That is, the type does not need to be
  a preorder anymore.

* [#8792](https://github.com/leanprover/lean4/pull/8792) makes the `clear_value` tactic preserve the order of variables
  in the local context. This is done by adding
  `Lean.MVarId.withRevertedFrom`, which reverts all local variables
  starting from a given variable, rather than only the ones that depend on
  it.

* [#8794](https://github.com/leanprover/lean4/pull/8794) adds a module `Lean.Util.CollectLooseBVars` with a function
  `Expr.collectLooseBVars` that collects the set of loose bound variables
  in an expression. That is, it computes the set of all `i` such that
  `e.hasLooseBVar i` is true.

* [#8795](https://github.com/leanprover/lean4/pull/8795) ensures that auxliary terms are not internalized by the ring and
  linarith modules.

* [#8796](https://github.com/leanprover/lean4/pull/8796) fixes `grind linarith` term internalization and support for
  `HSMul`.

* [#8798](https://github.com/leanprover/lean4/pull/8798) adds the following instance
  ```
  instance [Field α] [LinearOrder α] [Ring.IsOrdered α] : IsCharP α 0
  ```
  The goal is to ensure we do not perform unnecessary case-splits in our
  test suite.

* [#8804](https://github.com/leanprover/lean4/pull/8804) implements first-class support for nondependent let expressions
  in the elaborator; recall that a let expression `let x : t := v; b` is
  called *nondependent* if `fun x : t => b` typechecks, and the notation
  for a nondependent let expression is `have x := v; b`. Previously we
  encoded `have` using the `letFun` function, but now we make use of the
  `nondep` flag in the `Expr.letE` constructor for the encoding. This has
  been given full support throughout the metaprogramming interface and the
  elaborator. Key changes to the metaprogramming interface:
  - Local context `ldecl`s with `nondep := true` are generally treated as
  `cdecl`s. This is because in the body of a `have` expression the
  variable is opaque. Functions like `LocalDecl.isLet` by default return
  `false` for nondependent `ldecl`s. In the rare case where it is needed,
  they take an additional optional `allowNondep : Bool` flag (defaults to
  `false`) if the variable is being processed in a context where the value
  is relevant.
  - Functions such as `mkLetFVars` by default generalize nondependent let
  variables and create lambda expressions for them. The
  `generalizeNondepLet` flag (default true) can be set to false if `have`
  expressions should be produced instead. **Breaking change:** Uses of
  `letLambdaTelescope`/`mkLetFVars` need to use `generalizeNondepLet :=
  false`. See the next item.
  - There are now some mapping functions to make telescoping operations
  more convenient. See `mapLetTelescope` and `mapLambdaLetTelescope`.
  There is also `mapLetDecl` as a counterpart to `withLetDecl` for
  creating `let`/`have` expressions.
  - Important note about the `generalizeNondepLet` flag: it should only be
  used for variables in a local context that the metaprogram "owns". Since
  nondependent let variables are treated as constants in most cases, the
  `value` field might refer to variables that do not exist, if for example
  those variables were cleared or reverted. Using `mapLetDecl` is always
  fine.
  - The simplifier will cache its let dependence calculations in the
  nondep field of let expressions.
  - The `intro` tactic still produces *dependent* local variables. Given
  that the simplifier will transform lets into haves, it would be
  surprising if that would prevent `intro` from creating a local variable
  whose value cannot be used.

* [#8809](https://github.com/leanprover/lean4/pull/8809) introduces the basic theory of ordered modules over Nat (i.e.
  without subtraction), for `grind`. We'll solve problems here by
  embedding them in the `IntModule` envelope.

* [#8810](https://github.com/leanprover/lean4/pull/8810) implements equality elimination in `grind linarith`. The current
  implementation supports only `IntModule` and `IntModule` +
  `NoNatZeroDivisors`

* [#8813](https://github.com/leanprover/lean4/pull/8813) adds some basic lemmas about `grind` internal notions of
  modules.

* [#8815](https://github.com/leanprover/lean4/pull/8815) refactors the way simp arguments are elaborated: Instead of
  changing the `SimpTheorems` structure as we go, this elaborates each
  argument to a more declarative description of what it does, and then
  apply those. This enables more interesting checks of simp arguments that
  need to happen in the context of the eventually constructed simp context
  (the checks in #8688), or after simp has run (unused argument linter
  #8901).

* [#8828](https://github.com/leanprover/lean4/pull/8828) extends the experimental module system to support resolving
  private names imported (transitively) through `import all`.

* [#8835](https://github.com/leanprover/lean4/pull/8835) defines the embedding of a `CommSemiring` into its `CommRing`
  envelope, injective when the `CommSemiring` is cancellative. This will
  be used by `grind` to prove results in `Nat`.

* [#8836](https://github.com/leanprover/lean4/pull/8836) generalizes #8835 to the noncommutative case, allowing us to
  embed a `Lean.Grind.Semiring` into a `Lean.Grind.Ring`.

* [#8845](https://github.com/leanprover/lean4/pull/8845) implements the proof-by-reflection infrastructure for embedding
  semiring terms as ring ones.

* [#8847](https://github.com/leanprover/lean4/pull/8847) relaxes the assumptions for `Lean.Grind.IsCharP` from `Ring` to
  `Semiring`, and provides an alternative constructor for rings.

* [#8848](https://github.com/leanprover/lean4/pull/8848) generalizes the internal `grind` instance
  ```
  instance [Field α] [LinearOrder α] [Ring.IsOrdered α] : IsCharP α 0
  ```
  to
  ```
  instance [Ring α] [Preorder α] [Ring.IsOrdered α] : IsCharP α 0
  ```

* [#8855](https://github.com/leanprover/lean4/pull/8855) refactors `Lean.Grind.NatModule/IntModule/Ring.IsOrdered`.

* [#8859](https://github.com/leanprover/lean4/pull/8859) shows the equivalence between `Lean.Grind.NatModule.IsOrdered`
  and `Lean.Grind.IntModule.IsOrdered` over an `IntModule`.

* [#8865](https://github.com/leanprover/lean4/pull/8865) allows `simp` to recognize and warn about simp lemmas that are
  likely looping in the current simp set. It does so automatically
  whenever simplification fails with the dreaded “max recursion depth”
  error fails, but it can be made to do it always with `set_option
  linter.loopingSimpArgs true`. This check is not on by default because it
  is somewhat costly, and can warn about simp calls that still happen to
  work.

* [#8874](https://github.com/leanprover/lean4/pull/8874) skips attempting to compute a module name from the file name and
  root directory (i.e., `lean -R`) if a name is already provided via `lean
  --setup`.

* [#8880](https://github.com/leanprover/lean4/pull/8880) makes `simp` consult its own cache more often, to avoid
  replicating work.

* [#8882](https://github.com/leanprover/lean4/pull/8882) adds `@[expose]` annotations to terms that appear in `grind`
  proof certificates, so `grind` can be used in the module system. It's
  possible/likely that I haven't identified all of them yet.

* [#8890](https://github.com/leanprover/lean4/pull/8890) adds doc-strings to the `Lean.Grind` algebra typeclasses, as
  these will appear in the reference manual explaining how to extend
  `grind` algebra solvers to new types. Also removes some redundant
  fields.

* [#8892](https://github.com/leanprover/lean4/pull/8892) corrects the pretty printing of `grind` modifiers. Previously
  `@[grind →]` was being pretty printed as `@[grind→ ]` (Space on the
  right of the symbol, rather than left.) This fixes the pretty printing
  of attributes, and preserves the presence of spaces after the symbol in
  the output of `grind?`.

* [#8893](https://github.com/leanprover/lean4/pull/8893) fixes a bug in the `dvd` propagation function in cutsat.

* [#8901](https://github.com/leanprover/lean4/pull/8901) adds a linter (`linter.unusedSimpArgs`) that complains when a
  simp argument (`simp [foo]`) is unused. It should do the right thing if
  the `simp` invocation is run multiple times, e.g. inside `all_goals`. It
  does not trigger when the `simp` call is inside a macro. The linter
  message contains a clickable hint to remove the simp argument.

* [#8903](https://github.com/leanprover/lean4/pull/8903) make sure that the local instance cache calculation applies more
  reductions. In #2199 there was an issue where metavariables could
  prevent local variables from being considered as local instances. We use
  a slightly different approach that ensures that, for example, `let`s at
  the ends of telescopes do not cause similar problems. These reductions
  were already being calculated, so this does not require any additional
  work to be done.

* [#8909](https://github.com/leanprover/lean4/pull/8909) refactors the `NoNatZeroDivisors` to make sure it will work with
  the new `Semiring` support.

* [#8910](https://github.com/leanprover/lean4/pull/8910) adds the `NoNatZeroDivisors` instance for `OfSemiring.Q α`

* [#8913](https://github.com/leanprover/lean4/pull/8913) cleans up `grind`'s internal order typeclasses, removing
  unnecessary duplication.

* [#8914](https://github.com/leanprover/lean4/pull/8914) modifies `let` and `have` term syntaxes to be consistent with
  each other. Adds configuration options; for example, `have` is
  equivalent to `let +nondep`, for *nondependent* lets. Other options
  include `+usedOnly` (for `let_tmp`), `+zeta` (for `letI`/`haveI`), and
  `+postponeValue` (for `let_delayed)`. There is also `let (eq := h) x :=
  v; b` for introducing `h : x = v` when elaborating `b`. The `eq` option
  works for pattern matching as well, for example `let (eq := h) (x, y) :=
  p; b`.

* [#8918](https://github.com/leanprover/lean4/pull/8918) fixes the `guard_msgs.diff` default behavior so that the default
  specified in the option definition is actually used everywhere.

* [#8921](https://github.com/leanprover/lean4/pull/8921) implements support for (commutative) semirings in `grind`. It
  uses the Grothendieck completion to construct a (commutative) ring
  `Lean.Grind.Ring.OfSemiring.Q α` from a (commutative) semiring `α`. This
  construction is mostly useful for semirings that implement
  `AddRightCancel α`. Otherwise, the function `toQ` is not injective.
  Examples:
  ```lean
  example (x y : Nat) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
    grind

* [#8935](https://github.com/leanprover/lean4/pull/8935) adds the `+generalize` option to the `let` and `have` syntaxes.
  For example, `have +generalize n := a + b; body` replaces all instances
  of `a + b` in the expected type with `n` when elaborating `body`. This
  can be likened to a term version of the `generalize` tactic. One can
  combine this with `eq` in `have +generalize (eq := h) n := a + b; body`
  as an analogue of `generalize h : n = a + b`.

* [#8937](https://github.com/leanprover/lean4/pull/8937) changes the output universe of the generated `below`
  implementation for non-reflexive inductive types to match the
  implementation for reflexive inductive types in #7639.

* [#8940](https://github.com/leanprover/lean4/pull/8940) introduces antitonicity lemmas that support the elaboration of
  mixed inductive-coinductive predicates defined using the
  `least_fixpoint` / `greatest_fixpoint` constructs.

* [#8943](https://github.com/leanprover/lean4/pull/8943) adds helper theorems for normalizing semirings that do not
  implement `AddRightCancel`.

* [#8953](https://github.com/leanprover/lean4/pull/8953) implements support for normalization for commutative semirings
  that do not implement `AddRightCancel`. Examples:
  ```lean
  variable (R : Type u) [CommSemiring R]

* [#8954](https://github.com/leanprover/lean4/pull/8954) adds a procedure that efficiently transforms `let` expressions
  into `have` expressions (`Meta.letToHave`). This is exposed as the
  `let_to_have` tactic.

* [#8955](https://github.com/leanprover/lean4/pull/8955) fixes `Lean.MVarId.deltaLocalDecl`, which previously replaced
  the local definition with the target.

* [#8957](https://github.com/leanprover/lean4/pull/8957) adds configuration options to the `let`/`have` tactic syntaxes.
  For example, `let (eq := h) x := v` adds `h : x = v` to the local
  context. The configuration options are the same as those for the
  `let`/`have` term syntaxes.

* [#8958](https://github.com/leanprover/lean4/pull/8958) improves the case splitting strategy used in `grind`, and
  ensures `grind` also considers simple `match`-conditions for
  case-splitting. Example:

  ```lean
  example (x y : Nat)
      : 0 < match x, y with
            | 0, 0   => 1
            | _, _ => x + y := by -- x or y must be greater than 0
    grind
  ```

* [#8959](https://github.com/leanprover/lean4/pull/8959) add instances showing that the Grothendieck (i.e. additive)
  envelope of a semiring is an ordered ring if the original semiring is
  ordered (and satisfies ExistsAddOfLE), and in this case the embedding is
  monotone.

* [#8963](https://github.com/leanprover/lean4/pull/8963) embeds a NatModule into its IntModule completion, which is
  injective when we have AddLeftCancel, and monotone when the modules are
  ordered. Also adds some (failing) grind test cases that can be verified
  once `grind` uses this embedding.

* [#8964](https://github.com/leanprover/lean4/pull/8964) adds `@[expose]` attributes to proof terms constructed by
  `grind` that need to be evaluated in the kernel.

* [#8965](https://github.com/leanprover/lean4/pull/8965) revises @[grind] annotations on Nat bitwise operations.

* [#8968](https://github.com/leanprover/lean4/pull/8968) adds the following features to `simp`:
  - A routine for simplifying `have` telescopes in a way that avoids
  quadratic complexity arising from locally nameless expression
  representations, like what #6220 did for `letFun` telescopes.
  Furthermore, simp converts `letFun`s into `have`s (nondependent lets),
  and we remove the #6220 routine since we are moving away from `letFun`
  encodings of nondependent lets.
  - A `+letToHave` configuration option (enabled by default) that converts
  lets into haves when possible, when `-zeta` is set. Previously Lean
  would need to do a full typecheck of the bodies of `let`s, but the
  `letToHave` procedure can skip checking some subexpressions, and it
  modifies the `let`s in an entire expression at once rather than one at a
  time.
  - A `+zetaHave` configuration option, to turn off zeta reduction of
  `have`s specifically. The motivation is that dependent `let`s can only
  be dsimped by let, so zeta reducing just the dependent lets is a
  reasonable way to make progress. The `+zetaHave` option is also added to
  the meta configuration.
  - When `simp` is zeta reducing, it now uses an algorithm that avoids
  complexity quadratic in the depth of the let telescope.
  - Additionally, the zeta reduction routines in `simp`, `whnf`, and
  `isDefEq` now all are consistent with how they apply the `zeta`,
  `zetaHave`, and `zetaUnused` configurations.

* [#8971](https://github.com/leanprover/lean4/pull/8971) fixes `linter.simpUnusedSimpArgs` to check the syntax kind, to
  not fire on `simp` calls behind macros. Fixes #8969

* [#8973](https://github.com/leanprover/lean4/pull/8973) refactors the juggling of universes in the linear
  `noConfusionType` construction: Instead of using `PUnit.{…} → ` in the
  to get the branches of `withCtorType` to the same universe level, we use
  `PULift`.

* [#8978](https://github.com/leanprover/lean4/pull/8978) updates the `solveMonoStep` function used in the `monotonicity`
  tactic to check for definitional equality between the current goal and
  the monotonicity proof obtained from a recursive call. This ensures
  soundness by preventing incorrect applications when
  `Lean.Order.PartialOrder` instances differ—an issue that can arise with
  `mutual` blocks defined using the `partial_fixpoint` keyword, where
  different `Lean.Order.CCPO` structures may be involved.

* [#8980](https://github.com/leanprover/lean4/pull/8980) improves the consistency of error message formatting by
  rendering addenda of several existing error messages as labeled notes
  and hints.

* [#8983](https://github.com/leanprover/lean4/pull/8983) fixes a bug in congruence proof generation in `grind` for
  over-applied functions.

* [#8986](https://github.com/leanprover/lean4/pull/8986) improves the error messages produced by invalid projections and
  field notation. It also adds a hint to the "function expected" error
  message noting the argument to which the term is being applied, which
  can be helpful for debugging spurious "function expected" messages
  actually caused by syntax errors.

* [#8991](https://github.com/leanprover/lean4/pull/8991) adds some missing `ToInt.X` typeclass instances for `grind`.

* [#8995](https://github.com/leanprover/lean4/pull/8995) introduces a Hoare logic for monadic programs in
  `Std.Do.Triple`, and assorted tactics:

  *  `mspec` for applying Hoare triple specifications
  * `mvcgen` to turn a Hoare triple proof obligation `⦃P⦄ prog ⦃Q⦄` into
  pure verification conditoins (i.e., without any traces of Hoare triples
  or weakest preconditions reminiscent of `prog`). The resulting
  verification conditions in the stateful logic of `Std.Do.SPred` can be
  discharged manually with the tactics coming with its custom proof mode
  or with automation such as `simp` and `grind`.

* [#8996](https://github.com/leanprover/lean4/pull/8996) provides the remaining instances for the `Lean.Grind.ToInt`
  typeclasses.

* [#9004](https://github.com/leanprover/lean4/pull/9004) ensures that type-class synthesis failure errors in interpolated
  strings are displayed at the interpolant at which they occurred.

* [#9005](https://github.com/leanprover/lean4/pull/9005) changes the definition of `Lean.Grind.ToInt.OfNat`, introducing
  a `wrap` on the right-hand-side.

* [#9008](https://github.com/leanprover/lean4/pull/9008) implements the basic infrastructure for the generic `ToInt`
  support in `cutsat`.

* [#9022](https://github.com/leanprover/lean4/pull/9022) completes the generic `toInt` infrastructure for embedding terms
  implementing the `ToInt` type classes into `Int`.

* [#9026](https://github.com/leanprover/lean4/pull/9026) implements support for (non strict) `ToInt` inequalities in
  `grind cutsat`. `grind cutsat` can solve simple problems such as:
  ```lean
  example (a b c : Fin 11) : a ≤ b → b ≤ c → a ≤ c := by
    grind

* [#9030](https://github.com/leanprover/lean4/pull/9030) fixes a couple of bootstrapping-related hiccups in the newly
  added `Std.Do` module. More precisely,

* [#9035](https://github.com/leanprover/lean4/pull/9035) extends the list of acceptable characters to all the french ones
  as well as some others,
  by adding characters from the Latin-1-Supplement add Latin-Extended-A
  unicode block.

* [#9038](https://github.com/leanprover/lean4/pull/9038) adds test cases for the VC generator and implements a few small
  and tedious fixes to ensure they pass.

* [#9041](https://github.com/leanprover/lean4/pull/9041) makes `mspec` detect more viable assignments by `rfl` instead of
  generating a VC.

* [#9044](https://github.com/leanprover/lean4/pull/9044) adjusts the experimental module system to make `private` the
  default visibility modifier in `module`s, introducing `public` as a new
  modifier instead. `public section` can be used to revert the default for
  an entire section, though this is more intended to ease gradual adoption
  of the new semantics such as in `Init` (and soon `Std`) where they
  should be replaced by a future decl-by-decl re-review of visibilities.

* [#9045](https://github.com/leanprover/lean4/pull/9045) fixes a type error in `mvcgen` and makes it turn fewer natural
  goals into synthetic opaque ones, so that tactics such as `trivial` may
  instantiate them more easily.

* [#9048](https://github.com/leanprover/lean4/pull/9048) implements support for strict inequalities in the `ToInt`
  adapter used in `grind cutsat`. Example:
  ```lean
  example (a b c : Fin 11) : c ≤ 9 → a ≤ b → b < c → a < c + 1 := by
    grind
  ```

* [#9050](https://github.com/leanprover/lean4/pull/9050) ensures the `ToInt` bounds are asserted for every `toInt a`
  application internalized in `grind cutsat`.

* [#9051](https://github.com/leanprover/lean4/pull/9051) implements support for equalities and disequalities in `grind
  cutsat`. We still have to improve the encoding. Examples:
  ```lean
  example (a b c : Fin 11) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
    grind

* [#9057](https://github.com/leanprover/lean4/pull/9057) introduces a simple variable-reordering heuristic for `cutsat`.
  It is needed by the `ToInt` adapter to support finite types such as
  `UInt64`. The current encoding into `Int` produces large coefficients,
  which can enlarge the search space when an unfavorable variable order is
  used. Example:
  ```lean
  example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
    grind
  ```

* [#9059](https://github.com/leanprover/lean4/pull/9059) adds helper theorems for normalizing coefficients in rings of
  unknown characteristic.

* [#9062](https://github.com/leanprover/lean4/pull/9062) implements support for equations `<num> = 0` in rings and fields
  of unknown characteristic. Examples:
  ```lean
  example [Field α] (a : α) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind

* [#9065](https://github.com/leanprover/lean4/pull/9065) improves the counterexamples produced by the `cutsat` procedure
  in `grind` when using the `ToInt` gadget.

* [#9067](https://github.com/leanprover/lean4/pull/9067) adds a docstring for the `grind` tactic.

* [#9069](https://github.com/leanprover/lean4/pull/9069) implements support for the type class `LawfulEqCmp`. Examples:
  ```lean
  example (a b c : Vector (List Nat) n)
      : b = c → a.compareLex (List.compareLex compare) b = o → o = .eq → a = c := by
    grind

* [#9073](https://github.com/leanprover/lean4/pull/9073) copies #9069 to handle `ReflCmp` the same way; we need to call
  this in propagateUp rather than propagateDown.

* [#9074](https://github.com/leanprover/lean4/pull/9074) uses the commutative ring module to normalize nonlinear
  polynomials in `grind cutsat`. Examples:
  ```lean
  example (a b : Nat) (h₁ : a + 1 ≠ a * b * a) (h₂ : a * a * b ≤ a + 1) : b * a^2 < a + 1 := by
    grind

* [#9076](https://github.com/leanprover/lean4/pull/9076) adds an unexpander for `OfSemiring.toQ`. This an auxiliary
  function used by the `ring` module in `grind`, but we want to reduce the
  clutter in the diagnostic information produced by `grind`. Example:
  ```
  example [CommSemiring α] [AddRightCancel α] [IsCharP α 0] (x y : α)
      : x^2*y = 1 → x*y^2 = y → x + y = 2 → False := by
    grind
  ```
  produces
  ```
    [ring] Ring `Ring.OfSemiring.Q α` ▼
      [basis] Basis ▼
        [_] ↑x + ↑y + -2 = 0
        [_] ↑y + -1 = 0
  ```

* [#9086](https://github.com/leanprover/lean4/pull/9086) deprecates `let_fun` syntax in favor of `have` and removes
  `letFun` support from WHNF and `simp`.

* [#9087](https://github.com/leanprover/lean4/pull/9087) removes the `irreducible` attribute from `letFun`, which is one
  step toward removing special `letFun` support; part of #9086.

````
````markdown

## Library

* [#8003](https://github.com/leanprover/lean4/pull/8003) adds a new monadic interface for `Async` operations.

* [#8072](https://github.com/leanprover/lean4/pull/8072) adds DNS functions to the standard library

* [#8109](https://github.com/leanprover/lean4/pull/8109) adds system information functions to the standard library

* [#8178](https://github.com/leanprover/lean4/pull/8178) provides a compact formula for the MSB of the sdiv. Most of the
  work in the PR involves handling the corner cases of division
  overflowing (e.g. `intMin / -1 = intMin`)

* [#8203](https://github.com/leanprover/lean4/pull/8203) adds trichotomy lemmas for unsigned and signed comparisons,
  stating that only one of three cases may happen: either `x < y`, `x =
  y`, or `x > y` (for both signed and unsigned comparsions). We use
  explicit arguments so that users can write `rcases slt_trichotomy x y
  with hlt | heq | hgt`.

* [#8205](https://github.com/leanprover/lean4/pull/8205) adds a simp lemma that simplifies T-division where the numerator
  is a `Nat` into an E-division:


  ```lean
  @[simp] theorem ofNat_tdiv_eq_ediv {a : Nat} {b : Int} : (a : Int).tdiv b = a / b :=
     tdiv_eq_ediv_of_nonneg (by simp)
  ```

* [#8210](https://github.com/leanprover/lean4/pull/8210) adds an equivalence relation to tree maps akin to the existing
  one for hash maps. In order to get many congruence lemmas to eventually
  use for defining functions on extensional tree maps, almost all of the
  remaining tree map functions have also been given lemmas to relate them
  to list functions, although these aren't currently used to prove lemmas
  other than congruence lemmas.

* [#8253](https://github.com/leanprover/lean4/pull/8253) adds `toInt_smod` and auxilliary lemmas necessary for its proof
  (`msb_intMin_umod_neg_of_msb_true`,
  `msb_neg_umod_neg_of_msb_true_of_msb_true`, `toInt_dvd_toInt_iff`,
  `toInt_dvd_toInt_iff_of_msb_true_msb_false`,
  `toInt_dvd_toInt_iff_of_msb_false_msb_true`,
  `neg_toInt_neg_umod_eq_of_msb_true_msb_true`, `toNat_pos_of_ne_zero`,
  `toInt_umod_neg_add`, `toInt_sub_neg_umod` and
  `BitVec.[lt_of_msb_false_of_msb_true, msb_umod_of_msb_false_of_ne_zero`,
  `neg_toInt_neg]`)

* [#8420](https://github.com/leanprover/lean4/pull/8420) provides the iterator combinator `drop` that transforms any
  iterator into one that drops the first `n` elements.

* [#8534](https://github.com/leanprover/lean4/pull/8534) fixes `IO.FS.realPath` on windows to take symbolic links into
  account.

* [#8545](https://github.com/leanprover/lean4/pull/8545) provides the means to reason about "equivalent" iterators.
  Simply speaking, two iterators are equivalent if they behave the same as
  long as consumers do not introspect their states.

* [#8546](https://github.com/leanprover/lean4/pull/8546) adds a new `BitVec.clz` operation and a corresponding `clz`
  circuit to `bv_decide`, allowing to bitblast the count leading zeroes
  operation. The AIG circuit is linear in the number of bits of the
  original expression, making the bitblasting convenient wrt. rewriting.
  `clz` is common in numerous compiler intrinsics (see
  [here](https://clang.llvm.org/docs/LanguageExtensions.html#intrinsics-support-within-constant-expressions))
  and architectures (see
  [here](https://en.wikipedia.org/wiki/Find_first_set)).

* [#8573](https://github.com/leanprover/lean4/pull/8573) avoids the likely unexpected behavior of `removeDirAll` to
  delete through symlinks and adds the new function
  `IO.FS.symlinkMetadata`.

* [#8585](https://github.com/leanprover/lean4/pull/8585) makes the lemma `BitVec.extractLsb'_append_eq_ite` more usable
  by using the "simple case" more often, and uses this simplification to
  make `BitVec.extractLsb'_append_eq_of_add_lt` stronger, renaming it to
  `BitVec.extractLsb'_append_eq_of_add_le`.

* [#8587](https://github.com/leanprover/lean4/pull/8587) adjusts the grind annotation on
  `Std.HashMap.map_fst_toList_eq_keys` and variants, so `grind` can reason
  bidirectionally between `m.keys` and `m.toList`.

* [#8590](https://github.com/leanprover/lean4/pull/8590) adds `@[grind]` to `getElem?_pos` and variants.

* [#8615](https://github.com/leanprover/lean4/pull/8615) provides a special empty iterator type. Although its behavior
  can be emulated with a list iterator (for example), having a special
  type has the advantage of being easier to optimize for the compiler.

* [#8620](https://github.com/leanprover/lean4/pull/8620) removes the `NatCast (Fin n)` global instance (both the direct
  instance, and the indirect one via `Lean.Grind.Semiring`), as that
  instance causes causes `x < n` (for `x : Fin k`, `n : Nat`) to be
  elaborated as `x < ↑n` rather than `↑x < n`, which is undesirable. Note
  however that in Mathlib this happens anyway!

* [#8629](https://github.com/leanprover/lean4/pull/8629) replaces special, more optimized `IteratorLoop` instances, for
  which no lawfulness proof has been made, with the verified default
  implementation. The specialization of the loop/collect implementations
  is low priority, but having lawfulness instances for all iterators is
  important for verification.

* [#8631](https://github.com/leanprover/lean4/pull/8631) generalizes `Std.Sat.AIG. relabel(Nat)_unsat_iff` to allow the
  AIG type to be empty. We generalize the proof, by showing that in the
  case when `α` is empty, the environment doesn't matter, since all
  environments `α → Bool` are isomorphic.

* [#8640](https://github.com/leanprover/lean4/pull/8640) adds `BitVec.setWidth'_eq` to `bv_normalize` such that
  `bv_decide` can reduce it and solve lemmas involving `setWidth'_eq`

* [#8669](https://github.com/leanprover/lean4/pull/8669) makes `unsafeBaseIO` `noinline`. The new compiler is better at
  optimizing `Result`-like types, which can cause the final operation in
  an `unsafeBaseIO` block to be dropped, since `unsafeBaseIO` is
  discarding the state.

* [#8678](https://github.com/leanprover/lean4/pull/8678) makes the LHS of `isSome_finIdxOf?` and `isNone_finIdxOf?` more
  general.

* [#8703](https://github.com/leanprover/lean4/pull/8703) corrects the `IteratorLoop` instance in `DropWhile`, which
  previously triggered for arbitrary iterator types.

* [#8719](https://github.com/leanprover/lean4/pull/8719) adds grind annotations for
  List/Array/Vector.eraseP/erase/eraseIdx. It also adds some missing
  lemmas.

* [#8721](https://github.com/leanprover/lean4/pull/8721) adds the types `Std.ExtDTreeMap`, `Std.ExtTreeMap` and
  `Std.ExtTreeSet` of extensional tree maps and sets. These are very
  similar in construction to the existing extensional hash maps with one
  exception: extensional tree maps and sets provide all functions from
  regular tree maps and sets. This is possible because in contrast to hash
  maps, tree maps are always ordered.

* [#8734](https://github.com/leanprover/lean4/pull/8734) adds the missing instance
  ```
  instance decidableExistsFin (P : Fin n → Prop) [DecidablePred P] : Decidable (∃ i, P i)
  ```

* [#8740](https://github.com/leanprover/lean4/pull/8740) introduces associativity rules and preservation of `(umul, smul,
  uadd, sadd)Overflow`flags.

* [#8741](https://github.com/leanprover/lean4/pull/8741) adds annotations for
  `List/Array/Vector.find?/findSome?/idxOf?/findIdx?`.

* [#8742](https://github.com/leanprover/lean4/pull/8742) fixes a bug where the single-quote character `Char.ofNat 39`
  would delaborate as `'''`, which causes a parse error if pasted back in
  to the source code.

* [#8745](https://github.com/leanprover/lean4/pull/8745) adds a logic of stateful predicates `SPred` to `Std.Do` in order
  to support reasoning about monadic programs. It comes with a dedicated
  proof mode the tactics of which are accessible by importing
  `Std.Tactic.Do`.

* [#8747](https://github.com/leanprover/lean4/pull/8747) adds grind annotations for \`List/Array/Vector.finRange\`
  theorems.

* [#8748](https://github.com/leanprover/lean4/pull/8748) adds grind annotations for `Array/Vector.mapIdx` and `mapFinIdx`
  theorems.

* [#8749](https://github.com/leanprover/lean4/pull/8749) adds grind annotations for `List/Array/Vector.ofFn` theorems and
  additional `List.Impl` find operations.

* [#8750](https://github.com/leanprover/lean4/pull/8750) adds grind annotations for the
  `List/Array/Vector.zipWith/zipWithAll/unzip` functions.

* [#8765](https://github.com/leanprover/lean4/pull/8765) adds grind annotations for `List.Perm`; involves a revision of
  grind annotations for `List.countP/count` as well.

* [#8768](https://github.com/leanprover/lean4/pull/8768) introduces a `ForIn'` instance and a `size` function for
  iterators in a minimal fashion. The `ForIn'` instance is not marked as
  an instance because it is unclear which `Membership` relation is
  sufficiently useful. The `ForIn'` instance existing as a `def` and
  inducing the `ForIn` instance, it becomes possible to provide more
  specialized `ForIn'` instances, with nice `Membership` relations, for
  various types of iterators. The `size` function has no lemmas yet.

* [#8784](https://github.com/leanprover/lean4/pull/8784) introduces ranges that are polymorphic, in contrast to the
  existing `Std.Range` which only supports natural numbers.

* [#8805](https://github.com/leanprover/lean4/pull/8805) continues adding `grind` annotations for `List/Array/Vector`
  lemmas.

* [#8808](https://github.com/leanprover/lean4/pull/8808) adds the missing `le_of_add_left_le {n m k : Nat} (h : k + n ≤
  m) : n ≤ m` and `le_add_left_of_le {n m k : Nat} (h : n ≤ m) : n ≤ k +
  m`.

* [#8811](https://github.com/leanprover/lean4/pull/8811) adds theorems `BitVec.(toNat, toInt,
  toFin)_shiftLeftZeroExtend`, completing the API for
  `BitVec.shiftLeftZeroExtend`.

* [#8826](https://github.com/leanprover/lean4/pull/8826) corrects the definition of `Lean.Grind.NatModule`, which wasn't
  previously useful.

* [#8827](https://github.com/leanprover/lean4/pull/8827) renames `BitVec.getLsb'` to `BitVec.getLsb`, now that older
  deprecated definition occupying that name has been removed. (Similarly
  for `BitVec.getMsb'`.)

* [#8829](https://github.com/leanprover/lean4/pull/8829) avoids importing all of `BitVec.Lemmas` and `BitVec.BitBlast`
  into `UInt.Lemmas`. (They are still imported into `SInt.Lemmas`; this
  seems much harder to avoid.)

* [#8830](https://github.com/leanprover/lean4/pull/8830) rearranges files under `Init.Grind`, moving out instances for
  concrete algebraic types in `Init.GrindInstances`.

* [#8849](https://github.com/leanprover/lean4/pull/8849) adds `grind` annotations for `Sum`.

* [#8850](https://github.com/leanprover/lean4/pull/8850) adds `grind` annotations for `Prod`.

* [#8851](https://github.com/leanprover/lean4/pull/8851) adds grind annotations for `Function.curry`/`uncurry`.

* [#8852](https://github.com/leanprover/lean4/pull/8852) adds grind annotations for `Nat.testBit` and bitwise operations
  on `Nat`.

* [#8853](https://github.com/leanprover/lean4/pull/8853) adds `grind` annotations relating `Nat.fold/foldRev/any/all` and
  `Fin.foldl/foldr/foldlM/foldrM` to the corresponding operations on
  `List.finRange`.

* [#8877](https://github.com/leanprover/lean4/pull/8877) adds grind annotations for
  `List/Array/Vector.attach/attachWith/pmap`.

* [#8878](https://github.com/leanprover/lean4/pull/8878) adds grind annotations for List/Array/Vector monadic functions.

* [#8886](https://github.com/leanprover/lean4/pull/8886) adds `IO.FS.Stream.readToEnd` which parallels
  `IO.FS.Handle.readToEnd` along with its upstream definitions (i.e.,
  `readBinToEndInto` and `readBinToEnd`). It also removes an unnecessary
  `partial` from `IO.FS.Handle.readBinToEnd`.

* [#8887](https://github.com/leanprover/lean4/pull/8887) generalizes `IO.FS.lines` with `IO.FS.Handle.lines` and adds the
  parallel `IO.FS.Stream.lines` for streams.

* [#8897](https://github.com/leanprover/lean4/pull/8897) simplifies some `simp` calls.

* [#8905](https://github.com/leanprover/lean4/pull/8905) uses the linter from
  https://github.com/leanprover/lean4/pull/8901 to clean up simp
  arguments.

* [#8920](https://github.com/leanprover/lean4/pull/8920) uses the linter from #8901 to clean up more simp arguments,
  completing #8905.

* [#8928](https://github.com/leanprover/lean4/pull/8928) adds a logic of stateful predicates SPred to Std.Do in order to
  support reasoning about monadic programs. It comes with a dedicated
  proof mode the tactics of which are accessible by importing
  Std.Tactic.Do.

* [#8941](https://github.com/leanprover/lean4/pull/8941) adds `BitVec.(getElem, getLsbD, getMsbD)_(smod, sdiv, srem)`
  theorems to complete the API for `sdiv`, `srem`, `smod`. Even though the
  rhs is not particularly succint (it's hard to find a meaning for what it
  means to have "the n-th bit of the result of a signed division/modulo
  operation"), these lemmas prevent the need to `unfold` of operations.

* [#8947](https://github.com/leanprover/lean4/pull/8947) introduces polymorphic slices in their most basic form. They
  come with a notation similar to the new range notation. `Subarray` is
  now also a slice and can produce an iterator now. It is intended to
  migrate more operations of `Subarray` to the `Slice` wrapper type to
  make them available for slices of other types, too.

* [#8950](https://github.com/leanprover/lean4/pull/8950) adds `BitVec.toFin_(sdiv, smod, srem)` and `BitVec.toNat_srem`.
  The strategy for the `rhs` of the `toFin_*` lemmas is to consider what
  the corresponding `toNat_*` theorems do and push the `toFin` closerto
  the operands. For the `rhs` of `BitVec.toNat_srem` I used the same
  strategy as `BitVec.toNat_smod`.

* [#8967](https://github.com/leanprover/lean4/pull/8967) both adds initial `@[grind]` annotations for `BitVec`, and uses
  `grind` to remove many proofs from `BitVec/Lemmas`.

* [#8974](https://github.com/leanprover/lean4/pull/8974) adds `BitVec.msb_(smod, srem)`.

* [#8977](https://github.com/leanprover/lean4/pull/8977) adds a generic `MonadLiftT Id m` instance. We do not implement a
  `MonadLift Id m` instance because it would slow down instance resolution
  and because it would create more non-canonical instances. This change
  makes it possible to iterate over a pure iterator, such as `[1, 2,
  3].iter`, in arbitrary monads.

* [#8992](https://github.com/leanprover/lean4/pull/8992) adds `PULift`, a more general form of `ULift` and `PLift` that
  subsumes both.

* [#8995](https://github.com/leanprover/lean4/pull/8995) introduces a Hoare logic for monadic programs in
  `Std.Do.Triple`, and assorted tactics:

  *  `mspec` for applying Hoare triple specifications
  * `mvcgen` to turn a Hoare triple proof obligation `⦃P⦄ prog ⦃Q⦄` into
  pure verification conditoins (i.e., without any traces of Hoare triples
  or weakest preconditions reminiscent of `prog`). The resulting
  verification conditions in the stateful logic of `Std.Do.SPred` can be
  discharged manually with the tactics coming with its custom proof mode
  or with automation such as `simp` and `grind`.

* [#9027](https://github.com/leanprover/lean4/pull/9027) provides an iterator combinator that lifts the emitted values
  into a higher universe level via `ULift`. This combinator is then used
  to make the subarray iterators universe-polymorphic. Previously, they
  were only available for `Subarray α` if `α : Type`.

* [#9030](https://github.com/leanprover/lean4/pull/9030) fixes a couple of bootstrapping-related hiccups in the newly
  added `Std.Do` module. More precisely,

* [#9038](https://github.com/leanprover/lean4/pull/9038) adds test cases for the VC generator and implements a few small
  and tedious fixes to ensure they pass.

* [#9049](https://github.com/leanprover/lean4/pull/9049) proves that the default `toList`, `toListRev` and `toArray`
  functions on slices can be described in terms of the slice iterator.
  Relying on new lemmas for the `uLift` and `attachWith` iterator
  combinators, a more concrete description of said functions is given for
  `Subarray`.

* [#9054](https://github.com/leanprover/lean4/pull/9054) corrects some inconsistencies in `TreeMap`/`HashMap` grind
  annotations, for `isSome_get?_eq_contains` and `empty_eq_emptyc`.

* [#9055](https://github.com/leanprover/lean4/pull/9055) renames `Array/Vector.extract_push` to `extract_push_of_le`, and
  replaces the lemma with one without a side condition.

* [#9058](https://github.com/leanprover/lean4/pull/9058) provides a `ToStream` instance for slices so that they can be
  used in `for i in xs, j in ys do` notation.

* [#9075](https://github.com/leanprover/lean4/pull/9075) adds `BEq` instances for `ByteArray` and `FloatArray` (also a
  `DecidableEq` instance for `ByteArray`).

## Compiler

* [#8594](https://github.com/leanprover/lean4/pull/8594) removes incorrect optimizations for strictOr/strictAnd from the
  old compiler, along with deleting an incorrect test. In order to do
  these optimizations correctly, nontermination analysis is required.
  Arguably, the correct way to express these optimizations is by exposing
  the implementation of strictOr/strictAnd to a nontermination-aware phase
  of the compiler, and then having them follow from more general
  transformations.

* [#8595](https://github.com/leanprover/lean4/pull/8595) wraps the invocation of the new compiler in `withoutExporting`.
  This is not necessary for the old compiler because it uses more direct
  access to the kernel environment.

* [#8602](https://github.com/leanprover/lean4/pull/8602) adds support to the new compiler for `Eq.recOn` (which is
  supported by the old compiler but missing a test).

* [#8604](https://github.com/leanprover/lean4/pull/8604) adds support for the `compiler.extract_closed` option to the new
  compiler, since this is used by the definition of `unsafeBaseIO`. We'll
  revisit this once we switch to the new compiler and rethink its
  relationship with IO.

* [#8614](https://github.com/leanprover/lean4/pull/8614) implements constant folding for `toNat` in the new compiler,
  which improves parity with the old compiler.

* [#8616](https://github.com/leanprover/lean4/pull/8616) adds constant folding for `Nat.pow` to the new compiler,
  following the same limits as the old compiler.

* [#8618](https://github.com/leanprover/lean4/pull/8618) implements LCNF constant folding for `Nat.nextPowerOfTwo`.

* [#8634](https://github.com/leanprover/lean4/pull/8634) makes `hasTrivialStructure?` return false for types whose
  constructors have types that are erased, e.g. if they construct a
  `Prop`.

* [#8636](https://github.com/leanprover/lean4/pull/8636) adds a function called `lean_setup_libuv` that initializes
  required LIBUV components. It needs to be outside of
  `lean_initialize_runtime_module` because it requires `argv` and `argc`
  to work correctly.

* [#8647](https://github.com/leanprover/lean4/pull/8647) improves the precision of the new compiler's `noncomputable`
  check for projections. There is no test included because while this was
  reduced from Mathlib, the old compiler does not correctly handle the
  reduced test case. It's not entirely clear to me if the check is passing
  with the old compiler for correct reasons. A test will be added to the
  new compiler's branch.

* [#8675](https://github.com/leanprover/lean4/pull/8675) increases the precision of the new compiler's non computable
  check, particularly around irrelevant uses of `noncomputable` defs in
  applications.

* [#8681](https://github.com/leanprover/lean4/pull/8681) adds an optimization to the LCNF simp pass where the
  discriminant of a `cases` construct will only be mark used if it has a
  non-default alternative.

* [#8683](https://github.com/leanprover/lean4/pull/8683) adds an optimization to the LCNF simp pass where the
  discriminant of a single-alt cases is only marked as used if any param
  is used.

* [#8709](https://github.com/leanprover/lean4/pull/8709) handles constants with erased types in `toMonoType`. It is much
  harder to write a test case for this than you would think, because most
  references to such types get replaced with `lcErased` earlier.

* [#8712](https://github.com/leanprover/lean4/pull/8712) optimizes let decls of an erased type to an erased value.
  Specialization can create local functions that produce a Prop, and
  there's no point in keeping them around.

* [#8716](https://github.com/leanprover/lean4/pull/8716) makes any type application of an erased term to be erased. This
  comes up a bit more than one would expect in the implementation of Lean
  itself.

* [#8717](https://github.com/leanprover/lean4/pull/8717) uses the fvar substitution mechanism to replace erased code.
  This isn't entirely satisfactory, since LCNF's `.return` doesn't support
  a general `Arg` (which has a `.erased` constructor), it only supports an
  `FVarId`. This is in contrast to the IR `.ret`, which does support a
  general `Arg`.

* [#8729](https://github.com/leanprover/lean4/pull/8729) changes LCNF's `FVarSubst` to use `Arg` rather than `Expr`. This
  enforces the requirements on substitutions, which match the requirements
  on `Arg`.

* [#8752](https://github.com/leanprover/lean4/pull/8752) fixes an issue where the `extendJoinPointContext` pass can lift
  join points containing projections to the top level, as siblings of
  `cases` constructs matching on other projections of the same base value.
  This prevents the `structProjCases` pass from projecting both at once,
  extending the lifetime of the parent value and breaking linearity at
  runtime.

* [#8754](https://github.com/leanprover/lean4/pull/8754) changes the implementation of computed fields in the new
  compiler, which should enable more optimizations (and remove a
  questionable hack in `toLCNF` that was only suitable for bringup). We
  convert `casesOn` to `cases` like we do for other inductive types, all
  constructors get replaced by their real implementations late in the base
  phase, and then the `cases` expression is rewritten to use the real
  constructors in `toMono`.

* [#8758](https://github.com/leanprover/lean4/pull/8758) adds caching for the `hasTrivialStructure?` function for LCNF
  types. This is one of the hottest small functions in the new compiler,
  so adding a cache makes a lot of sense.

* [#8764](https://github.com/leanprover/lean4/pull/8764) changes the LCNF pass pipeline so checks are no longer run by
  default after every pass, only after `init`, `saveBase`, `toMono` and
  `saveMono`. This is a compile time improvement, and the utility of these
  checks is decreased a bit after the decision to no longer attempt to
  preserve types throughout compilation. They have not been a significant
  way to discover issues during development of the new compiler.

* [#8802](https://github.com/leanprover/lean4/pull/8802) fixes a bug in `floatLetIn` where if one decl (e.g. a join
  point) is floated into a case arm and it uses another decl (e.g. another
  join point) that does not have any other existing uses in that arm, then
  the second decl does not get floated in despite this being perfectly
  legal. This was causing artificial array linearity issues in
  `Lean.Elab.Tactic.BVDecide.LRAT.trim.useAnalysis`.

* [#8816](https://github.com/leanprover/lean4/pull/8816) adds constant folding for Char.ofNat in LCNF simp. This
  implicitly relies on the representation of `Char` as `UInt32` rather
  than making a separate `.char` literal type, which seems reasonable as
  `Char` is erased by the trivial structure optimization in `toMono`.

* [#8822](https://github.com/leanprover/lean4/pull/8822) adds a cache for constructor info in toIR. This is called for
  all constructors, projections, and cases alternatives, so it makes sense
  to cache.

* [#8825](https://github.com/leanprover/lean4/pull/8825) improves IR generation for constructors of inductive types that
  are represented by scalars. Surprisingly, this isn't required for
  correctness, because the boxing pass will fix it up. The extra `unbox`
  operation it inserts shouldn't matter when compiling to native code,
  because it's trivial for a C compiler to optimize, but it does matter
  for the interpreter.

* [#8831](https://github.com/leanprover/lean4/pull/8831) caches the result of `lowerEnumToScalarType`, which is used
  heavily in LCNF to IR conversion.

* [#8885](https://github.com/leanprover/lean4/pull/8885) removes an old workaround around non-implemented C++11 features
  in the thread finalization.

* [#8923](https://github.com/leanprover/lean4/pull/8923) implements `casesOn` for `Thunk` and `Task`. Since these are
  builtin types, this needs to be special-cased in `toMono`.

* [#8952](https://github.com/leanprover/lean4/pull/8952) fixes the handling of the `never_extract` attribute in the
  compiler's CSE pass. There is an interesting debate to be had about
  exactly how hard the compiler should try to avoid duplicating anything
  that transitively uses `never_extract`, but this is the simplest form
  and roughly matches the check in the old compiler (although due to
  different handling of local function decls in the two compilers, the
  consequences might be slightly different).

* [#8956](https://github.com/leanprover/lean4/pull/8956) changes `toLCNF` to stop caching translations of expressions
  upon seeing an expression marked `never_extract`. This is more
  coarse-grained than it needs to be, but it is difficult to do any
  better, as the new compiler's `Expr` cache is based on structural
  identity (rather than the pointer identity of the old compiler).

* [#9003](https://github.com/leanprover/lean4/pull/9003) implements the validity check for the type of `main` in the new
  compiler. There were no tests for this, so it slipped under the radar.

## Pretty Printing

* [#7954](https://github.com/leanprover/lean4/pull/7954) improves `pp.oneline`, where it now preserves tags when
  truncating formatted syntax to a single line. Note that the `[...]`
  continuation does not yet have any functionality to enable seeing the
  untruncated syntax. Closes #3681.

* [#8617](https://github.com/leanprover/lean4/pull/8617) fixes (1) an issue where private names are not unresolved when
  they are pretty printed, (2) an issue where in `pp.universes` mode names
  were allowed to shadow local names, (3) an issue where in `match`
  patterns constants shadowing locals wouldn't use `_root_`, and (4) an
  issue where tactics might have an incorrect "try this" when
  `pp.fullNames` is set. Adds more delaboration tests for name
  unresolution.

* [#8626](https://github.com/leanprover/lean4/pull/8626) closes #3791, making sure that the Syntax formatter inserts
  whitespace before and after comments in the leading and trailing text of
  Syntax to avoid having comments comment out any following syntax, and to
  avoid comments' lexical syntax from being interpreted as being part of
  another syntax. If the text contains newlines before or after any
  comments, they are formatted as hard newlines rather than soft newlines.
  For example, `--` comments will have a hard newline after them. Note:
  metaprograms generating Syntax with comments should be sure to include
  newlines at the ends of `--` comments.

## Documentation

* [#8934](https://github.com/leanprover/lean4/pull/8934) adds explanations for a few errors concerning noncomputability,
  redundant match alternatives, and invalid inductive declarations.

* [#8990](https://github.com/leanprover/lean4/pull/8990) adds missing doc-strings for grind's internal algebra
  typeclasses, for inclusion in the reference manual.

* [#8998](https://github.com/leanprover/lean4/pull/8998) makes the docstrings related to `Format` and `Repr` have
  consistent formatting and style, and adds missing docstrings.

## Server

* [#8105](https://github.com/leanprover/lean4/pull/8105) adds support for server-sided `RpcRef` reuse and fixes a bug
  where trace nodes in the InfoView would close while the file was still
  being processed.

* [#8511](https://github.com/leanprover/lean4/pull/8511) implements signature help support. When typing a function
  application, editors with support for signature help will now display a
  popup that designates the current (remaining) function type. This
  removes the need to remember the function signature while typing the
  function application, or having to constantly cycle between hovering
  over the function identifier and typing the application. In VS Code, the
  signature help can be triggered manually using `Ctrl+Shift+Space`.

* [#8654](https://github.com/leanprover/lean4/pull/8654) adds server-side support for a new module hierarchy component in
  VS Code that can be used to navigate both the import tree of a module
  and the imported-by tree of a module. Specifically, it implements new
  requests `$/lean/prepareModuleHierarchy`,
  `$/lean/moduleHierarchy/imports` and
  `$/lean/moduleHierarchy/importedBy`. These requests are not supported by
  standard LSP. Companion PR at
  [leanprover/vscode-lean4#620](https://github.com/leanprover/vscode-lean4/pull/620).

* [#8699](https://github.com/leanprover/lean4/pull/8699) adds support to the server for the new module setup process by
  changing how `lake setup-file` is used.

* [#8868](https://github.com/leanprover/lean4/pull/8868) ensures that code actions do not have to wait for the full file
  to elaborate. This regression was accidentally introduced in #7665.

* [#9019](https://github.com/leanprover/lean4/pull/9019) fixes a bug where semantic highlighting would only highlight
  keywords that started with an alphanumeric character. Now, it uses
  `Lean.isIdFirst`.

## Lake

* [#7738](https://github.com/leanprover/lean4/pull/7738) makes memoization of built-in facets toggleable through a
  `memoize` option on the facet configuration. Built-in facets which are
  essentially aliases (e.g., `default`, `o`) have had memoization
  disabled.

* [#8447](https://github.com/leanprover/lean4/pull/8447) makes use of `lean --setup` in Lake builds of Lean modules and
  adds Lake support for the new `.olean` artifacts produced by the module
  system.

* [#8613](https://github.com/leanprover/lean4/pull/8613) changes the Lake version syntax (to `5.0.0-src+<commit>`) to
  ensure it is a well-formed SemVer,

* [#8656](https://github.com/leanprover/lean4/pull/8656) enables auto-implicits in the Lake math template. This resolves
  an issue where new users sometimes set up a new project for math
  formalization and then quickly realize that none of the code samples in
  our official books and docs that use auto-implicits work in their
  projects. With the introduction of [inlay hints for
  auto-implicits](https://github.com/leanprover/lean4/pull/6768), we
  consider the auto-implicit UX to be sufficiently usable that they can be
  enabled by default in the math template.
  Notably, this change does not affect Mathlib itself, which will proceed
  to disable auto-implicits.

* [#8701](https://github.com/leanprover/lean4/pull/8701) exports `LeanOption` in the `Lean` namespace from the `Lake`
  namespace. `LeanOption` was moved from `Lean` to `Lake` in #8447, which
  can cause unnecessary breakage without this.

* [#8736](https://github.com/leanprover/lean4/pull/8736) partially reverts #8024 which introduced a significant Lake
  performance regression during builds. Once the cause is discovered and
  fixed, a similar PR will be made to revert this.

* [#8846](https://github.com/leanprover/lean4/pull/8846) reintroduces the basics of `lean --setup` integration into Lake
  without the module computation which is still undergoing performance
  debugging in #8787.

* [#8866](https://github.com/leanprover/lean4/pull/8866) upgrades the `math` template for `lake init` and `lake new` to
  configures the new project to meet rigorous Mathlib maintenance
  standards. In comparison with the previous version (now available as
  `lake new ... math-lax`), this automatically provides:

  * Strict linting options matching Mathlib.
  * GitHub workflow for automatic upgrades to newer Lean and Mathlib
  releases.
  * Automatic release tagging for toolchain upgrades.
  * API documentation generated by
  [doc-gen4](https://github.com/leanprover/doc-gen4) and hosted on
  `github.io`.
  * README with some GitHub-specific instructions.

* [#8922](https://github.com/leanprover/lean4/pull/8922) introduces a local artifact cache for Lake. When enabled, Lake
  will shared build artifacts (built files) across different instances of
  the same package using an input- and content-addressed cache.

* [#8981](https://github.com/leanprover/lean4/pull/8981) removes Lake's usage of `lean -R` and `moduleNameOfFileName` to
  pass module names to Lean. For workspace names, it now relies on
  directly passing the module name through `lean --setup`. For
  non-workspace modules passed to `lake lean` or `lake setup-file`, it
  uses a fixed module name of `_unknown`.

* [#9068](https://github.com/leanprover/lean4/pull/9068) fixes some bugs with the local Lake artifact cache and cleans up
  the surrounding API. It also adds the ability to opt-in to the cache on
  packages without `enableArtifactCache` set using the
  `LAKE_ARTIFACT_CACHE` environment variable.

* [#9081](https://github.com/leanprover/lean4/pull/9081) fixes a bug with Lake where the job monitor would sit on a
  top-level build (e.g., `mathlib/Mathlib:default`) instead of reporting
  module build progress.

* [#9101](https://github.com/leanprover/lean4/pull/9101) fixes a bug introduce by #9081 where the source file was dropped
  from the module input trace and some entries were dropped from the
  module job log.

## Other

* [#8702](https://github.com/leanprover/lean4/pull/8702) enhances the PR release workflow to create both short format and
  SHA-suffixed release tags. Creates both pr-release-{PR_NUMBER} and
  pr-release-{PR_NUMBER}-{SHORT_SHA} tags, generates separate releases for
  both formats, adds separate GitHub status checks, and updates
  Batteries/Mathlib testing branches to use SHA-suffixed tags for exact
  commit traceability.

* [#8710](https://github.com/leanprover/lean4/pull/8710) pins the precise hash of softprops/action-gh-release to

* [#9033](https://github.com/leanprover/lean4/pull/9033) adds a Mathlib-like testing and feedback system for the
  reference manual. Lean PRs will receive comments that reflect the status
  of the language reference with respect to the PR.

* [#9092](https://github.com/leanprover/lean4/pull/9092) further updates release automation. The per-repository update
  scripts `script/release_steps.py` now actually performs the tests,
  rather than outputting a script for the release manager to run line by
  line. It's been tested on `v4.21.0` (i.e. the easy case of a stable
  release), and we'll debug its behaviour on `v4.22.0-rc1` tonight.


````
