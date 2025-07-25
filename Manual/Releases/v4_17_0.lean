/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: investigate why the Markdown elaboration is taking this much stack in the new compiler
set_option maxRecDepth 9500

#doc (Manual) "Lean 4.17.0 (2025-03-03)" =>
%%%
tag := "release-v4.17.0"
file := "v4.17.0"
%%%

````markdown

For this release, 319 changes landed. In addition to the 168 feature additions and 57 fixes listed below there were 12 refactoring changes, 13 documentation improvements and 56 chores.


## Highlights

The Lean v4.17 release brings a range of new features, performance improvements,
and bug fixes. Notable user-visible updates include:

* [#6368](https://github.com/leanprover/lean4/pull/6368) implements executing kernel checking in parallel to elaboration,
which is a prerequisite for parallelizing elaboration itself.

* [#6711](https://github.com/leanprover/lean4/pull/6711) adds support for `UIntX` and `USize` in `bv_decide` by adding a
preprocessor that turns them into `BitVec` of their corresponding size.

* [#6505](https://github.com/leanprover/lean4/pull/6505) implements a basic async framework as well as asynchronously
running timers using libuv.

* improvements to documentation with `docgen`, which now links
dot notations ([#6703](https://github.com/leanprover/lean4/pull/6703)),
coerced functions ([#6729](https://github.com/leanprover/lean4/pull/6729)),
and tokens ([#6730](https://github.com/leanprover/lean4/pull/6730)).

* extensive library development, in particular, expanding verification APIs of `BitVec`,
making APIs of `List` / `Array` / `Vector` consistent, and adding lemmas describing the behavior of `UInt`.

* [#6597](https://github.com/leanprover/lean4/pull/6597) fixes the indentation of nested traces nodes in the info view.

### New Language Features

* **Partial Fixpoint**

  [#6355](https://github.com/leanprover/lean4/pull/6355) adds the ability to define possibly non-terminating functions
and still be able to reason about them equationally, as long as they are
tail-recursive, or operate within certain monads such as `Option`

  Typical examples:

  ```lean
  def ack : (n m : Nat) → Option Nat
    | 0,   y   => some (y+1)
    | x+1, 0   => ack x 1
    | x+1, y+1 => do ack x (← ack (x+1) y)
  partial_fixpoint

  def whileSome (f : α → Option α) (x : α) : α :=
    match f x with
    | none => x
    | some x' => whileSome f x'
  partial_fixpoint

  def computeLfp {α : Type u} [DecidableEq α] (f : α → α) (x : α) : α :=
    let next := f x
    if x ≠ next then
      computeLfp f next
    else
      x
  partial_fixpoint
  ```

  See the [reference manual](https://lean-lang.org/doc/reference/latest/Recursive-Definitions/Partial-Fixpoint-Recursion/#partial-fixpoint)
for more details.

* [#6905](https://github.com/leanprover/lean4/pull/6905) adds a first draft of the `try`?
  interactive tactic, which tries various tactics, including induction:
  ```lean
  @[simp] def revAppend : List Nat → List Nat → List Nat
  | [],    ys => ys
  | x::xs, ys => revAppend xs (x::ys)

  example : (revAppend xs ys).length = xs.length + ys.length := by
    try?
    /-
    Try these:
    • · induction xs, ys using revAppend.induct
        · simp
        · simp +arith [*]
    • · induction xs, ys using revAppend.induct
        · simp only [revAppend, List.length_nil, Nat.zero_add]
        · simp +arith only [revAppend, List.length_cons, *]
    -/
  ```

* **`induction` with zero alternatives**

  [#6486](https://github.com/leanprover/lean4/pull/6486) modifies the `induction`/`cases` syntax so that the `with`
clause does not need to be followed by any alternatives. This improves
friendliness of these tactics, since this lets them surface the names of
the missing alternatives:
  ```lean
  example (n : Nat) : True := by
    induction n with
  /-            ~~~~
  alternative 'zero' has not been provided
  alternative 'succ' has not been provided
  -/
  ```

* **`simp?` and `dsimp?` tactics in conversion mode**

  [#6593](https://github.com/leanprover/lean4/pull/6593) adds support for the `simp?` and `dsimp?` tactics in conversion
mode.

* **`fun_cases`**

  [#6261](https://github.com/leanprover/lean4/pull/6261) adds `foo.fun_cases`, an automatically generated theorem that
splits the goal according to the branching structure of `foo`, much like
the Functional Induction Principle, but for all functions (not just
recursive ones), and without providing inductive hypotheses.

### New CLI Features

* [#6427](https://github.com/leanprover/lean4/pull/6427) adds the Lean CLI option `--src-deps` which parallels `--deps`.
It parses the Lean code's header and prints out the paths to the
(transitively) imported modules' source files (deduced from
`LEAN_SRC_PATH`).

* [#6323](https://github.com/leanprover/lean4/pull/6323) adds a new Lake CLI command, `lake query`, that both builds
targets and outputs their results. It can produce raw text or JSON
-formatted output (with `--json` / `-J`).

### Breaking Changes

* [#6602](https://github.com/leanprover/lean4/pull/6602) allows the dot ident notation to resolve to the current
definition, or to any of the other definitions in the same mutual block.
Existing code that uses dot ident notation may need to have `nonrec`
added if the ident has the same name as the definition.

* Introduction of the `zetaUnused` simp and reduction option ([#6755](https://github.com/leanprover/lean4/pull/6755))
is a breaking change in rare cases: the `split` tactic no longer removes unused `let` and `have` expressions as a side-effect.
`dsimp only` can be used to remove unused `have` and `let` expressions.

_This highlights section was contributed by Violetta Sim._

## Language

* [#5145](https://github.com/leanprover/lean4/pull/5145) splits the environment used by the kernel from that used by the
elaborator, providing the foundation for tracking of asynchronously
elaborated declarations, which will exist as a concept only in the
latter.

* [#6261](https://github.com/leanprover/lean4/pull/6261) adds `foo.fun_cases`, an automatically generated theorem that
splits the goal according to the branching structure of `foo`, much like
the Functional Induction Principle, but for all functions (not just
recursive ones), and without providing inductive hypotheses.

* [#6355](https://github.com/leanprover/lean4/pull/6355) adds the ability to define possibly non-terminating functions
and still be able to reason about them equationally, as long as they are
tail-recursive or monadic.

* [#6368](https://github.com/leanprover/lean4/pull/6368) implements executing kernel checking in parallel to elaboration,
which is a prerequisite for parallelizing elaboration itself.

* [#6427](https://github.com/leanprover/lean4/pull/6427) adds the Lean CLI option `--src-deps` which parallels `--deps`.
It parses the Lean code's header and prints out the paths to the
(transitively) imported modules' source files (deduced from
`LEAN_SRC_PATH`).

* [#6486](https://github.com/leanprover/lean4/pull/6486) modifies the `induction`/`cases` syntax so that the `with`
clause does not need to be followed by any alternatives. This improves
friendliness of these tactics, since this lets them surface the names of
the missing alternatives:
  ```lean
  example (n : Nat) : True := by
    induction n with
  /-            ~~~~
  alternative 'zero' has not been provided
  alternative 'succ' has not been provided
  -/
  ```

* [#6505](https://github.com/leanprover/lean4/pull/6505) implements a basic async framework as well as asynchronously
running timers using libuv.

* [#6516](https://github.com/leanprover/lean4/pull/6516) enhances the `cases` tactic used in the `grind` tactic and
ensures that it can be applied to arbitrary expressions.

* [#6521](https://github.com/leanprover/lean4/pull/6521) adds support for activating relevant `match`-equations as
E-matching theorems. It uses the `match`-equation lhs as the pattern.

* [#6528](https://github.com/leanprover/lean4/pull/6528) adds a missing propagation rule to the (WIP) `grind` tactic.

* [#6529](https://github.com/leanprover/lean4/pull/6529) adds support for `let`-declarations to the (WIP) `grind` tactic.

* [#6530](https://github.com/leanprover/lean4/pull/6530) fixes nondeterministic failures in the (WIP) `grind` tactic.

* [#6531](https://github.com/leanprover/lean4/pull/6531) fixes the support for `let_fun` in `grind`.

* [#6533](https://github.com/leanprover/lean4/pull/6533) adds support to E-matching offset patterns. For example, we want
to be able to E-match the pattern `f (#0 + 1)` with term `f (a + 2)`.

* [#6534](https://github.com/leanprover/lean4/pull/6534) ensures that users can utilize projections in E-matching
patterns within the `grind` tactic.

* [#6536](https://github.com/leanprover/lean4/pull/6536) fixes different thresholds for controlling E-matching in the
`grind` tactic.

* [#6538](https://github.com/leanprover/lean4/pull/6538) ensures patterns provided by users are normalized. See new test
to understand why this is needed.

* [#6539](https://github.com/leanprover/lean4/pull/6539) introduces the `[grind_eq]` attribute, designed to annotate
equational theorems and functions for heuristic instantiations in the
`grind` tactic.
When applied to an equational theorem, the `[grind_eq]` attribute
instructs the `grind` tactic to automatically use the annotated theorem
to instantiate patterns during proof search. If applied to a function,
it marks all equational theorems associated with that function.

* [#6543](https://github.com/leanprover/lean4/pull/6543) adds additional tests for `grind`, demonstrating that we can
automate some manual proofs from Mathlib's basic category theory
library, with less reliance on Mathlib's `@[reassoc]` trick.

* [#6545](https://github.com/leanprover/lean4/pull/6545) introduces the parametric attribute `[grind]` for annotating
theorems and definitions. It also replaces `[grind_eq]` with `[grind
=]`. For definitions, `[grind]` is equivalent to `[grind =]`.

* [#6556](https://github.com/leanprover/lean4/pull/6556) adds propagators for implication to the `grind` tactic. It also
disables the normalization rule: `(p → q) = (¬ p ∨ q)`

* [#6559](https://github.com/leanprover/lean4/pull/6559) adds a basic case-splitting strategy for the `grind` tactic. We
still need to add support for user customization.

* [#6565](https://github.com/leanprover/lean4/pull/6565) fixes the location of the error emitted when the `rintro` and
`intro` tactics cannot introduce the requested number of binders.

* [#6566](https://github.com/leanprover/lean4/pull/6566) adds support for erasing the `[grind]` attribute used to mark
theorems for heuristic instantiation in the `grind` tactic.

* [#6567](https://github.com/leanprover/lean4/pull/6567) adds support for erasing the `[grind]` attribute used to mark
theorems for heuristic instantiation in the `grind` tactic.

* [#6568](https://github.com/leanprover/lean4/pull/6568) adds basic support for cast-like operators to the grind tactic.
Example:
  ```lean
  example (α : Type) (β : Type) (a₁ a₂ : α) (b₁ b₂ : β)
          (h₁ : α = β)
          (h₂ : h₁ ▸ a₁ = b₁)
          (h₃ : a₁ = a₂)
          (h₄ : b₁ = b₂)
          : HEq a₂ b₂ := by
    grind
  ```

* [#6569](https://github.com/leanprover/lean4/pull/6569) adds support for case splitting on `match`-expressions in
`grind`.
We still need to add support for resolving the antecedents of
`match`-conditional equations.

* [#6575](https://github.com/leanprover/lean4/pull/6575) ensures tactics are evaluated incrementally in the body of
`classical`.

* [#6578](https://github.com/leanprover/lean4/pull/6578) fixes and improves the propagator for forall-expressions in the
`grind` tactic.

* [#6581](https://github.com/leanprover/lean4/pull/6581) adds the following configuration options to `Grind.Config`:
`splitIte`, `splitMatch`, and `splitIndPred`.

* [#6582](https://github.com/leanprover/lean4/pull/6582) adds support for creating local E-matching theorems for
universal propositions known to be true. It allows `grind` to
automatically solve examples such as:

* [#6584](https://github.com/leanprover/lean4/pull/6584) adds helper theorems to implement offset constraints in grind.

* [#6585](https://github.com/leanprover/lean4/pull/6585) fixes a bug in the `grind` canonicalizer.

* [#6588](https://github.com/leanprover/lean4/pull/6588) improves the `grind` canonicalizer diagnostics.

* [#6593](https://github.com/leanprover/lean4/pull/6593) adds support for the `simp?` and `dsimp?` tactics in conversion
mode.

* [#6595](https://github.com/leanprover/lean4/pull/6595) improves the theorems used to justify the steps performed by the
inequality offset module. See new test for examples of how they are
going to be used.

* [#6600](https://github.com/leanprover/lean4/pull/6600) removes functions from compiling decls from Environment, and
moves all users to functions on CoreM. This is required for supporting
the new code generator, since its implementation uses CoreM.

* [#6602](https://github.com/leanprover/lean4/pull/6602) allows the dot ident notation to resolve to the current
definition, or to any of the other definitions in the same mutual block.
Existing code that uses dot ident notation may need to have `nonrec`
added if the ident has the same name as the definition.

* [#6603](https://github.com/leanprover/lean4/pull/6603) implements support for offset constraints in the `grind` tactic.
Several features are still missing, such as constraint propagation and
support for offset equalities, but `grind` can already solve examples
like the following:

* [#6606](https://github.com/leanprover/lean4/pull/6606) fixes a bug in the pattern selection in the `grind`.

* [#6607](https://github.com/leanprover/lean4/pull/6607) adds support for case-splitting on `<->` (and `@Eq Prop`) in the
`grind` tactic.

* [#6608](https://github.com/leanprover/lean4/pull/6608) fixes a bug in the `simp_arith` tactic. See new test.

* [#6609](https://github.com/leanprover/lean4/pull/6609) improves the case-split heuristic used in grind, prioritizing
case-splits with fewer cases.

* [#6610](https://github.com/leanprover/lean4/pull/6610) fixes a bug in the `grind` core module responsible for merging
equivalence classes and propagating constraints.

* [#6611](https://github.com/leanprover/lean4/pull/6611) fixes one of the sanity check tests used in `grind`.

* [#6613](https://github.com/leanprover/lean4/pull/6613) improves the case split heuristic used in the `grind` tactic,
ensuring it now avoids unnecessary case-splits on `Iff`.

* [#6614](https://github.com/leanprover/lean4/pull/6614) improves the usability of the `[grind =]` attribute by
automatically handling
forbidden pattern symbols. For example, consider the following theorem
tagged with this attribute:
  ```lean
  getLast?_eq_some_iff {xs : List α} {a : α} : xs.getLast? = some a ↔ ∃ ys, xs = ys ++ [a]
  ```
  Here, the selected pattern is `xs.getLast? = some a`, but `Eq` is a
forbidden pattern symbol.
Instead of producing an error, this function converts the pattern into a
multi-pattern,
allowing the attribute to be used conveniently.

* [#6615](https://github.com/leanprover/lean4/pull/6615) adds two auxiliary functions `mkEqTrueCore` and `mkOfEqTrueCore`
that avoid redundant proof terms in proofs produced by `grind`.

* [#6618](https://github.com/leanprover/lean4/pull/6618) implements exhaustive offset constraint propagation in the
`grind` tactic. This enhancement minimizes the number of case splits
performed by `grind`. For instance, it can solve the following example
without performing any case splits:

* [#6633](https://github.com/leanprover/lean4/pull/6633) improves the failure message produced by the `grind` tactic. We
now include information about asserted facts, propositions that are
known to be true and false, and equivalence classes.

* [#6636](https://github.com/leanprover/lean4/pull/6636) implements model construction for offset constraints in the
`grind` tactic.

* [#6639](https://github.com/leanprover/lean4/pull/6639) puts the `bv_normalize` simp set into simp_nf and splits up the
bv_normalize implementation across multiple files in preparation for
upcoming changes.

* [#6641](https://github.com/leanprover/lean4/pull/6641) implements several optimisation tricks from Bitwuzla's
preprocessing passes into the Lean equivalent in `bv_decide`. Note that
these changes are mostly geared towards large proof states as for
example seen in SMT-Lib.

* [#6645](https://github.com/leanprover/lean4/pull/6645) implements support for offset equality constraints in the
`grind` tactic and exhaustive equality propagation for them. The `grind`
tactic can now solve problems such as the following:

* [#6648](https://github.com/leanprover/lean4/pull/6648) adds support for numerals, lower & upper bounds to the offset
constraint module in the `grind` tactic. `grind` can now solve examples
such as:
  ```lean
  example (f : Nat → Nat) :
          f 2 = a →
          b ≤ 1 → b ≥ 1 →
          c = b + 1 →
          f c = a := by
    grind
  ```
  In the example above, the literal `2` and the lower&upper bounds, `b ≤
1` and `b ≥ 1`, are now processed by offset constraint module.

* [#6649](https://github.com/leanprover/lean4/pull/6649) fixes a bug in the term canonicalizer used in the `grind`
tactic.

* [#6652](https://github.com/leanprover/lean4/pull/6652) adds the `int_toBitVec` simp set to convert UIntX and later IntX
propositions to BitVec ones. This will be used as a preprocessor for `bv_decide` to provide UIntX/IntX `bv_decide` support.

* [#6653](https://github.com/leanprover/lean4/pull/6653) improves the E-matching pattern selection heuristics in the
`grind` tactic. They now take into account type predicates and
transformers.

* [#6654](https://github.com/leanprover/lean4/pull/6654) improves the support for partial applications in the E-matching
procedure used in `grind`.

* [#6656](https://github.com/leanprover/lean4/pull/6656) improves the diagnostic information provided in `grind` failure
states. We now include the list of issues found during the search, and
all search thresholds that have been reached. also improves its
formatting.

* [#6657](https://github.com/leanprover/lean4/pull/6657) improves the `grind` search procedure, and adds the new
configuration option: `failures`.

* [#6658](https://github.com/leanprover/lean4/pull/6658) ensures that `grind` avoids case-splitting on terms congruent to
those that have already been case-split.

* [#6659](https://github.com/leanprover/lean4/pull/6659) fixes a bug in the `grind` term preprocessor. It was abstracting
nested proofs **before** reducible constants were unfolded.

* [#6662](https://github.com/leanprover/lean4/pull/6662) improves the canonicalizer used in the `grind` tactic and the
diagnostics it produces. It also adds a new configuration option,
`canonHeartbeats`, to address (some of) the issues. Here is an example
illustrating the new diagnostics, where we intentionally create a
problem by using a very small number of heartbeats.

* [#6663](https://github.com/leanprover/lean4/pull/6663) implements a basic equality resolution procedure for the `grind`
tactic.

* [#6669](https://github.com/leanprover/lean4/pull/6669) adds a workaround for the discrepancy between Terminal/Emacs and
VS Code when displaying info trees.

* [#6675](https://github.com/leanprover/lean4/pull/6675) adds `simp`-like parameters to `grind`, and `grind only` similar
to `simp only`.

* [#6679](https://github.com/leanprover/lean4/pull/6679) changes the identifier parser to allow for the ⱼ unicode
character which was forgotten as it lives by itself in a codeblock with
coptic characters.

* [#6682](https://github.com/leanprover/lean4/pull/6682) adds support for extensionality theorems (using the `[ext]`
attribute) to the `grind` tactic. Users can disable this functionality
using `grind -ext` . Below are examples that demonstrate problems now
solvable by `grind`.

* [#6685](https://github.com/leanprover/lean4/pull/6685) fixes the issue that `#check_failure`'s output is warning

* [#6686](https://github.com/leanprover/lean4/pull/6686) fixes parameter processing, initialization, and attribute
handling issues in the `grind` tactic.

* [#6691](https://github.com/leanprover/lean4/pull/6691) introduces the central API for making parallel changes to the
environment

* [#6692](https://github.com/leanprover/lean4/pull/6692) removes the `[grind_norm]` attribute. The normalization theorems
used by `grind` are now fixed and cannot be modified by users. We use
normalization theorems to ensure the built-in procedures receive term
wish expected "shapes". We use it for types that have built-in support
in grind. Users could misuse this feature as a simplification rule. For
example, consider the following example:

* [#6700](https://github.com/leanprover/lean4/pull/6700) adds support for beta reduction in the `grind` tactic. `grind`
can now solve goals such as
  ```lean
  example (f : Nat → Nat) : f = (fun x : Nat => x + 5) → f 2 > 5 := by
    grind
  ```

* [#6702](https://github.com/leanprover/lean4/pull/6702) adds support for equality backward reasoning to `grind`. We can
illustrate the new feature with the following example. Suppose we have a
theorem:
  ```lean
  theorem inv_eq {a b : α} (w : a * b = 1) : inv a = b
  ```
  and we want to instantiate the theorem whenever we are tying to prove
`inv t = s` for some terms `t` and `s`
The attribute `[grind ←]` is not applicable in this case because, by
default, `=` is not eligible for E-matching. The new attribute `[grind
←=]` instructs `grind` to use the equality and consider disequalities in
the `grind` proof state as candidates for E-matching.

* [#6705](https://github.com/leanprover/lean4/pull/6705) adds the attributes `[grind cases]` and `[grind cases eager]`
for controlling case splitting in `grind`. They will replace the
`[grind_cases]` and the configuration option `splitIndPred`.

* [#6711](https://github.com/leanprover/lean4/pull/6711) adds support for `UIntX` and `USize` in `bv_decide` by adding a
preprocessor that turns them into `BitVec` of their corresponding size.

* [#6717](https://github.com/leanprover/lean4/pull/6717) introduces a new feature that allows users to specify which
inductive datatypes the `grind` tactic should perform case splits on.
The configuration option `splitIndPred` is now set to `false` by
default. The attribute `[grind cases]` is used to mark inductive
datatypes and predicates that `grind` may case split on during the
search. Additionally, the attribute `[grind cases eager]` can be used to
mark datatypes and predicates for case splitting both during
pre-processing and the search.

* [#6718](https://github.com/leanprover/lean4/pull/6718) adds BitVec lemmas required to cancel multiplicative negatives,
and plumb support through to `bv_normalize` to make use of this result in
the normalized twos-complement form.

* [#6719](https://github.com/leanprover/lean4/pull/6719) fixes a bug in the equational theorem generator for
`match`-expressions. See new test for an example.

* [#6724](https://github.com/leanprover/lean4/pull/6724) adds support for `bv_decide` to automatically split up
non-recursive structures that contain information about supported types.
It can be controlled using the new `structures` field in the `bv_decide`
config.

* [#6733](https://github.com/leanprover/lean4/pull/6733) adds better support for overlapping `match` patterns in `grind`.
`grind` can now solve examples such as
  ```lean
  inductive S where
    | mk1 (n : Nat)
    | mk2 (n : Nat) (s : S)
    | mk3 (n : Bool)
    | mk4 (s1 s2 : S)

  def f (x y : S) :=
    match x, y with
    | .mk1 _, _ => 2
    | _, .mk2 1 (.mk4 _ _) => 3
    | .mk3 _, _ => 4
    | _, _ => 5

  example : b = .mk2 y1 y2 → y1 = 2 → a = .mk4 y3 y4 → f a b = 5 := by
    unfold f
    grind (splits := 0)
  ```

* [#6735](https://github.com/leanprover/lean4/pull/6735) adds support for case splitting on `match`-expressions with
overlapping patterns to the `grind` tactic. `grind` can now solve
examples such as:
  ```lean
  inductive S where
    | mk1 (n : Nat)
    | mk2 (n : Nat) (s : S)
    | mk3 (n : Bool)
    | mk4 (s1 s2 : S)

  def g (x y : S) :=
    match x, y with
    | .mk1 a, _ => a + 2
    | _, .mk2 1 (.mk4 _ _) => 3
    | .mk3 _, .mk4 _ _ => 4
    | _, _ => 5

  example : g a b > 1 := by
    grind [g.eq_def]
  ```

* [#6736](https://github.com/leanprover/lean4/pull/6736) ensures the canonicalizer used in `grind` does not waste time
checking whether terms with different types are definitionally equal.

* [#6737](https://github.com/leanprover/lean4/pull/6737) ensures that the branches of an `if-then-else` term are
internalized only after establishing the truth value of the condition.
This change makes its behavior consistent with the `match`-expression
and dependent `if-then-else` behavior in `grind`.
This feature is particularly important for recursive functions defined
by well-founded recursion and `if-then-else`. Without lazy
`if-then-else` branch internalization, the equation theorem for the
recursive function would unfold until reaching the generation depth
threshold, and before performing any case analysis. See new tests for an
example.

* [#6739](https://github.com/leanprover/lean4/pull/6739) adds a fast path for bitblasting multiplication with constants
in `bv_decide`.

* [#6740](https://github.com/leanprover/lean4/pull/6740) extends `bv_decide`'s structure reasoning support for also
reasoning about equalities of supported structures.

* [#6745](https://github.com/leanprover/lean4/pull/6745) supports rewriting `ushiftRight` in terms of `extractLsb'`. This
is the companion PR to #6743 which adds the similar lemmas about
`shiftLeft`.

* [#6746](https://github.com/leanprover/lean4/pull/6746) ensures that conditional equation theorems for function
definitions are handled correctly in `grind`. We use the same
infrastructure built for `match`-expression equations. Recall that in
both cases, these theorems are conditional when there are overlapping
patterns.

* [#6748](https://github.com/leanprover/lean4/pull/6748) fixes a few bugs in the `grind` tactic: missing issues, bad
error messages, incorrect threshold in the canonicalizer, and bug in the
ground pattern internalizer.

* [#6750](https://github.com/leanprover/lean4/pull/6750) adds support for fixing type mismatches using `cast` while
instantiating quantifiers in the E-matching module used by the grind
tactic.

* [#6754](https://github.com/leanprover/lean4/pull/6754) adds the `+zetaUnused` option.

* [#6755](https://github.com/leanprover/lean4/pull/6755) implements the `zetaUnused` simp and reduction option (added in
#6754).

* [#6761](https://github.com/leanprover/lean4/pull/6761) fixes issues in `grind` when processing `match`-expressions with
indexed families.

* [#6773](https://github.com/leanprover/lean4/pull/6773) fixes a typo that prevented `Nat.reduceAnd` from working
correctly.

* [#6777](https://github.com/leanprover/lean4/pull/6777) fixes a bug in the internalization of offset terms in the
`grind` tactic. For example, `grind` was failing to solve the following
example because of this bug.
  ```lean
  example (f : Nat → Nat) : f (a + 1) = 1 → a = 0 → f 1 = 1 := by
    grind
  ```

* [#6778](https://github.com/leanprover/lean4/pull/6778) fixes the assignment produced by `grind` to satisfy the offset
constraints in a goal.

* [#6779](https://github.com/leanprover/lean4/pull/6779) improves the support for `match`-expressions in the `grind`
tactic.

* [#6781](https://github.com/leanprover/lean4/pull/6781) fixes the support for case splitting on data in the `grind`
tactic. The following example works now:
  ```lean
  inductive C where
    | a | b | c

  def f : C → Nat
    | .a => 2
    | .b => 3
    | .c => 4

  example : f x > 1 := by
    grind [
        f, -- instructs `grind` to use `f`-equation theorems,
        C -- instructs `grind` to case-split on free variables of type `C`
    ]
  ```

* [#6783](https://github.com/leanprover/lean4/pull/6783) adds support for closing goals using `match`-expression
conditions that are known to be true in the `grind` tactic state.
`grind` can now solve goals such as:
  ```lean
  def f : List Nat → List Nat → Nat
    | _, 1 :: _ :: _ => 1
    | _, _ :: _ => 2
    | _, _  => 0

  example : z = a :: as → y = z → f x y > 0
  ```

* [#6785](https://github.com/leanprover/lean4/pull/6785) adds infrastructure for the `grind?` tactic. It also adds the
new modifier `usr` which allows users to write `grind only [use thmName]` to instruct `grind` to only use theorem `thmName`, but using
the patterns specified with the command `grind_pattern`.

* [#6788](https://github.com/leanprover/lean4/pull/6788) teaches bv_normalize that `!(x < x)` and `!(x < 0)`.

* [#6790](https://github.com/leanprover/lean4/pull/6790) fixes an issue with the generation of equational theorems from
`partial_fixpoint` when case-splitting is necessary. Fixes #6786.

* [#6791](https://github.com/leanprover/lean4/pull/6791) fixes #6789 by ensuring metadata generated for inaccessible
variables in pattern-matches is consumed in `casesOnStuckLHS`
accordingly.

* [#6801](https://github.com/leanprover/lean4/pull/6801) fixes a bug in the exhaustive offset constraint propagation
module used in `grind`.

* [#6810](https://github.com/leanprover/lean4/pull/6810) implements a basic `grind?` tactic companion for `grind`. We
will add more bells and whistles later.

* [#6822](https://github.com/leanprover/lean4/pull/6822) adds a few builtin case-splits for `grind`. They are similar to
builtin `simp` theorems. They reduce the noise in the tactics produced
by `grind?`.

* [#6824](https://github.com/leanprover/lean4/pull/6824) introduces the auxiliary command `%reset_grind_attrs` for
debugging purposes. It is particularly useful for writing self-contained
tests.

* [#6834](https://github.com/leanprover/lean4/pull/6834) adds "performance" counters (e.g., number of instances per
theorem) to `grind`. The counters are always reported on failures, and
on successes when `set_option diagnostics true`.

* [#6839](https://github.com/leanprover/lean4/pull/6839) ensures `grind` can use constructors and axioms for heuristic
instantiation based on E-matching. It also allows patterns without
pattern variables for theorems such as `theorem evenz : Even 0`.

* [#6851](https://github.com/leanprover/lean4/pull/6851) makes `bv_normalize` rewrite shifts by `BitVec` constants to
shifts by `Nat` constants. This is part of the greater effort in
providing good support for constant shift simplification in
`bv_normalize`.

* [#6852](https://github.com/leanprover/lean4/pull/6852) allows environment extensions to opt into access modes that do
not block on the entire environment up to this point as a necessary
prerequisite for parallel proof elaboration.

* [#6854](https://github.com/leanprover/lean4/pull/6854) adds a convenience for inductive predicates in `grind`. Now,
give an inductive predicate `C`, `grind [C]` marks `C` terms as
case-split candidates **and** `C` constructors as E-matching theorems.
Here is an example:
  ```lean
  example {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
    grind [BigStep]
  ```
  Users can still use `grind [cases BigStep]` to only mark `C` as a case
split candidate.

* [#6858](https://github.com/leanprover/lean4/pull/6858) adds new propagation rules for `decide` and equality in `grind`.
It also adds new tests and cleans old ones

* [#6861](https://github.com/leanprover/lean4/pull/6861) adds propagation rules for `Bool.and`, `Bool.or`, and `Bool.not`
to the `grind` tactic.

* [#6870](https://github.com/leanprover/lean4/pull/6870) adds two new normalization steps in `grind` that reduces `a !=
b` and `a == b` to `decide (¬ a = b)` and `decide (a = b)`,
respectively.

* [#6879](https://github.com/leanprover/lean4/pull/6879) fixes a bug in `mkMatchCondProf?` used by the `grind` tactic.
This bug was introducing a failure in the test `grind_constProp.lean`.

* [#6880](https://github.com/leanprover/lean4/pull/6880) improves the E-matching pattern selection heuristic used in
`grind`.

* [#6881](https://github.com/leanprover/lean4/pull/6881) improves the `grind` error message by including a trace of the
terms on which `grind` applied `cases`-like operations.

* [#6882](https://github.com/leanprover/lean4/pull/6882) ensures `grind` auxiliary gadgets are "hidden" in error and
diagnostic messages.

* [#6888](https://github.com/leanprover/lean4/pull/6888) adds the `[grind intro]` attribute. It instructs `grind` to mark
the introduction rules of an inductive predicate as E-matching theorems.

* [#6889](https://github.com/leanprover/lean4/pull/6889) inlines a few functions in the `bv_decide` circuit cache.

* [#6892](https://github.com/leanprover/lean4/pull/6892) fixes a bug in the pattern selection heuristic used in `grind`.
It was unfolding definitions/abstractions that were not supposed to be
unfolded. See `grind_constProp.lean` for examples affected by this bug.

* [#6895](https://github.com/leanprover/lean4/pull/6895) fixes a few `grind` issues exposed by the `grind_constProp.lean`
test.
  - Support for equational theorem hypotheses created before invoking
  `grind`. Example: applying an induction principle.s
  - Support of `Unit`-like types.
  - Missing recursion depth checks.

* [#6897](https://github.com/leanprover/lean4/pull/6897) adds the new attributes `[grind =>]` and `[grind <=]` for
controlling pattern selection and minimizing the number of places where
we have to use verbose `grind_pattern` command. It also fixes a bug in
the new pattern selection procedure, and improves the automatic pattern
selection for local lemmas.

* [#6904](https://github.com/leanprover/lean4/pull/6904) adds the `grind` configuration option `verbose`. For example,
`grind -verbose` disables all diagnostics. We are going to use this flag
to implement `try?`.

* [#6905](https://github.com/leanprover/lean4/pull/6905) adds the `try?` tactic; see above

## Library

* [#6177](https://github.com/leanprover/lean4/pull/6177) implements `BitVec.*_fill`.

* [#6211](https://github.com/leanprover/lean4/pull/6211) verifies the `insertMany` method on `HashMap`s for the special
case of inserting lists.

* [#6346](https://github.com/leanprover/lean4/pull/6346) completes the toNat/Int/Fin family for `shiftLeft`.

* [#6347](https://github.com/leanprover/lean4/pull/6347) adds `BitVec.toNat_rotateLeft` and `BitVec.toNat_rotateLeft`.

* [#6402](https://github.com/leanprover/lean4/pull/6402) adds a `toFin` and `msb` lemma for unsigned bitvector division.
We *don't* have `toInt_udiv`, since the only truly general statement we
can make does no better than unfolding the definition, and it's not
uncontroversially clear how to unfold `toInt` (see
`toInt_eq_msb_cond`/`toInt_eq_toNat_cond`/`toInt_eq_toNat_bmod` for a
few options currently provided). Instead, we do have `toInt_udiv_of_msb`
that's able to provide a more meaningful rewrite given an extra
side-condition (that `x.msb = false`).

* [#6404](https://github.com/leanprover/lean4/pull/6404) adds a `toFin` and `msb` lemma for unsigned bitvector modulus.
Similar to #6402, we don't provide a general `toInt_umod` lemmas, but
instead choose to provide more specialized rewrites, with extra
side-conditions.

* [#6431](https://github.com/leanprover/lean4/pull/6431) fixes the `Repr` instance of the `Timestamp` type and changes
the `PlainTime` type so that it always represents a clock time that may
be a leap second.

* [#6476](https://github.com/leanprover/lean4/pull/6476) defines `reverse` for bitvectors and implements a first subset
of theorems (`getLsbD_reverse, getMsbD_reverse, reverse_append,
reverse_replicate, reverse_cast, msb_reverse`). We also include some
necessary related theorems (`cons_append, cons_append_append,
append_assoc, replicate_append_self, replicate_succ'`) and deprecate
theorems`replicate_zero_eq` and `replicate_succ_eq`.

* [#6494](https://github.com/leanprover/lean4/pull/6494) proves the basic theorems about the functions `Int.bdiv` and
`Int.bmod`.

* [#6507](https://github.com/leanprover/lean4/pull/6507) adds the subtraction equivalents for `Int.emod_add_emod` (`(a %
n + b) % n = (a + b) % n`) and `Int.add_emod_emod` (`(a + b % n) % n =
(a + b) % n`). These are marked @[simp] like their addition equivalents.

* [#6524](https://github.com/leanprover/lean4/pull/6524) upstreams some remaining `List.Perm` lemmas from Batteries.

* [#6546](https://github.com/leanprover/lean4/pull/6546) continues aligning `Array` and `Vector` lemmas with `List`,
working on `fold` and `map` operations.

* [#6563](https://github.com/leanprover/lean4/pull/6563) implements `Std.Net.Addr` which contains structures around IP
and socket addresses.

* [#6573](https://github.com/leanprover/lean4/pull/6573) replaces the existing implementations of `(D)HashMap.alter` and
`(D)HashMap.modify` with primitive, more efficient ones and in
particular provides proofs that they yield well-formed hash maps (`WF`
typeclass).

* [#6586](https://github.com/leanprover/lean4/pull/6586) continues aligning `List/Array/Vector` lemmas, finishing up
lemmas about `map`.

* [#6587](https://github.com/leanprover/lean4/pull/6587) adds decidable instances for the `LE` and `LT` instances for the
`Offset` types defined in `Std.Time`.

* [#6589](https://github.com/leanprover/lean4/pull/6589) continues aligning `List/Array` lemmas, finishing `filter` and
`filterMap`.

* [#6591](https://github.com/leanprover/lean4/pull/6591) adds less-than and less-than-or-equal-to relations to `UInt32`,
consistent with the other `UIntN` types.

* [#6612](https://github.com/leanprover/lean4/pull/6612) adds lemmas about `Array.append`, improving alignment with the
`List` API.

* [#6617](https://github.com/leanprover/lean4/pull/6617) completes alignment of `List`/`Array`/`Vector` `append` lemmas.

* [#6620](https://github.com/leanprover/lean4/pull/6620) adds lemmas about HashMap.alter and .modify. These lemmas
describe the interaction of alter and modify with the read methods of
the HashMap. The additions affect the HashMap, the DHashMap and their
respective raw versions. Moreover, the raw versions of alter and modify
are defined.

* [#6625](https://github.com/leanprover/lean4/pull/6625) adds lemmas describing the behavior of `UIntX.toBitVec` on
`UIntX` operations.

* [#6630](https://github.com/leanprover/lean4/pull/6630) adds theorems `Nat.[shiftLeft_or_distrib`,
shiftLeft_xor_distrib`, shiftLeft_and_distrib`, `testBit_mul_two_pow`,
`bitwise_mul_two_pow`, `shiftLeft_bitwise_distrib]`, to prove
`Nat.shiftLeft_or_distrib` by emulating the proof strategy of
`shiftRight_and_distrib`.

* [#6640](https://github.com/leanprover/lean4/pull/6640) completes aligning `List`/`Array`/`Vector` lemmas about
`flatten`. `Vector.flatten` was previously missing, and has been added
(for rectangular sizes only). A small number of missing `Option` lemmas
were also need to get the proofs to go through.

* [#6660](https://github.com/leanprover/lean4/pull/6660) defines `Vector.flatMap`, changes the order of arguments in
`List.flatMap` for consistency, and aligns the lemmas for
`List`/`Array`/`Vector` `flatMap`.

* [#6661](https://github.com/leanprover/lean4/pull/6661) adds array indexing lemmas for `Vector.flatMap`. (These were not
available for `List` and `Array` due to variable lengths.)

* [#6667](https://github.com/leanprover/lean4/pull/6667) aligns `List.replicate`/`Array.mkArray`/`Vector.mkVector`
lemmas.

* [#6668](https://github.com/leanprover/lean4/pull/6668) fixes negative timestamps and `PlainDateTime`s before 1970.

* [#6674](https://github.com/leanprover/lean4/pull/6674) adds theorems `BitVec.[getMsbD_mul, getElem_udiv, getLsbD_udiv,
getMsbD_udiv]`

* [#6695](https://github.com/leanprover/lean4/pull/6695) aligns `List/Array/Vector.reverse` lemmas.

* [#6697](https://github.com/leanprover/lean4/pull/6697) changes the arguments of `List/Array.mapFinIdx` from `(f : Fin
as.size → α → β)` to `(f : (i : Nat) → α → (h : i < as.size) → β)`, in
line with the API design elsewhere for `List/Array`.

* [#6701](https://github.com/leanprover/lean4/pull/6701) completes aligning `mapIdx` and `mapFinIdx` across
`List/Array/Vector`.

* [#6707](https://github.com/leanprover/lean4/pull/6707) completes aligning lemmas for `List` / `Array` / `Vector` about
`foldl`, `foldr`, and their monadic versions.

* [#6708](https://github.com/leanprover/lean4/pull/6708) deprecates `List.iota`, which we make no essential use of. `iota
n` can be replaced with `(range' 1 n).reverse`. The verification lemmas
for `range'` already have better coverage than those for `iota`.
Any downstream projects using it (I am not aware of any) are encouraged
to adopt it.

* [#6712](https://github.com/leanprover/lean4/pull/6712) aligns `List`/`Array`/`Vector` theorems for `countP` and
`count`.

* [#6723](https://github.com/leanprover/lean4/pull/6723) completes the alignment of
{List/Array/Vector}.{attach,attachWith,pmap} lemmas. I had to fill in a
number of gaps in the List API.

* [#6728](https://github.com/leanprover/lean4/pull/6728) removes theorems `Nat.mul_one` to simplify a rewrite in the
proof of `BitVec.getMsbD_rotateLeft_of_lt`

* [#6742](https://github.com/leanprover/lean4/pull/6742) adds the lemmas that show what happens when multiplying by
`twoPow` to an arbitrary term, as well to another `twoPow`.

* [#6743](https://github.com/leanprover/lean4/pull/6743) adds rewrites that normalizes left shifts by extracting bits and
concatenating zeroes. If the shift amount is larger than the bit-width,
then the resulting bitvector is zero.

* [#6747](https://github.com/leanprover/lean4/pull/6747) adds the ability to push `BitVec.extractLsb` and
`BitVec.extractLsb'` with bitwise operations. This is useful for
constant-folding extracts.

* [#6767](https://github.com/leanprover/lean4/pull/6767) adds lemmas to rewrite
`BitVec.shiftLeft,shiftRight,sshiftRight'` by a `BitVec.ofNat` into a
shift-by-natural number. This will be used to canonicalize shifts by
constant bitvectors into shift by constant numbers, which have further
rewrites on them if the number is a power of two.

* [#6799](https://github.com/leanprover/lean4/pull/6799) adds a number of simple comparison lemmas to the top/bottom
element for BitVec. Then they are applied to teach bv_normalize that
`(a<1) = (a==0)` and to remove an intermediate proof that is no longer
necessary along the way.

* [#6800](https://github.com/leanprover/lean4/pull/6800) uniformizes the naming of `enum`/`enumFrom` (on `List`) and
`zipWithIndex` (on `Array` on `Vector`), replacing all with `zipIdx`. At
the same time, we generalize to add an optional `Nat` parameter for the
initial value of the index (which previously existed, only for `List`,
as the separate function `enumFrom`).

* [#6808](https://github.com/leanprover/lean4/pull/6808) adds simp lemmas replacing `BitVec.setWidth'` with `setWidth`,
and conditionally simplifying `setWidth v (setWidth w v)`.

* [#6818](https://github.com/leanprover/lean4/pull/6818) adds a BitVec lemma that `(x >> x) = 0` and plumbs it through to
bv_normalize. I also move some theorems I found useful to the top of the
ushiftRight section.

* [#6821](https://github.com/leanprover/lean4/pull/6821) adds basic lemmas about `Ordering`, describing the interaction
of `isLT`/`isLE`/`isGE`/`isGT`, `swap` and the constructors.
Additionally, it refactors the instance derivation code such that a
`LawfulBEq Ordering` instance is also derived automatically.

* [#6826](https://github.com/leanprover/lean4/pull/6826) adds injectivity theorems for inductives that did not get them
automatically (because they are defined too early) but also not yet
manuall later.

* [#6828](https://github.com/leanprover/lean4/pull/6828) adds add/sub injectivity lemmas for BitVec, and then adds
specialized forms with additional symmetries for the `bv_normalize`
normal form.

* [#6831](https://github.com/leanprover/lean4/pull/6831) completes the alignment of `List/Array/Vector` lemmas about
`isEqv` and `==`.

* [#6833](https://github.com/leanprover/lean4/pull/6833) makes the signatures of `find` functions across
`List`/`Array`/`Vector` consistent. Verification lemmas will follow in
subsequent PRs.

* [#6835](https://github.com/leanprover/lean4/pull/6835) fills some gaps in the `Vector` API, adding `mapM`, `zip`, and
`ForIn'` and `ToStream` instances.

* [#6838](https://github.com/leanprover/lean4/pull/6838) completes aligning the (limited) verification API for
`List/Array/Vector.ofFn`.

* [#6840](https://github.com/leanprover/lean4/pull/6840) completes the alignment of
`List/Array/Vector.zip/zipWith/zipWithAll/unzip` lemmas.

* [#6845](https://github.com/leanprover/lean4/pull/6845) adds missing monadic higher order functions on
`List`/`Array`/`Vector`. Only the most basic verification lemmas
(relating the operations on the three container types) are provided for
now.

* [#6848](https://github.com/leanprover/lean4/pull/6848) adds simp lemmas proving `x + y = x ↔ x = 0` for BitVec, along
with symmetries, and then adds these to the bv_normalize simpset.

* [#6860](https://github.com/leanprover/lean4/pull/6860) makes `take`/`drop`/`extract` available for each of
`List`/`Array`/`Vector`. The simp normal forms differ, however: in
`List`, we simplify `extract` to `take+drop`, while in `Array` and
`Vector` we simplify `take` and `drop` to `extract`. We also provide
`Array/Vector.shrink`, which simplifies to `take`, but is implemented by
repeatedly popping. Verification lemmas for `Array/Vector.extract` to
follow in a subsequent PR.

* [#6862](https://github.com/leanprover/lean4/pull/6862) defines Cooper resolution with a divisibility constraint as
formulated in
"Cutting to the Chase: Solving Linear Integer Arithmetic" by Dejan
Jovanović and Leonardo de Moura,
DOI 10.1007/s10817-013-9281-x.

* [#6863](https://github.com/leanprover/lean4/pull/6863) allows fixing regressions in mathlib introduced in
nightly-2024-02-25 by allowing the use of `x * y` in match patterns.
There are currently 11 instances in mathlib explicitly flagging the lack
of this match pattern.

* [#6864](https://github.com/leanprover/lean4/pull/6864) adds lemmas relating the operations on
findIdx?/findFinIdx?/idxOf?/findIdxOf?/eraseP/erase on List and on
Array. It's preliminary to aligning the verification lemmas for
`find...` and `erase...`.

* [#6868](https://github.com/leanprover/lean4/pull/6868) completes the alignment across `List/Array/Vector` of lemmas
about the `eraseP/erase/eraseIdx` operations.

* [#6872](https://github.com/leanprover/lean4/pull/6872) adds lemmas for xor injectivity and when and/or/xor equal
allOnes or zero. Then I plumb support for the new lemmas through to
bv_normalize.

* [#6875](https://github.com/leanprover/lean4/pull/6875) adds a lemma relating `msb` and `getMsbD`, and three lemmas
regarding `getElem` and `shiftConcat`. These lemmas were needed in
[Batteries#1078](https://github.com/leanprover-community/batteries/pull/1078)
and the request to upstream was made in the review of that PR.

* [#6878](https://github.com/leanprover/lean4/pull/6878) completes alignments of `List/Array/Vector` lemmas about
`range`, `range'`, and `zipIdx`.

* [#6883](https://github.com/leanprover/lean4/pull/6883) completes the alignment of lemmas about monadic functions on
`List/Array/Vector`. Amongst other changes, we change the simp normal
form from `List.forM` to `ForM.forM`, and correct the definition of
`List.flatMapM`, which previously was returning results in the incorrect
order. There remain many gaps in the verification lemmas for monadic
functions; this PR only makes the lemmas uniform across
`List/Array/Vector`.

* [#6890](https://github.com/leanprover/lean4/pull/6890) teaches bv_normalize to replace subtractions on one side of an
equality with an addition on the other side, this re-write eliminates a
not + addition in the normalized form so it is easier on the solver.

* [#6912](https://github.com/leanprover/lean4/pull/6912) aligns current coverage of `find`-type theorems across
`List`/`Array`/`Vector`. There are still quite a few holes in this API,
which will be filled later.

## Compiler

* [#6535](https://github.com/leanprover/lean4/pull/6535) avoids a linker warning on Windows.

* [#6547](https://github.com/leanprover/lean4/pull/6547) should prevent Lake from accidentally picking up other linkers
installed on the machine.

* [#6574](https://github.com/leanprover/lean4/pull/6574) actually prevents Lake from accidentally picking up other
toolchains installed on the machine.

* [#6664](https://github.com/leanprover/lean4/pull/6664) changes the toMono pass to longer filter out type class
instances, because they may actually be needed for later compilation.

* [#6665](https://github.com/leanprover/lean4/pull/6665) adds a new lcAny constant to Prelude, which is meant for use in
LCNF to represent types whose dependency on another term has been erased
during compilation. This is in addition to the existing lcErased
constant, which represents types that are irrelevant.

* [#6678](https://github.com/leanprover/lean4/pull/6678) modifies LCNF.toMonoType to use a more refined type erasure
scheme, which distinguishes between irrelevant/erased information
(represented by lcErased) and erased type dependencies (represented by
lcAny). This corresponds to the irrelevant/object distinction in the old
code generator.

* [#6680](https://github.com/leanprover/lean4/pull/6680) makes the new code generator skip generating code for decls with
an implemented_by decl, just like the old code generator.

* [#6757](https://github.com/leanprover/lean4/pull/6757) adds support for applying crimp theorems in toLCNF.

* [#6758](https://github.com/leanprover/lean4/pull/6758) prevents deadlocks from non-cyclical task waits that may
otherwise occur during parallel elaboration with small threadpool sizes.

* [#6837](https://github.com/leanprover/lean4/pull/6837) adds Float32 to the LCNF builtinRuntimeTypes list. This was
missed during the initial Float32 implementation, but this omission has
the side effect of lowering Float32 to obj in the IR.

## Pretty Printing

* [#6703](https://github.com/leanprover/lean4/pull/6703) modifies the delaborator so that in `pp.tagAppFns` mode,
generalized field notation is tagged with the head constant. The effect
is that docgen documentation will linkify dot notation. Internal change:
now formatted `rawIdent` can be tagged.

* [#6716](https://github.com/leanprover/lean4/pull/6716) renames the option `infoview.maxTraceChildren` to
`maxTraceChildren` and applies it to the cmdline driver and language
server clients lacking an info view as well. It also implements the
common idiom of the option value `0` meaning "unlimited".

* [#6729](https://github.com/leanprover/lean4/pull/6729) makes the pretty printer for `.coeFun`-tagged functions respect
`pp.tagAppFns`. The effect is that in docgen, when an expression pretty
prints as `f x y z` with `f` a coerced function, then if `f` is a
constant it will be linkified.

* [#6730](https://github.com/leanprover/lean4/pull/6730) changes how app unexpanders are invoked. Before the ref was
`.missing`, but now the ref is the head constant's delaborated syntax.
This way, when `pp.tagAppFns` is true, then tokens in app unexpanders
are annotated with the head constant. The consequence is that in docgen,
tokens will be linkified. This new behavior is consistent with how
`notation` defines app unexpanders.

## Documentation

* [#6549](https://github.com/leanprover/lean4/pull/6549) fixes #6548.

* [#6638](https://github.com/leanprover/lean4/pull/6638) correct the docstring of theorem `Bitvec.toNat_add_of_lt`

* [#6643](https://github.com/leanprover/lean4/pull/6643) changes the macOS docs to indicate that Lean now requires
pkgconf to build.

* [#6646](https://github.com/leanprover/lean4/pull/6646) changes the ubuntu docs to indicate that Lean now requires
pkgconf to build.

* [#6738](https://github.com/leanprover/lean4/pull/6738) updates our lexical structure documentation to mention the newly
supported ⱼ which lives in a separate unicode block and is thus not
captured by the current ranges.

* [#6885](https://github.com/leanprover/lean4/pull/6885) fixes the name of the truncating integer division function in
the `HDiv.hDiv` docstring (which is shown when hovering over `/`). It
was changed from `Int.div` to `Int.tdiv` in #5301.

## Server

* [#6597](https://github.com/leanprover/lean4/pull/6597) fixes the indentation of nested traces nodes in the info view.

* [#6794](https://github.com/leanprover/lean4/pull/6794) fixes a significant auto-completion performance regression that
was introduced in #5666, i.e. v4.14.0.

## Lake

* [#6290](https://github.com/leanprover/lean4/pull/6290) uses `StateRefT` instead of `StateT` to equip the Lake build
monad with a build store.

* [#6323](https://github.com/leanprover/lean4/pull/6323) adds a new Lake CLI command, `lake query`, that both builds
targets and outputs their results. It can produce raw text or JSON
-formatted output (with `--json` / `-J`).

* [#6418](https://github.com/leanprover/lean4/pull/6418) alters all builtin Lake facets to produce `Job` objects.

* [#6627](https://github.com/leanprover/lean4/pull/6627) aims to fix the trace issues reported by Mathlib that are
breaking `lake exe cache` in downstream projects.

* [#6631](https://github.com/leanprover/lean4/pull/6631) sets `MACOSX_DEPLOYMENT_TARGET` for shared libraries (it was
previously only set for executables).

* [#6771](https://github.com/leanprover/lean4/pull/6771) enables `FetchM` to be run from `JobM` / `SpawnM` and
vice-versa. This allows calls of `fetch` to asynchronously depend on the
outputs of other jobs.

* [#6780](https://github.com/leanprover/lean4/pull/6780) makes all targets and all `fetch` calls produce a `Job` of some
value. As part of this change, facet definitions (e.g., `library_data`,
`module_data`, `package_data`) and Lake type families (e.g.,
`FamilyOut`) should no longer include `Job` in their types (as this is
now implicit).

* [#6798](https://github.com/leanprover/lean4/pull/6798) deprecates the `-U` shorthand for the `--update` option.

* [#7209](https://github.com/leanprover/lean4/pull/7209) fixes broken Lake tests on Windows' new MSYS2. As of MSYS2
0.0.20250221, `OSTYPE` is now reported as `cygwin` instead of `msys`, which must be accounted for in a few Lake tests.

## Other

* [#6479](https://github.com/leanprover/lean4/pull/6479) speeds up JSON serialisation by using a lookup table to check
whether a string needs to be escaped.

* [#6519](https://github.com/leanprover/lean4/pull/6519) adds a script to automatically generate release notes using the
new `changelog-*` labels and "..." conventions.

* [#6542](https://github.com/leanprover/lean4/pull/6542) introduces a script that automates checking whether major
downstream repositories have been updated for a new toolchain release.

````
