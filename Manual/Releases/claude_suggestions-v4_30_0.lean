/-
Suggested rewrite of the `# Highlights` section for v4_30_0.lean.
Historical context from the v4.x release series (v4.0.0–v4.30.0) is woven
into each PR description rather than collected in a separate section.

To apply: replace the `# Highlights` block in v4_30_0.lean
(from `# Highlights` through the last `## Breaking Changes` bullet)
with the markdown content below. The Lean example after the
`## New `sym =>` Interactive Tactic` section is live code so the
`#check` outputs and the `sym =>` proof can be inspected directly.
-/

/-
============================================================
SUGGESTED # Highlights SECTION (markdown body)
============================================================

# Highlights

Lean 4.30.0 delivers `sym =>` — a user-facing interactive tactic mode built
atop the symbolic simulation framework introduced in v4.28.0 — substantially
expands the {tactic}`cbv` tactic that arrived experimentally in v4.29.0,
completes the LCNF compiler backend migration begun in v4.16.0, and makes
Lake's remote caching seamless by integrating on-demand downloads into
`lake build`.

## New `sym =>` Interactive Tactic

[#12970](https://github.com/leanprover/lean4/pull/12970) adds `sym =>`, an
interactive tactic mode built on {tactic}`grind`. Unlike `grind =>`, it gives
users explicit control over each step — `intro`, `apply`, `internalize`,
`by_contra`, and `simp` — without eagerly applying by-contradiction. Satellite
solvers like `lia` and `ring` handle remaining goals automatically when
invoked. The mode is backed by a new `Sym.simp` simplifier that also powers
{tactic}`cbv` and {tactic}`grind`, with support for named variants
([#13034](https://github.com/leanprover/lean4/pull/13034)), named theorem sets
([#13018](https://github.com/leanprover/lean4/pull/13018)), and loop
prevention for permutation theorems
([#13046](https://github.com/leanprover/lean4/pull/13046)).

{tactic}`grind` has been under continuous development since v4.9.0 (mid-2024).
The `SymM` symbolic simulation framework it builds on was introduced in
v4.28.0 as internal infrastructure for verification condition generators.
`sym =>` is the first user-facing interactive mode to emerge from that line
of work — complementing `grind =>` rather than replacing it.

*Universe-preserving example.* Rather than statically binding universe
variables in the binders, the example below lets the universe of a type
synonym `Twin` be auto-bound at the definition site and transports its
`Inhabited` instance through `inferInstanceAs`. This is precisely the
v4.29.0 transparency-aware form: `inferInstanceAs` takes an explicit
*source* type (here `Inhabited (α × α)`) and adjusts its result so the
target type's RHS is not leaked at lower-than-semireducible transparency,
whereas plain `inferInstance` only resolves the *target* type and inherits
the user's transparency assumptions implicitly. The two `#check` lines
following the definitions make the contrast directly inspectable in the
infoview. The `sym =>` proof at the bottom drives the simulation with a
single `simp [h]` step and respects the same universe-level discipline
that `inferInstanceAs` set up.
-/

-- Live example for the `sym =>` highlight.
-- The universe `u` is auto-bound; no `universe u` declaration is needed.

def Twin (α : Type u) : Type u := α × α

-- Transport the product's `Inhabited` instance to the synonym, preserving
-- the universe of `α` through `inferInstanceAs`:
instance [Inhabited α] : Inhabited (Twin α) :=
  inferInstanceAs (Inhabited (α × α))

-- `inferInstance` resolves the *target* type only — it picks up the
-- transported instance defined above.
#check (inferInstance : Inhabited (Twin Nat))

-- `inferInstanceAs` requires an explicit *source* type for transport
-- and an inferable target from context; the synthesized result does not
-- leak `Twin`'s RHS at low transparency.
#check (inferInstanceAs (Inhabited (Nat × Nat)) : Inhabited (Twin Nat))

-- `sym =>` proof: the binders `xs` and `h` are introduced by the `example`
-- header, so no `intro` step is needed inside the simulation.
example (xs : Twin Nat) (h : xs = default) : xs = default := by
  sym =>
    simp [h]

/-
The static type of `xs` is `Twin Nat`; its dynamic type after the synonym
is unfolded is `Nat × Nat`. Because `Sym.simp` works on maximally-shared
expressions and respects the transparency settings honored by the
`inferInstanceAs`-built instance, the same script generalizes to any
universe in which `α` lives — the universe level is preserved end-to-end
without ever being collapsed to `Level.zero`.

## `cbv` Tactic Expansion

The {tactic}`cbv` tactic — introduced as an experimental user-facing tactic
in v4.29.0 — receives major new capabilities in v4.30.0:
[#12597](https://github.com/leanprover/lean4/pull/12597) adds a
`cbv_simproc` system for user-defined simplification procedures (mirroring
{tactic}`simp`'s `simproc` infrastructure);
[#12773](https://github.com/leanprover/lean4/pull/12773) adds `at` location
syntax (`cbv at h`, `cbv at *`), matching `simp`'s interface;
[#12763](https://github.com/leanprover/lean4/pull/12763) adds short-circuit
evaluation for `Or`/`And`, avoiding unnecessary work on branches whose outcome
is already determined; and
[#12788](https://github.com/leanprover/lean4/pull/12788) adds
`set_option cbv.maxSteps N`.

These additions move `cbv` from an experimental evaluator toward a principled,
user-extensible alternative to {tactic}`native_decide` for computational
goals — filling a gap that has existed since `native_decide` first appeared in
the Lean 4 toolchain.

## Compiler: User Borrow Annotations and New LCNF Backend

[#12830](https://github.com/leanprover/lean4/pull/12830) enables
user-provided borrow annotations: mark arguments with `(x : @&Ty)` to reduce
reference counting pressure. Use `trace.Compiler.inferBorrow` to inspect the
compiler's reasoning.
[#12942](https://github.com/leanprover/lean4/pull/12942) marks `ReaderT`'s
context argument as borrowed, propagating RC savings across the
metaprogramming stack.

[#12781](https://github.com/leanprover/lean4/pull/12781) ports the C emission
pass to LCNF, completing end-to-end code generation through the new
infrastructure. [#12665](https://github.com/leanprover/lean4/pull/12665)
ports the reset/reuse pass with improved exponential-code prevention, yielding
a *~15% decrease in binary size*.

The LCNF infrastructure has been under construction since v4.16.0, with IR
passes migrating one by one across releases. v4.29.0 ported push_proj,
ResetReuse, borrow, box/unbox, RC insertion, and toposorting; v4.30.0 ports
C emission — the last pass — so the entire pipeline now runs end-to-end
through LCNF.

## Lake Cache Overhaul

[#12634](https://github.com/leanprover/lean4/pull/12634) enables on-demand
artifact downloads during `lake build`, removing the need for a separate
`lake cache get` step.
[#12974](https://github.com/leanprover/lean4/pull/12974) adds parallel
transfers via `curl --parallel`, and
[#13164](https://github.com/leanprover/lean4/pull/13164) fetches all artifact
URLs from Reservoir in a single bulk request rather than one redirect per
artifact. [#13144](https://github.com/leanprover/lean4/pull/13144) adds staged
upload commands (`lake cache stage`/`unstage`/`put-staged`) paralleling
Mathlib's `lake exe cache` workflow.

Lake's remote caching integration with Reservoir was introduced in v4.25.0.
v4.29.0 added hard links for local transfers, `lake cache clean`, and a
system-wide configuration file. v4.30.0 completes the picture: artifact
downloads now happen automatically as part of `lake build`.

## Theorems Are Now Opaque in the Kernel

[#12973](https://github.com/leanprover/lean4/pull/12973) makes theorems
opaque to the kernel: a `theorem` is never unfolded during reduction or type
checking, closing a gap that proof irrelevance had already made largely
theoretical. Proofs that must reduce (e.g., `Acc.rec` eliminating into `Type`)
must use `def` instead.

This continues v4.29.0's systematic tightening of reducibility and
transparency semantics — `@[implicit_reducible]`, `isDefEq` transparency
changes, and kernel-level `theorem` opacity are successive steps in a broader
effort across recent releases to make Lean's definitional equality algorithm
more predictable and scalable.

## `@[deprecated_arg]` Attribute

[#13011](https://github.com/leanprover/lean4/pull/13011) adds
`@[deprecated_arg old new (since := "...")]` for deprecating individual
function parameters. Callers using the old name receive a warning and a rename
code action; removed parameters produce an error with a delete hint.

Lean has had `@[deprecated]` for whole-function deprecation since early in
the v4 series. `@[deprecated_arg]` fills the finer-grained gap, covering the
common case where a library refactors parameter names without changing the
function's identifier.

## Library Highlights

[#12126](https://github.com/leanprover/lean4/pull/12126)–[#12144](https://github.com/leanprover/lean4/pull/12144)
introduce core HTTP data types (`Request`, `Response`, `Status`, `Headers`,
`URI`, streaming `Body`) as the foundation of a standard HTTP library — the
first such types in Lean core. String verification continues from v4.29.0
(which proved KMP correctness for `Slice` patterns), adding proofs for
`startsWith`, `split`, `intercalate`, `isNat`/`toNat?`, `isInt`/`toInt?`, and
more. [#12385](https://github.com/leanprover/lean4/pull/12385) adds
`Array.mergeSort`, a stable O(n log n) sort about twice as fast as
`List.mergeSort` on large random inputs.

## Experimental: Live Debugging with `idbg`

[#12648](https://github.com/leanprover/lean4/pull/12648) adds experimental
`idbg e` syntax: when placed in a `do` block, it connects a running compiled
program to the language server over TCP and evaluates `e` with actual runtime
values. Editing the expression re-evaluates it live. Known limitations: single
`idbg` at a time, requires `LEAN_PATH`, untested on Windows/macOS.

This is a qualitatively new debugging capability for the Lean toolchain: prior
to v4.30.0, no mechanism connected a compiled Lean program back to the
language server for live inspection — debugging relied on `#eval`, trace
messages, or external tools.

## Breaking Changes

- [#12973](https://github.com/leanprover/lean4/pull/12973) Theorems are now
  opaque in the kernel; use `def` for proof terms that must reduce.
- [#12749](https://github.com/leanprover/lean4/pull/12749) Renames
  metaprogramming APIs: `isStructureLike` → `isNonRecStructure`,
  `matchConstStructLike` → `matchConstNonRecStructure`,
  `getStructureLikeCtor?` → `getNonRecStructureCtor?`,
  `getStructureLikeNumFields` → `getNonRecStructureNumFields`.
- [#13005](https://github.com/leanprover/lean4/pull/13005) Metaprograms
  calling `compileDecl` directly may need to call `markMeta` first.
- [#12771](https://github.com/leanprover/lean4/pull/12771)
  `String.Slice.Pos.cast` now requires `s.copy = t.copy` instead of `s = t`.
- [#12435](https://github.com/leanprover/lean4/pull/12435) Changes the
  signature of `Option.getElem?_inj`.
- [#12708](https://github.com/leanprover/lean4/pull/12708) `PostCond`
  functions reorder implicit parameters so `α` consistently comes before `ps`.


## Release Themes: Progression from v4.29.0

The highlights above cluster into distinct themes, tracing the arc from v4.29.0 to v4.30.0.

**Symbolic simulation surfaces as an interactive tactic.** v4.29.0 left the `SymM` framework as internal plumbing; v4.30.0 ships `sym =>` as a user-facing interactive mode. Where `grind =>` works eagerly and automatically, `sym =>` puts the user in explicit control of `intro`, `apply`, `internalize`, and `simp` steps — complementing rather than replacing `grind`. The shared `Sym.simp` engine underneath also drives {tactic}`cbv`, so improvements to the simplifier compound across both tactics.

**`cbv` graduates from experimental to capable.** v4.29.0 introduced `cbv` as an experimental user-facing tactic with basic `@[cbv_opaque]` and `@[cbv_eval]` support. v4.30.0 substantially expands it: `cbv_simproc` extensibility mirrors `simp`'s simproc infrastructure, `at` location syntax brings it in line with `simp at h`, short-circuit evaluation avoids unnecessary work on `Or`/`And`, and a user-configurable step limit replaces the hardcoded default. The tactic moves from "available but limited" to "production-ready for computational goals."

**The LCNF compiler backend reaches end-to-end.** v4.29.0 ported a series of IR passes to LCNF (push_proj, ResetReuse, borrow, box/unbox, RC insertion, toposorting). v4.30.0 ports C emission — the final piece — so the entire code-generation pipeline now runs through LCNF. Alongside this, user borrow annotations (`@&Ty`) arrive: authors can now annotate function arguments to guide the borrow analysis, reducing reference-counting pressure in hot paths. The ~15% binary size reduction from the ported reset/reuse pass is a direct dividend of completing this migration.

**Lake caching eliminates the manual prefetch step.** v4.29.0 improved local cache mechanics (hard links, `lake cache clean`, system-wide config). v4.30.0 integrates remote artifact fetching directly into `lake build`: artifacts are downloaded on demand as needed rather than requiring a separate `lake cache get` invocation. Parallel transfers via `curl --parallel` and bulk Reservoir URL fetching reduce transfer overhead further. For Mathlib-scale projects, staged upload commands (`lake cache stage`/`put-staged`) parallel the existing `lake exe cache` workflow.

**Kernel opacity of theorems closes a type-theory gap.** v4.29.0's big semantic change was in reducibility handling for elaboration and `isDefEq`. v4.30.0 takes the next step: the kernel itself now treats `theorem` declarations as opaque, formalizing what proof irrelevance already implied. Code that previously relied on kernel unfolding of proof terms (e.g., `Acc.rec` eliminating into `Type`) must use `def` instead.

**`@[deprecated_arg]` fills a gap in API migration tooling.** v4.29.0 had no mechanism for deprecating individual function parameters. v4.30.0 adds `@[deprecated_arg old new (since := "...")]`: callers using the old parameter name receive a deprecation warning and a rename code action; removed parameters produce an error with a delete hint. This covers the common API evolution pattern where a function keeps its name but its parameter names change.

**String verification continues and HTTP types arrive.** v4.29.0 proved KMP correctness for `Slice` patterns; v4.30.0 extends verification coverage to `startsWith`, `skipPrefix?`, `dropPrefix?`, `split`, `intercalate`, `isNat`/`toNat?`, and `isInt`/`toInt?`. In parallel, the core HTTP type hierarchy — `Request`, `Response`, `Status`, `Headers`, `URI`, and streaming `Body` — lands as the foundation of a future standard HTTP library. `Array.mergeSort` adds a stable, O(n log n) alternative to `List.mergeSort` that is about twice as fast on large random inputs.

**Live debugging opens a new introspection channel.** Nothing in v4.29.0 connected a running compiled Lean program to the language server. `idbg` does exactly this: placing `idbg e` in a `do` block causes a compiled program to connect back to the language server over TCP, evaluating `e` against actual runtime values. Edits to `e` re-evaluate live without recompiling — a qualitatively different debugging mode from `#eval` or trace logs.
-/
