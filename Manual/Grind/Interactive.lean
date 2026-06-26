/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

#doc (Manual) "Interactive Mode" =>
%%%
tag := "grind-interactive"
%%%

Because {tactic}`grind` relies on the current set of {ref "e-matching"}[annotated lemmas], proofs may stop working or take longer to process when library annotations change.
Additionally, as it searches for a proof, {tactic}`grind` may attempt many steps that don't contribute to the final result, which can take time.
A script can replace {tactic}`grind`'s search, leading it directly down the successful proof path and instantiating precisely those lemmas that actually contribute to the proof.
Rechecking such a proof is both faster and more resilient to library changes.
This script feature is called {tactic}`grind`'s {deftech}_interactive mode_, and scripts are written in a special-purpose tactic language.

A script for {tactic}`grind`'s interactive mode consists of {keywordOf Lean.Parser.Tactic.grind}`grind =>` followed by an indented block of {tactic}`grind` tactics.
Each of these tactics runs one of {tactic}`grind`'s engines, instantiates a theorem, performs a case split, inspects the shared state, or manages the remaining goals.
The steps operate on the same “whiteboard” that the automatic search uses: the equalities, inequalities, and Boolean facts that all prior steps have discovered, together with the equivalence classes derived from them.

Interactive mode can also be used to understand why {tactic}`grind` is unable to complete a proof.
The {ref "grind-interactive-inspect"}[inspection tactics] reveal the current state of the whiteboard, which may make it possible to notice a missing theorem instantiation or case split that a few explicit steps or an additional annotation in a library can supply.
An explicit script can also make it easier for readers to understand _why_ {tactic}`grind` succeeds.

:::example "Reading a `grind?` Proof"

The structure {lean}`Two` can be thought of as a two-element array, indexed by {name}`Bool` instead of {name}`Nat`.
```lean
structure Two α where
  fst : α
  snd : α

namespace Two

def get (xs : Two α) (i : Bool) : α :=
  if i then xs.fst else xs.snd
```

The API for {name}`Two` includes a number of lemmas, annotated for use with {tactic}`grind`:
```lean
def both (x : α) : Two α := ⟨x, x⟩

def map (f : α → β) (xs : Two α) : Two β := ⟨f xs.fst, f xs.snd⟩

@[ext, grind ext]
theorem ext_get {xs ys : Two α}
    (h : ∀ i, xs.get i = ys.get i) : xs = ys := by
  cases xs; cases ys
  simp_all [get]

@[grind =]
theorem get_def {xs : Two α} {i} :
    xs.get i = if i then xs.fst else xs.snd := rfl

@[grind =]
theorem map_fst {f : α → β} {xs} :
    (map f xs).fst = f xs.fst := rfl

@[grind =]
theorem map_snd {f : α → β} {xs} :
    (map f xs).snd = f xs.snd := rfl

@[grind =]
theorem both_fst {x : α} : (both x).fst = x := rfl

@[grind =]
theorem both_snd {x : α} : (both x).snd = x := rfl

@[grind =]
theorem both_fst_eq_snd {x : α} :
    (both x).fst = (both x).snd := rfl
```

Using these lemmas, {tactic}`grind` can prove that {name}`Two.map` distributes over {name}`Two.both`.
Calling {tactic}`grind?` results in multiple suggestions for more specific calls to {tactic}`grind`, one of which is an interactive script:
```lean (name := mapBoth)
theorem map_both {x : α} {f : α → β} :
    (both x).map f = both (f x) := by
  grind?
```
```leanOutput mapBoth
Try these:
  [apply] grind only [= get_def, = both_fst, = map_fst, = both_snd, = map_snd, #1362, #ba8b]
  [apply] grind only [= get_def, = both_fst, = map_fst, = both_snd, = map_snd]
  [apply] grind =>
    cases #1362
    instantiate only [= get_def]
    cases #ba8b
    · instantiate only [= both_fst, = map_fst]
      instantiate only [= both_fst]
    · instantiate only [= both_snd, = map_snd]
      instantiate only [= both_snd]
```

The script makes the proof's two internal {ref "grind-interactive-cases"}[case splits] explicit.

During its search, {tactic}`grind` also instantiates {name}`Two.both_fst_eq_snd`, even though that equation contributes nothing to the proof.
Because it does not end up contributing to the result, none of the suggested {tactic}`grind` calls mention it; when rechecking these suggested versions, the overhead of this needless instantiation is avoided.
Setting the {option}`diagnostics` option reports how many times each theorem was instantiated:
```lean (name := mapBothDiag)
set_option diagnostics true in
set_option diagnostics.threshold 1 in
example {x : α} {f : α → β} : (both x).map f = both (f x) := by
  grind
```
```leanOutput mapBothDiag (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] both_snd ↦ 3
    [thm] both_fst ↦ 2
    [thm] both_fst_eq_snd ↦ 2
    [thm] get_def ↦ 2
    [thm] map_fst ↦ 1
    [thm] map_snd ↦ 1
  [split] Case splits
  [app] Applications
  [grind] Simplifier
    [simp] tried theorems (max: 15, num: 1):
    [simp] tried congruence theorems (max: 2, num: 1):
    use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
```

The suggested interactive-mode {tactic}`grind` does not instantiate {name}`Two.both_fst_eq_snd`:
```lean (name := mapBothDiag2)
set_option diagnostics true in
set_option diagnostics.threshold 1 in
example {x : α} {f : α → β} : (both x).map f = both (f x) := by
  grind =>
    cases #1362
    instantiate only [= get_def]
    cases #ba8b
    · instantiate only [= both_fst, = map_fst]
      instantiate only [= both_fst]
    · instantiate only [= both_snd, = map_snd]
      instantiate only [= both_snd]
```
```leanOutput mapBothDiag2 (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] both_fst ↦ 2
    [thm] both_snd ↦ 2
    [thm] get_def ↦ 2
    [thm] map_fst ↦ 1
    [thm] map_snd ↦ 1
  [split] Case splits
  [app] Applications
  [grind] Simplifier
    [simp] tried theorems (max: 13, num: 1):
    [simp] tried congruence theorems (max: 2, num: 1):
    use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
```
:::

# Entry Points
%%%
tag := "grind-interactive-entry"
%%%

There are two versions of {tactic}`grind`'s interactive mode.
The first, introduced with {keywordOf Lean.Parser.Tactic.grind}`grind =>`, is designed for controlling {tactic}`grind` and automatically takes certain steps that are needed for most proofs.
The other, introduced with {tactic}`sym`, allows a higher degree of manual control and is intended for use in symbolic simulation workflows.

When used with a script, {tactic}`grind` initializes the proof by introducing all hypotheses and then invoking proof by contradiction so the initial goal is always {name}`False`.
It then runs the script.

:::syntax tactic (title := "Interactive `grind`")
```grammar
grind $_:optConfig $[only]? $[ [ $[$p],* ] ]? => $steps
```
:::

Unlike {tactic}`grind`, the {tactic}`sym` tactic does not begin by introducing hypotheses or invoking proof by contradiction.
The author of the script has full control over the context and goal.

:::syntax tactic (title := "Symbolic Simulation")
```grammar
sym $_:optConfig $[only]? $[ [ $[$p],* ] ]? => $steps
```
:::

Both tactics accept the same configuration options, the {keywordOf Lean.Parser.Tactic.grind}`only` modifier, and the bracketed list of theorems and parameters that ordinary {tactic}`grind` accepts.
Certain features that are invoked automatically by {tactic}`grind` and manually in {tactic}`sym` have dedicated tactics that are described in the {ref "grind-sym"}[symbolic simulation mode section].

The {tactic}`grind?` tactic takes the same arguments as {tactic}`grind` but does not support entering interactive mode.
It {ref "grind-minimizing"}[suggests] an equivalent {keywordOf Lean.Parser.Tactic.grind}`grind only` call, as well as an equivalent script.
Within an interactive {tactic}`grind` script, the {grindTactic}`finish?` and {grindTactic}`cases?` tactics similarly suggest scripts.

# The `grind` Tactic Language
%%%
tag := "grind-interactive-steps"
%%%

The sequence of steps that follow {keywordOf Lean.Parser.Tactic.grind}`grind =>` is written in an indented block, with one step on each line; multiple steps may also be separated by `;`.
As an alternative to indentation, they may be enclosed in braces.
Such a sequence is represented by the syntax category {name Lean.Parser.Tactic.Grind.grindSeq}`grindSeq`.

Just as in an ordinary Lean tactic script, {tactic}`grind` tactics manipulate a {tech}[proof state] that consists of a sequence of {tech}[goals], each of which consists of a sequence of assumptions and a conclusion.
When there are no further goals, the proof is complete.
Most tactics operate on the {tech}[main goal], and {ref "grind-interactive-goals"}[goal-management tactics] redistribute goals across steps exactly as their ordinary tactic counterparts do.
Additionally, {tactic}`grind` tactics have access to the “whiteboard”.

## Anchors

Several tactics refer to entries on the whiteboard by an {deftech}_anchor_, written `#` followed by a hexadecimal number, as in `#1a`.
These anchors take the place of names: they identify a specific fact, equivalence class, or case-split candidate.
Anchors appear in the output of the inspection tactics or in filtered states.
The {grindTactic}`cases?` and {grindTactic}`show_cases` tactics report the anchors that {grindTactic}`cases` can act on.

An anchor is a stable hash of the term that it refers to.
It is computed from the term's structure while deliberately ignoring unstable implementation details such as internal names and instance arguments.
This means that anchors are insensitive to many unrelated proof changes, but they may change if the structure of the referenced term changes.
An anchor produced by {grindTactic}`cases?` can therefore be saved in a script file as long as the referenced candidate remains structurally the same.

```lean (name := anchorCanary) -show
-- Regression test: the anchor of `p ∨ q` is a stable hash; this pins its value so that any change
-- to the anchoring scheme is caught by the build.
example (p q : Prop) (h : p ∨ q) : q ∨ p := by
  sym =>
    internalize_all
    show_cases
    cases_next
    all_goals finish
```
```leanOutput anchorCanary -show
[splits] Case split candidates
  [split] #4283 := p ∨ q
```

## Filters

Any {tactic}`grind` tactic may be followed by `|` and a {deftech}_filter_ that selects some subset of the data in the {tactic}`grind` state.
The filtered state is then displayed both before and after the step runs, which is convenient for watching how a step changes the whiteboard.
If the filter after `|` is empty, then the entire state matches.

:::syntax grind_filter (title := "Generation Filters") (label := "grind filter")
```grammar
gen < $n
```
```grammar
gen ≤ $n
```
```grammar
gen <= $n
```
```grammar
gen = $n
```
```grammar
gen != $n
```
```grammar
gen ≥ $n
```
```grammar
gen >= $n
```
```grammar
gen > $n
```
These filters are satisfied when the {tech}[generation] of the entry satisfies the indicated comparison against the numeral.
  Lower generations correspond to facts discovered earlier in the search.
:::

:::syntax grind_filter (title := "Name Filters") (label := "grind filter")
```grammar
$x:ident
```
This filter is satisfied when the identifier is the name of a local hypothesis or global constant and it occurs in the term.
:::

:::syntax grind_filter (title := "Filter Expressions") (label := "grind filter")
```grammar
($f)
```
```grammar
$f && $f
```
```grammar
$f || $f
```
```grammar
!$f
```
Filters may be grouped with parentheses, negated, and combined with conjunction and disjunction.
Both conjunction and disjunction are left-associative and have the same precedence, so use explicit parentheses for grouping.
:::

:::example "Filters"
```lean
inductive Color where | red | green
inductive Fruit where | cherry | lime

example (peel pulp : Fruit → Color)
    (h1 : peel .cherry = pulp .cherry)
    (h2 : ∀ f, pulp f = .red) :
    peel .cherry = .red := by
  grind =>
    instantiate | pulp
```

Following a step with `|` and a {tech}[filter] shows the matching part of the {tactic}`grind` state in the editor, both before and after the step runs.
Filtering by `| pulp` keeps only the entries that mention `pulp`.
Before the round, these are `h2` and the equivalence class `{peel .cherry, pulp .cherry}` from `h1`:
```
[grind] Grind state
  [facts] Asserted facts
  [props] True propositions
    [_] ∀ (f : Fruit), pulp f = Color.red
  [eqc] Equivalence classes
    [eqc] {peel Fruit.cherry, pulp Fruit.cherry}
```

The false proposition `peel .cherry = .red` is omitted because it does not mention `pulp`.
Instantiating `h2` at `.cherry` asserts `pulp .cherry = .red` and closes the goal, so `no grind state` is shown after.
:::



# Goal Management and Sequencing
%%%
tag := "grind-interactive-goals"
%%%

These tactics don't invoke a solver or modify the {tactic}`grind` state.
They mirror the corresponding {ref "tactic-language-control"}[control structures and tactics] in the primary tactic language.

:::grindTactic "skip"
:::

:::grindTactic "done"
:::

A sequence may be grouped with parentheses, written `( steps )`, which runs the enclosed steps on the current goals with no added effect.
This grouping is used to delimit the scope of a control structure such as {grindTactic}`first` or {grindTactic}`repeat`.

:::grindTactic "focus"
:::

:::grindTactic "next" (show := "next =>")
:::

:::grindTactic "." (show := "·")
:::

The bullet is shorthand for {grindTactic}`next`.
It focuses on the main goal, suppressing all others.
It is an error if the enclosed tactic script does not result in a successful proof of the focused goal.

:::grindTactic "all_goals"
:::

:::grindTactic "any_goals"
:::

:::grindTactic "first"
:::

:::grindTactic "try"
:::

:::grindTactic "repeat"
:::

:::grindTactic "fail_if_success"
:::

:::grindTactic "fail"
:::

:::grindTactic "<;>"

If the tactic fails on any of the {tech}[subgoals], then the whole {grindTactic}`<;>` tactic fails.
:::


# Completing Proofs
%%%
tag := "grind-interactive-finish"
%%%

These tactics close goals, either by handing control back to {tactic}`grind`'s automatic search or by escaping into Lean's ordinary tactic language.
Goals may also be closed by one of the {ref "grind-interactive-solvers"}[theory solvers].

:::grindTactic "finish"
:::

:::grindTactic "finish?"
:::

When {grindTactic}`finish?` closes a goal, it offers a code action that replaces the call with the script it discovered, just as {tactic}`grind?` suggests a {keywordOf Lean.Parser.Tactic.grind}`grind only` call.
This enables an interactive workflow where parts of the proof can be discovered by {tactic}`grind` and then manually modified if needed.

:::example "Recording a `grind` Proof as an Interactive Script"
```lean -show
variable (pred : Nat → Prop)
```
{lean}`WithSucc` is closed under successor:
```lean
@[grind]
inductive WithSucc (pred : Nat → Prop): Nat → Prop where
  | base : pred n → WithSucc pred n
  | step : WithSucc pred n → WithSucc pred (n + 1)
```

{tactic}`grind` proves {lean}`WithSucc pred 2` from a proof of {lean}`WithSucc pred 0` by instantiating {name}`WithSucc.step` twice:
```lean
example (h : WithSucc pred 0) : WithSucc pred 2 := by
  grind
```

Following the goal with {keyword}`=> finish?` instead closes it and reports a script that reproduces the proof:
```lean
example (h : WithSucc pred 0) : WithSucc pred 2 := by
  grind => finish?
```

Applying the suggested script makes each instantiation explicit:
```lean
example (h : WithSucc pred 0) : WithSucc pred 2 := by
  grind =>
    instantiate only [→ WithSucc.step]
    instantiate only [→ WithSucc.step]
```
:::

:::grindTactic "sorry"
:::

:::grindTactic "admit"
:::

:::grindTactic "tactic" (show := "tactic =>")
:::

:::grindTactic "exact"
:::

# Theory Solvers
%%%
tag := "grind-interactive-solvers"
%%%

Each of these tactics runs one of {tactic}`grind`'s decision procedures on the current state.

:::grindTactic "lia"
:::

:::grindTactic "linarith"
:::

:::grindTactic "ring"
:::

:::grindTactic "ac"
:::

# Theorem Instantiation
%%%
tag := "grind-interactive-instantiate"
%%%

These tactics add new facts to the {tactic}`grind` state (that is, the “whiteboard”) by instantiating theorems.

:::grindTactic "instantiate"
:::

{grindTactic}`instantiate` runs a single round of E-matching.
By default, this round uses all of {tactic}`grind`'s currently active theorems; the bracketed list supplies further theorems to instantiate alongside them, and an {tech}[anchor] adds a specific local theorem from the state.
Running {grindTactic}`show_local_thms` displays the local theorems' anchors.
The {keywordOf Lean.Parser.Tactic.Grind.instantiate}`only` modifier restricts the round to the listed theorems.

The {keywordOf Lean.Parser.Tactic.Grind.instantiate}`approx` modifier has no effect on how the step runs.
It is a marker that appears in automatically generated scripts, such as those suggested by {tactic}`grind?` and {grindTactic}`finish?`, when {tactic}`grind` cannot determine a precise list of theorems for the step.
It signals that the listed theorems are an approximation that may need to be adjusted by hand.

:::example "Instantiating a Local Hypothesis"
A hypothesis that is a quantified statement becomes a local theorem in the {tactic}`grind` state.
Because this hypothesis has no global name, it is instantiated by its {tech}[anchor], which {grindTactic}`show_local_thms` reports:
```lean (name := instAnchor)
example (f : Nat → Nat) (h : ∀ n, f n ≤ n * n) :
    f 3 ≤ 9 := by
  grind =>
    show_local_thms
    instantiate [#7468]
```
```leanOutput instAnchor
[thms] Local theorems
  [thm] #7468 := ∀ (n : Nat), f n ≤ n * n
```

```lean -show
variable (f : Nat → Nat) (h : ∀ n, f n ≤ n * n)
```
Instantiating {lean}`h` at {lean}`3` adds the fact {lean}`f 3 ≤ 3 * 3` to the state, from which {tactic}`grind` concludes that {lean}`f 3 ≤ 9`.
:::

:::grindTactic "use"
:::

:::grindTactic "mbtc"
:::

# Case Analysis
%%%
tag := "grind-interactive-cases"
%%%

These tactics invoke {tactic}`grind`'s {ref "grind-split"}[case splitting].

:::grindTactic "cases"
:::

:::grindTactic "cases?"
:::

:::grindTactic "cases_next"
:::

# State Inspection
%%%
tag := "grind-interactive-inspect"
%%%

Many of the tactics in this section take an optional {tech}[filter] as a parameter.
This filter should be provided _without_ the `|` character, because that invokes the general state display mechanism instead of customizing the tactic's display.

:::example "Inspecting the Whiteboard"
{grindTactic}`show_state` prints the asserted facts, the true and false propositions, and the equivalence classes found so far:
```lean (name := showState)
inductive Color where | red | green
inductive Fruit where | cherry | lime

example (peel pulp : Fruit → Color)
    (h1 : peel .cherry = pulp .cherry)
    (h2 : ∀ f, pulp f = .red) :
    peel .cherry = .red := by
  grind =>
    show_state
    finish
```
```leanOutput showState
[grind] Grind state
  [facts] Asserted facts
  [props] True propositions
    [_] ∀ (f : Fruit), pulp f = Color.red
  [props] False propositions
    [_] peel Fruit.cherry = Color.red
  [eqc] Equivalence classes
    [eqc] {peel Fruit.cherry, pulp Fruit.cherry}
```

The class `{peel .cherry, pulp .cherry}` comes from `h1`.
The universally quantified statement `h2` is not yet instantiated, so the proof is not complete until {grindTactic}`finish` hands control back to {tactic}`grind`'s search.
The companion tactics {grindTactic}`show_asserted`, {grindTactic}`show_true`, {grindTactic}`show_false`, and {grindTactic}`show_eqcs` display individual sections of this state.
:::

:::grindTactic "show_state"
:::

:::grindTactic "show_asserted"
:::

:::grindTactic "show_true"
:::

:::grindTactic "show_false"
:::

:::grindTactic "show_eqcs"
:::

:::grindTactic "show_cases"
:::

:::grindTactic "show_local_thms"
:::

:::grindTactic "show_goals"
:::

:::grindTactic "show_term"
:::

# Local Context and Naming
%%%
tag := "grind-interactive-context"
%%%

These tactics add hypotheses to the local context and make inaccessible names available to later steps.

:::grindTactic Grind.«have» (show := "have")
:::

A second form of {keywordOf Lean.Parser.Tactic.Grind.haveSilent}`have`, written `have h : t` with no value, proves `t` from the current {tactic}`grind` state using the default search strategy and adds it as a hypothesis.

:::grindTactic haveSilent (show := "have")
:::

:::grindTactic "rename_i"
:::

:::grindTactic "expose_names"
:::

# Configuration
%%%
tag := "grind-interactive-config"
%%%

These tactics run a sequence of {tactic}`grind` tactics with modified options or configuration.

:::grindTactic "set_option"
:::

:::grindTactic "set_config"
:::

# Symbolic Simulation Mode
%%%
tag := "grind-sym"
%%%

The {tactic}`sym` tactic is a lower-level version of {keywordOf Lean.Parser.Tactic.grind}`grind =>` that provides a higher degree of manual control over the state.
When run, {tactic}`sym` enters interactive mode without the eager introduction of hypotheses and use of proof by contradiction that {tactic}`grind` performs.

When using {tactic}`sym`, assumptions must be manually introduced, just as in the standard proof tactic language.
Introducing an assumption moves it from the goal's conclusion into a new hypothesis.
It is often also useful to add the assumption to the “whiteboard”, so that it participates in congruence closure and {tactic}`grind`'s other processes.
Adding a hypothesis or term to the whiteboard is called {deftech}_internalization_.
Once internalized, a hypothesis participates in congruence reasoning, {tech}[constraint propagation], and the theory solvers; until then, {tactic}`grind` does not reason about it.

The following tactics are available only after {tactic}`sym`; they are not available in plain interactive {tactic}`grind` because it carries out their operations automatically when needed.

:::grindTactic symIntro (show := "intro")
:::

::::example "Introduction and Internalization"
Introducing a hypothesis changes the goal and, by default, adds the hypothesis to the whiteboard:

:::grindTacticExample +sym
{grindGoal}`∀ (a b : Nat), a = b → b = a`
```grindPrefix
intro a b
```

When the current goal is an implication and the {tactic}`grind` state is empty, running {grindTactic Lean.Parser.Tactic.Grind.symIntro}`intro` both adds the antecedent as an assumption and integrates it into the whiteboard.
If the initial goal and grind state are:
```grindProofState
case grind
a b : Nat
⊢ a = b → b = a
```
```grindState
[grind] Grind state
```
then running
```grindStep
intro h
```
results in a new assumption:
```grindProofState
case grind
a b : Nat
h : a = b
⊢ b = a
```
This new assumption has also modified the {tactic}`grind` state, which is now:
```grindState
[grind] Grind state
  [facts] Asserted facts
    [_] a = b
  [eqc] Equivalence classes
    [eqc] {a, b}
```
:::
:::grindTacticExample +sym
{grindGoal}`∀ (a b : Nat), a = b → b = a`
```grindPrefix
intro a b
```

With the same goal and empty state:
```grindProofState
case grind
a b : Nat
⊢ a = b → b = a
```
```grindState
[grind] Grind state
```
introducing without internalization:
```grindStep
intro (internalize := false) h
```
results in a modified goal but an empty state:
```grindProofState
case grind
a b : Nat
h : a = b
⊢ b = a
```
```grindState
[grind] Grind state
```
:::

::::

The shorthand `intro~` introduces binders without internalizing them, equivalent to `intro (internalize := false)`.

:::grindTactic symIntros (show := "intros")
:::

The shorthand `intros~` introduces all remaining binders without internalizing them.

:::grindTactic "apply"
:::

:::grindTactic "internalize"
:::

:::grindTactic "internalize_all"
:::

:::grindTactic "by_contra"
:::

The {grindTactic}`simp` and {grindTactic}`dsimp` tactics in {tactic}`sym` scripts run {tactic}`grind`'s own simplifier, a separate implementation built for its internal representation of terms, with its own performance characteristics and feature set.
This simplifier operates directly on that representation and avoids testing definitional equality.
Instead of {tech}[simp sets], it uses {deftech}_named variants_: named bundles of simprocs (to be run before and after simplification) along with configuration overrides.
Named variants are described in more detail {ref "grind-sym-simp-variants"}[in the next section].

:::grindTactic "simp"
:::

:::grindTactic "dsimp"
:::

## Registering Simplification Variants
%%%
tag := "grind-sym-simp-variants"
%%%

Named variants, used by the {tactic}`sym` versions of {grindTactic}`simp` and {grindTactic}`dsimp`, are declared using the {keywordOf Lean.Parser.Command.registerSymSimp}`register_sym_simp` and {keywordOf Lean.Parser.Command.registerSymDSimp}`register_sym_dsimp` commands.
Once registered, a variant is then selected by following {grindTactic}`simp` or {grindTactic}`dsimp` with that name.

:::syntax command (title := "Registering a `Sym.simp` Variant")
```grammar
register_sym_simp $name:ident where
  $fields*
```

{includeDocstring Lean.Parser.Command.registerSymSimp}
:::

:::syntax command (title := "Registering a `Sym.dsimp` Variant")
```grammar
register_sym_dsimp $name:ident where
  $fields*
```

{includeDocstring Lean.Parser.Command.registerSymDSimp}
:::

The fields in the `where` block are all optional:

: `pre` and `post`

  The simproc chains applied before and after simplification, respectively.

: `maxSteps`

  Bounds the number of simplification steps.

: `maxDischargeDepth`

  Bounds the depth of recursive side-goal discharge.
  Available only for {keywordOf Lean.Parser.Command.registerSymSimp}`register_sym_simp`.
