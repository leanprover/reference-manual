import VersoManual

import Lean.Parser.Term

import Manual.Meta

import Manual.Tactics.Reference
import Manual.Tactics.Impls

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic

#doc (Manual) "Tactic Proofs" =>

The tactic language is a special-purpose programming language for constructing proofs.
In Lean, statements are represented by types, and proofs are terms that inhabit these types.
While terms are designed to make it convenient to indicate a specific inhabitant of a type, tactics are designed to make it convenient to demonstrate that a type is inhabited.
This distinction exists because it's important that definitions pick out the precise objects of interest and that programs return the intended results, but proof irrelevance means that there's no _technical_ reason to prefer one proof term over another.
For example, given two assumptions of a given type, a program must be carefully written to use the correct one, while a proof may use either without consequence.

Tactics are imperative programs that modify a {deftech}_proof state_.{index}[proof state]
A proof state consists of an ordered sequence of {deftech}_goals_, which are contexts of local assumptions together with types to be inhabited; a tactic may either _succeed_ with a possibly-empty sequence of further goals or _fail_ if it cannot make progress.
If tactic succeeds with no further goals, then the proof is complete.
If it succeeds with one or more further goals, then its goal or goals will be proved when those further goals have been proved.
The first goal in the proof state is called the {deftech}_main goal_.{index subterm:="main"}[goal]{index}[main goal]
While most tactics affect only the first goal in the sequence, operators such as {tactic}`<;>` and {tactic}`all_goals` can be used to apply a tactic to many goals, and operators such as bullets, {tactic}`next` or {tactic}`case` can narrow the focus of subsequent tactics to only a single goal in the proof state.

Behind the scenes, tactics construct {deftech}[proof terms].
Proof terms are independently checkable evidence of a theorem's truth, written in Lean's core type theory.
Each proof is checked in the {tech}[kernel], and can be verified with independently-implemented external checkers, so the worst outcome from a bug in a tactic is a confusing error message, rather than an incorrect proof.
Each goal in a tactic proof corresponds to an incomplete portion of a proof term.

# Running Tactics

:::syntax Lean.Parser.Term.byTactic
Tactics are included in terms using {keywordOf Lean.Parser.Term.byTactic}`by`, which is followed by a sequence of tactics in which each has the same indentation:
```grammar
by
$t
```

Alternatively, explicit brackets and semicolons may be used:
```grammar
by { $t* }
```
:::

Tactics are invoked using the {keywordOf Lean.Parser.Term.byTactic}`by` term.
When the elaborator encounters {keywordOf Lean.Parser.Term.byTactic}`by`, it invokes the tactic interpreter to construct the resulting term.
Tactic proofs may be embedded via {keywordOf Lean.Parser.Term.byTactic}`by` in any context in which a term can occur.

# Reading Proof States

:::planned
 * Assumptions and inaccessible names
 * Cases and {deftech}_case labels_
 * Diff labels
:::

# The Tactic Language

A tactic script consists of a sequence of tactics, separated either by semicolons or newlines.
When separated by newlines, tactics must be indented to the same level.
Explicit curly braces and semicolons may be used instead of indentation.
Tactic sequences may be grouped by parentheses.
This allows a sequence of tactics to be used in a position where a single tactic would otherwise be grammatically expected.

Generally, execution proceeds from top to bottom, with each tactic running in the proof state left behind by the prior tactic.
The tactic language contains a number of control structures that can modify this flow.

Each tactic is a syntax extension in the `tactic` category.
This means that tactics are free to define their own concrete syntax and parsing rules.
However, with a few exceptions, the majority of tactics can be identified by a leading keyword; the exceptions are typically frequently-used built-in control structures.

:::TODO
move macro bit to other section, insert xref here
:::

Just as terms may be defined either via macro expansion into other terms or using elaborators, tactics may be defined either via macro expansion into other tactics or by a definition of type {name}`Tactic`, which is a function from syntax to an action in the tactic monad {name}`TacticM`.
Macro expansion is interleaved with tactic execution, so tactic macros are first expanded just before they are interpreted.
Because tactic macros are not fully expanded prior to running a tactic script, they can make use of recursion.

::::keepEnv
:::example "Recursive tactic macro"
This recursive implementation of a tactic akin to {tactic}`repeat` is defined via macro expansion.
When the argument `$t` fails, the recursive occurrence of {tactic}`rep` is never invoked, and is thus never macro expanded.
```lean
syntax "rep" tactic : tactic
macro_rules
  | `(tactic|rep $t) =>
  `(tactic|
    first
      | $t; rep $t
      | skip)

example : 0 ≤ 4 := by
  rep (apply Nat.le.step)
  apply Nat.le.refl
```
:::
::::

## Control Structures

### Success and Failure

When run in a proof state, every tactic either succeeds or fails.
Tactic failure is akin to exceptions: failures typically "bubble up" until handled.
Unlike exceptions, there is no operator to distinguish between reasons for failure; {tactic}`first` simply takes the first branch that succeeds.

::: tactic "fail"
:::

:::tactic "fail_if_success"
:::

:::tactic "try"
:::

:::tactic "first"
:::


### Branching

Tactic proofs may use pattern matching and conditionals.
However, their meaning is not quite the same as it is in terms.
While terms are expected to be executed once the values of their variables are known, proofs are executed with their variables left abstract and should consider _all_ cases simultaneously.
Thus, when `if` and `match` are used in tactics, their meaning is reasoning by cases rather than selection of a concrete branch.
All of their branches are executed, and the condition or pattern match is used to refine the main goal with more information in each branch, rather than to select a single branch.

:::tactic Lean.Parser.Tactic.tacIfThenElse show := "if"

:::

:::example "Reasoning by cases with `if`"
In each branch of the {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if`, an assumption is added that reflects whether `n = 0`.

```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  if n = 0 then
    simp [*]
  else
    simp only [↓reduceIte, gt_iff_lt, *]
    omega
```
:::

:::tactic Lean.Parser.Tactic.match show := "match"

When pattern matching, instances of the scrutinee in the goal are replaced with the patterns that match them in each branch.
Each branch must then prove the refined goal.
Compared to the `cases` tactic, using `match` can allow a greater degree of flexibility in the cases analysis being performed, but the requirement that each branch solve its goal completely makes it more difficult to incorporate into larger automation scripts.
:::

:::example "Reasoning by cases with `match`"
In each branch of the {keywordOf Lean.Parser.Tactic.match}`match`, the scrutinee `n` has been replaced by either `0` or `k + 1`.
```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  match n with
  | 0 =>
    simp
  | k + 1 =>
    simp
```
:::

### Goal Selection

Most tactics affect the {tech}[main goal].
Goal selection tactics provide a way to treat a different goal as the main one, rearranging the sequence of goals in the proof state.


:::tactic "case"
:::

:::tactic "case'"
:::


:::tactic "rotate_left"
:::

:::tactic "rotate_right"
:::

#### Sequencing

The {tactic}`<;>` tactic combinator allows a tactic to be applied to _every_ subgoal produced by some other tactic.

:::tactic "<;>"
:::

:::TODO
examples
:::

#### Working on Multiple Goals

The tactics {tactic}`all_goals` and {tactic}`any_goals` allow a tactic to be applied to every goal in the proof state.
The difference between them is that if the tactic fails for in any of the goals, {tactic}`all_goals` itself fails, while {tactic}`any_goals` fails only if the tactic fails in all of the goals.

:::tactic "all_goals"
:::

:::tactic "any_goals"
:::


### Focusing


Focusing tactics remove some subset of the proof goals (typically leaving only the main goal) from the consideration of some further tactics.
In addition to the tactics described here, the {tactic}`case` tactic focuses on the selected goal.

:::tactic Lean.cdot show:="·"

It is generally considered good Lean style to use bullets whenever a tactic line results in more than one new subgoal.
This makes it easier to read and maintain proofs, because the connections between steps of reasoning are more clear and any change in the number of subgoals while editing the proof will have a localized effect.
:::

:::tactic "next"
:::


:::tactic "focus"
:::

### Repetition and Iteration

:::tactic "iterate"
:::

:::tactic "repeat"
:::

:::tactic "repeat'"
:::

:::tactic "repeat1'"
:::


## Names and Hygiene


Behind the scenes, tactics generate proof terms.
These proof terms exist in a local context, because assumptions in proof states correspond to local binders in terms.
Uses of assumptions correspond to variable references.
It is very important that the naming of assumptions be predictable; otherwise, small changes to the internal implementation of a tactic could either lead to variable capture or to a broken reference if they cause different names to be selected.

Lean's tactic language is _hygienic_.
This means that the tactic language respects lexical scope, even though it is generating code.
Variable references in tactic scripts refer either to names that were in scope at the beginning of the script or to bindings that were explicitly introduced as part of the tactics, rather than to the names chosen for use in the proof term behind the scenes.

A consequence of hygienic tactics is that the only way to refer to an assumption is to explicitly name it.
Tactics cannot assign assumption names names themselves, but must rather accept names from users; users are correspondingly obligated to provide names for assumptions that they wish to refer to.
When an assumption does not have a user-provided name, it is shown in the proof state with a dagger (`'†', DAGGER	0x2020`).
The dagger indicates that the name is _inaccessible_.

Hygiene can be disabled by setting the option {option}`tactic.hygienic` to `false`.
This is not recommended, as many tactics rely on the hygiene system to prevent capture and thus do not incur the overhead of careful manual name selection.

{optionDocs tactic.hygienic}

::::example "Tactic hygiene: inaccessible assumptions"
:::tacticExample

```setup
skip
```
When proving that {goal}`∀ (n : Nat), 0 + n = n`, the initial proof state is:

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

The tactic {tacticStep}`intro` results in a proof state with an inaccessible  assumption:

```post
n✝ : Nat
⊢ 0 + n✝ = n✝
```
:::
::::

::::example "Tactic hygiene: accessible assumptions"
:::tacticExample

```setup
skip
```
When proving that {goal}`∀ (n : Nat), 0 + n = n`, the initial proof state is:

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

The tactic {tacticStep}`intro n`, with the explicit name `n`, results in a proof state with an accessibly-named assumption:

```post
n : Nat
⊢ 0 + n = n
```
:::
::::

### Accessing Assumptions

Many tactics provide a means of specifying names for the assumptions that they introduce.
For example, {tactic}`intro` and {tactic}`intros` take assumption names as arguments, and {tactic}`induction`'s {keywordOf Lean.Parser.Tactic.induction}`with`-form allows simultaneous case selection, assumption naming, and focusing.
When an assumption does not have a name, one can be assigned using {tactic}`next`, {tactic}`case`, or {tactic}`rename_i`.

:::tactic "rename_i"
:::

## Assumption Management

:::tactic "rename"
:::

:::tactic "revert"
:::

:::tactic "clear"
:::

:::tactic "intro"
:::


:::tactic "intros"
:::

:::tactic Lean.Parser.Tactic.introMatch (show := "intro | ... => ... | ... => ...")
:::

:::tactic "rintro"
:::

## Local Definitions and Proofs

{tactic}`have` and {tactic}`let` both create local assumptions.
Generally speaking, {tactic}`have` should be used when proving an intermediate lemma; {tactic}`let` should be reserved for local definitions.

:::tactic "have"
:::

:::tactic Lean.Parser.Tactic.tacticHaveI_
:::

:::tactic Lean.Parser.Tactic.tacticHave'_
:::

::: TODO
Mark as alias upstream in Lean
:::

:::tactic Lean.Parser.Tactic.«tacticHave'_:=_»
:::


:::tactic "let"
:::

:::tactic Lean.Parser.Tactic.tacticLet_
:::

:::tactic Lean.Parser.Tactic.tacticLetI_
:::

:::tactic Lean.Parser.Tactic.tacticLet'_
:::

## Namespace and Option Management

:::tactic Lean.Parser.Tactic.set_option show:="set_option"
:::

:::tactic Lean.Parser.Tactic.open show:="open"
:::

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withUnfoldingAll
:::


# Options

{optionDocs tactic.dbg_cache}

{optionDocs tactic.customEliminators}

{optionDocs tactic.skipAssignedInstances}

{optionDocs tactic.simp.trace}


{include 0 Manual.Tactics.Reference}

# Targeted Rewriting with {tactic}`conv`

The {tactic}`conv`, or conversion, tactic allows targeted rewriting within a goal.
The argument to {tactic}`conv` is written in a separate language that interoperates with the main tactic language; it features commands to navigate to specific subterms within the goal along with commands that allow these subterms to be rewritten.
{tactic}`conv` is useful when rewrites should only be applied in part of a goal (e.g. only on one side of an equality), rather than across the board.

:::tactic "conv"
:::

:::tactic Lean.Parser.Tactic.Conv.convTactic
:::

::: TODO
 Adapt tactic documentation feature to show conv documentation as well, and include the conv tactics here
:::

# Custom Tactics

::: planned
 * Adding tactics with `macro_rules`
 * Extending existing tactics via `macro_rules`
 * The tactic monad `TacticM`
:::

## The Tactic Monad

::: planned
 * Overview of available effects
 * Checkpointing
:::

{docstring Lean.Elab.Tactic.Tactic}

{docstring Lean.Elab.Tactic.TacticM}

{docstring Lean.Elab.Tactic.run}

{docstring Lean.Elab.Tactic.runTermElab}

### Control

{docstring Lean.Elab.Tactic.tryTactic}

{docstring Lean.Elab.Tactic.tryTactic?}

### Expressions

{docstring Lean.Elab.Tactic.ensureHasNoMVars}

{docstring Lean.Elab.Tactic.getFVarId}

{docstring Lean.Elab.Tactic.getFVarIds}

{docstring Lean.Elab.Tactic.sortMVarIdsByIndex}

{docstring Lean.Elab.Tactic.sortMVarIdArrayByIndex}

### Source Locations

{docstring Lean.Elab.Tactic.withLocation}

### Goals

{docstring Lean.Elab.Tactic.getGoals}

{docstring Lean.Elab.Tactic.setGoals}

{docstring Lean.Elab.Tactic.getMainGoal}

{docstring Lean.Elab.Tactic.getMainTag}

{docstring Lean.Elab.Tactic.closeMainGoal}

{docstring Lean.Elab.Tactic.focus}

{docstring Lean.Elab.Tactic.tagUntaggedGoals}

{docstring Lean.Elab.Tactic.getUnsolvedGoals}

{docstring Lean.Elab.Tactic.pruneSolvedGoals}

{docstring Lean.Elab.Tactic.appendGoals}

{docstring Lean.Elab.Tactic.closeMainGoalUsing}

### Term Elaboration

{docstring Lean.Elab.Tactic.elabTerm}

{docstring Lean.Elab.Tactic.elabTermEnsuringType}

{docstring Lean.Elab.Tactic.elabTermWithHoles}


### Low-Level Operations

These operations are primarily used as part of the implementation of {name}`TacticM` or of particular tactics.
It's rare that they are useful when implementing new tactics.

#### Monad Class Implementations

These operations are exposed through standard Lean monad type classes.

{docstring Lean.Elab.Tactic.tryCatch}

{docstring Lean.Elab.Tactic.liftMetaMAtMain}

{docstring Lean.Elab.Tactic.getMainModule}

{docstring Lean.Elab.Tactic.orElse}

#### Macro Expansion

{docstring Lean.Elab.Tactic.getCurrMacroScope}

{docstring Lean.Elab.Tactic.adaptExpander}

#### Case Analysis

{docstring Lean.Elab.Tactic.elabCasesTargets}

#### Simplifier

{docstring Lean.Elab.Tactic.elabSimpArgs}

{docstring Lean.Elab.Tactic.elabSimpConfig}

{docstring Lean.Elab.Tactic.elabSimpConfigCtxCore}

{docstring Lean.Elab.Tactic.dsimpLocation'}

{docstring Lean.Elab.Tactic.elabDSimpConfigCore}

#### Attributes

{docstring Lean.Elab.Tactic.tacticElabAttribute}

{docstring Lean.Elab.Tactic.mkTacticAttribute}


{include 2 Manual.Tactics.Impls}
