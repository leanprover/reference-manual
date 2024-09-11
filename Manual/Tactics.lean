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
 * Cases and case labels
 * Diff labels
:::

# Hygiene

# Options

{optionDocs tactic.dbg_cache}

{optionDocs tactic.hygienic}

{optionDocs tactic.customEliminators}

{optionDocs tactic.skipAssignedInstances}

{optionDocs tactic.simp.trace}

# Extensions

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

{include 0 Manual.Tactics.Reference}
