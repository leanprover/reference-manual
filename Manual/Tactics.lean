import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Tactic Proofs" =>

The tactic language is a special-purpose programming language for constructing proofs.
In Lean, statements are represented by types, and proofs are terms that inhabit these types.
While terms are designed to make it convenient to indicate a specific inhabitant of a type, tactics are designed to make it convenient to demonstrate that a type is inhabited.
This distinction exists because it's important that definitions pick out the precise objects of interest and that programs return the intended results, but proof irrelevance means that there's no _technical_ reason to prefer one proof term over another.
For example, given two assumptions of a given type, a program must be carefully written to use the correct one, while a proof may use either without consequence.

Tactics are imperative programs that modify a {deftech}_proof state_.{index}[proof state]
A proof state consists of a sequence of {deftech}_goals_, which are contexts of local assumptions together with types to be inhabited; a tactic may either _succeed_ with a possibly-empty sequence of further goals or _fail_ if it cannot make progress.
If tactic succeeds with no further goals, then the goal that it was applied to has been completely proved.
If it succeeds with one or more further goals, then its goal or goals will be proved when those further goals have been proved.

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

# Tactic Overview

## Assumptions

:::TODO
Create a tactic documentation command that does what both of the following do, using the infrastructure from https://github.com/leanprover/lean4/pull/4490
:::

{docstring Lean.Parser.Tactic.assumption}

:::syntax Lean.Parser.Tactic.assumption
```grammar
assumption
```
:::
