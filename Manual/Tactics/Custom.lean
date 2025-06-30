/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

import Manual.Tactics.Reference
import Manual.Tactics.Conv

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
set_option verso.docstring.allowMissing true

open Lean.Elab.Tactic

#doc (Manual) "Custom Tactics" =>
%%%
tag := "custom-tactics"
%%%


```lean (show := false)
open Lean
```

Tactics are productions in the syntax category `tactic`. {TODO}[xref macro for syntax\_cats]
Given the syntax of a tactic, the tactic interpreter is responsible for carrying out actions in the tactic monad {name}`TacticM`, which is a wrapper around Lean's term elaborator that keeps track of the additional state needed to execute tactics.
A custom tactic consists of an extension to the `tactic` category along with either:
 * a {tech}[macro] that translates the new syntax into existing syntax, or
 * an elaborator that carries out {name}`TacticM` actions to implement the tactic.

# Tactic Macros
%%%
tag := "tactic-macros"
%%%

The easiest way to define a new tactic is as a {tech}[macro] that expands into already-existing tactics.
Macro expansion is interleaved with tactic execution.
The tactic interpreter first expands tactic macros just before they are to be interpreted.
Because tactic macros are not fully expanded prior to running a tactic script, they can use recursion; as long as the recursive occurrence of the macro syntax is beneath a tactic that can be executed, there will not be an infinite chain of expansion.

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

Like other Lean macros, tactic macros are {tech key:="hygiene"}[hygienic].
References to global names are resolved when the macro is defined, and names introduced by the tactic macro cannot capture names from its invocation site.

When defining a tactic macro, it's important to specify that the syntax being matched or constructed is for the syntax category `tactic`.
Otherwise, the syntax will be interpreted as that of a term, which will match against or construct an incorrect AST for tactics.

## Extensible Tactic Macros
%%%
tag := "tactic-macro-extension"
%%%


Because macro expansion can fail, {TODO}[xref] multiple macros can match the same syntax, allowing backtracking.
Tactic macros take this further: even if a tactic macro expands successfully, if the expansion fails when interpreted, the tactic interpreter will attempt the next expansion.
This is used to make a number of Lean's built-in tactics extensible—new behavior can be added to a tactic by adding a {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` declaration.

::::keepEnv
:::example "Extending {tactic}`trivial`"

The {tactic}`trivial`, which is used by many other tactics to quickly dispatch subgoals that are not worth bothering the user with, is designed to be extended through new macro expansions.
Lean's default {lean}`trivial` can't solve {lean}`IsEmpty []` goals:
```lean (error := true)
def IsEmpty (xs : List α) : Prop :=
  ¬ xs ≠ []

example (α : Type u) : IsEmpty (α := α) [] := by trivial
```

The error message is an artifact of {tactic}`trivial` trying {tactic}`assumption` last.
Adding another expansion allows {tactic}`trivial` to take care of these goals:
```lean
def emptyIsEmpty : IsEmpty (α := α) [] := by simp [IsEmpty]

macro_rules | `(tactic|trivial) => `(tactic|exact emptyIsEmpty)

example (α : Type u) : IsEmpty (α := α) [] := by
  trivial
```
:::
::::

::::keepEnv
:::example "Expansion Backtracking"
Macro expansion can induce backtracking when the failure arises from any part of the expanded syntax.
An infix version of {tactic}`first` can be defined by providing multiple expansions in separate {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` declarations:
```lean
syntax tactic "<|||>" tactic : tactic
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t1
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t2

example : 2 = 2 := by
  rfl <|||> apply And.intro

example : 2 = 2 := by
  apply And.intro <|||> rfl
```

Multiple {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` declarations are needed because each defines a pattern-matching function that will always take the first matching alternative.
Backtracking is at the granularity of {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` declarations, not their individual cases.
:::
::::
