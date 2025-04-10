/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.PrettyPrinter.Delaborator

import Manual.Meta


open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean (Syntax Expr)

#doc (Manual) "Extending Lean's Output" =>
%%%
tag := "unexpand-and-delab"
%%%

Extending Lean with new syntax and implementing the new syntax with macros and elaborators allows users to express ideas to Lean more conveniently.
However, Lean is an _interactive_ theorem prover: it is also important that the feedback it provides can be readily understood.
Syntax extensions should be used in _output_ as well as in _input_.

:::paragraph
There are two primary mechanisms for instructing Lean to use a syntax extension in its output:

: Unexpanders

  Unexpanders are the inverse of {tech}[macros].
  Macros implement new syntax in terms of the old syntax by translation, _expanding_ the new feature into encodings in pre-existing features.
  Like macros, {deftech}_unexpanders_ translate {lean}`Syntax` into {lean}`Syntax`; unlike macros, they transform the encodings into the new extensions.

: Delaborators

  Delaborators are the inverse of {tech}[elaborators].
  While elaborators translate {lean}`Syntax` into the core type theory's {lean}`Expr`, {deftech}_delaborators_ translate {lean}`Expr`s into {lean}`Syntax`.
:::

Before an {name}`Expr` is displayed, it is first delaborated and then unexpanded.
The delaborator tracks the position in the original {name}`Expr` that its output originated from; this position is encoded in the resulting syntax's {name Lean.SourceInfo}`SourceInfo`.
Just as macro expansion automatically annotates the resulting syntax with synthetic source information that correspond to the original syntax's position, the unexpansion mechanism preserves the resulting syntax's association with the underlying {name}`Expr`.
This association enables Lean's interactive features that provide information about the resulting syntax when it is shown in {tech}[proof states] and diagnostics.

# Unexpanders
%%%
tag := "Unexpanders"
%%%

Just as macros are registered in a table that maps {tech}[syntax kinds] to macro implementations, unexpanders are registered in a table that maps the names of constants to unexpander implementations.
Before Lean displays syntax to users, it attempts to rewrite each application of a constant in the syntax according to this table.
Occurrences of the context that are not applications are treated as applications with zero arguments.

Unexpansion proceeds from the inside out.
The unexpander is passed the syntax of the application, with implicit arguments hidden, after the arguments have been unexpanded.
If the option {option}`pp.explicit` is {lean}`true` or {option}`pp.notation` is {lean}`false`, then unexpanders are not used.

::::::::leanSection
```lean (show := false)
open Lean.PrettyPrinter (Unexpander UnexpandM)
```

An unexpander has type {lean}`Lean.PrettyPrinter.Unexpander`, which is an abbreviation for `Syntax → Lean.PrettyPrinter.UnexpandM Syntax`.
In the remainder of this section, the names {lean}`Unexpander` and {lean}`UnexpandM` are used unqualified.
{lean}`UnexpandM` is a monad that supports quotation and failure via its {name Lean.MonadQuotation}`MonadQuotation` and {lean}`MonadExcept Unit` instances.

An unexpander should either return unexpanded syntax or fail using {lean type:="UnexpandM Syntax"}`throw ()`.
If the unexpander succeeds, then the resulting syntax is unexpanded again; if it fails, then the next unexpander is tried.
When no unexpander succeeds for the syntax, its child nodes are unexpanded until all opportunities for unexpansion are exhausted.

{docstring Lean.PrettyPrinter.Unexpander}

{docstring Lean.PrettyPrinter.UnexpandM}

An unexpander for a constant is registered by applying the {attr}`app_unexpander` attribute.
{ref "operators"}[Custom operators] and {ref "notations"}[notations] automatically create unexpanders for the syntax that they introduce.

:::syntax attr (title := "Unexpander Registration")
```grammar
app_unexpander $_:ident
```

Registers an unexpander of type {name}`Unexpander` for applications of a constant.
:::


:::::example "Custom Unit Type"
::::keepEnv
A type equivalent to {lean}`Unit`, but with its own notation, can be defined as a zero-field structure and a macro:
```lean
structure Solo where
  mk ::

syntax "‹" "›" : term

macro_rules
  | `(term|‹›) => ``(Solo.mk)
```


While the new notation can be used to write theorem statements, it does not appear in proof states.
For example, when proving that all values of type {lean}`Solo` are equal to {lean}`‹›`, the initial proof state is:
```proofState
∀v, v = ‹› := by
intro v
/--
v : Solo
⊢ v = { }
-/

```
This proof state shows the constructor using {tech}[structure instance] syntax.
An unexpander can be used to override this choice.
Because {name}`Solo.mk` cannot be applied to any arguments, the unexpander is free to ignore the syntax, which will always be {lean (type := "UnexpandM Syntax")}``` `(Solo.mk) ```.

```lean
@[app_unexpander Solo.mk]
def unexpandSolo : Lean.PrettyPrinter.Unexpander
  | _ => `(‹›)
```

With this unexpander, the initial state of the proof now renders with the correct syntax:
```proofState
∀v, v = ‹› := by
intro v
/--
v : Solo
⊢ v = ‹›
-/
```

::::
:::::

:::::example "Unexpansion and Arguments"

A {name}`ListCursor` represents a position in a {lean}`List`.
{name}`ListCursor.before` contains the reversed list of elements prior to the position, and {name}`ListCursor.after` contains the elements after the position.

```lean
structure ListCursor (α) where
  before : List α
  after : List α
deriving Repr
```

List cursors can be moved to the left or to the right:
```lean
def ListCursor.left : ListCursor α → Option (ListCursor α)
  | ⟨[], _⟩ => none
  | ⟨l :: ls, rs⟩ => some ⟨ls, l :: rs⟩

def ListCursor.right : ListCursor α → Option (ListCursor α)
  | ⟨_, []⟩ => none
  | ⟨ls, r :: rs⟩ => some ⟨r :: ls, rs⟩
```

They can also be moved all the way to the left or all the way to the right:
```lean
def ListCursor.rewind : ListCursor α → ListCursor α
  | xs@⟨[], _⟩ => xs
  | ⟨l :: ls, rs⟩ => rewind ⟨ls, l :: rs⟩
termination_by xs => xs.before

def ListCursor.fastForward : ListCursor α → ListCursor α
  | xs@⟨_, []⟩ => xs
  | ⟨ls, r :: rs⟩ => fastForward ⟨r :: ls, rs⟩
termination_by xs => xs.after
```

```lean (show := false)
def ListCursor.ofList (xs : List α) : ListCursor α where
  before := []
  after := xs

def ListCursor.toList : (xs : ListCursor α) → List α
  | ⟨[], rs⟩ => rs
  | ⟨l::ls, rs⟩ => toList ⟨ls, l :: rs⟩
termination_by xs => xs.before
```

However, the need to reverse the list of previous elements can make list cursors difficult to understand.
A cursor can be given a notation in which a flag (`🚩`) marks the cursor's location in a list:
```lean
syntax "[" term,* " 🚩 " term,* "]": term
macro_rules
  | `([$ls,* 🚩 $rs,*]) =>
    ``(ListCursor.mk [$[$((ls : Array Lean.Term).reverse)],*] [$rs,*])
```
In the macro, the sequences of elements have type {lean}``Syntax.TSepArray `term ","``.
The type annotation as {lean}`Array Lean.Term` causes a coercion to fire so that {name}`Array.reverse` can be applied, and a similar coercion reinserts the separating commas.
These coercions are described in the section on {ref "typed-syntax"}[typed syntax].

While the syntax works, it is not used in Lean's output:
```lean (name := flagNo)
#check [1, 2, 3 🚩 4, 5]
```
```leanOutput flagNo
{ before := [3, 2, 1], after := [4, 5] } : ListCursor Nat
```

An unexpander solves this problem.
The unexpander relies on the built-in unexpanders for list literals already having rewritten the two lists:
```lean
@[app_unexpander ListCursor.mk]
def unexpandListCursor : Lean.PrettyPrinter.Unexpander
  | `($_ [$ls,*] [$rs,*]) =>
    `([$((ls : Array Lean.Term).reverse),* 🚩 $(rs),*])
  | _ => throw ()
```

```lean (name := flagYes)
#check [1, 2, 3 🚩 4, 5]
```
```leanOutput flagYes
[1, 2, 3 🚩 4, 5] : ListCursor Nat
```

```lean (name := flagYes2)
#reduce [1, 2, 3 🚩 4, 5].right
```
```leanOutput flagYes2
some [1, 2, 3, 4 🚩 5]
```

```lean (name := flagYes3)
#reduce [1, 2, 3 🚩 4, 5].left >>= (·.left)
```
```leanOutput flagYes3
some [1 🚩 2, 3, 4, 5]
```

:::::

::::::::


# Delaborators
%%%
tag := "delaborators"
%%%
::::::::leanSection
```lean (show := false)
open Lean.PrettyPrinter.Delaborator (DelabM Delab)
open Lean (Term)
```
A delaborator is function of type {lean}`Lean.PrettyPrinter.Delaborator.Delab`, which is an abbreviation for {lean}`Lean.PrettyPrinter.Delaborator.DelabM Term`.
Unlike unexpanders, delaborators are not implemented as functions.
This is to make it easier to implement them correctly: the monad {name}`DelabM` tracks the current position in the expression that's being delaborated so the delaboration mechanism can annotate the resulting syntax.

Delaborators are registered with the {attr}`delab` attribute.
An internal table maps the names of the constructors of {name}`Expr` (without namespaces) to delaborators.
Additionally, the name `app.`﻿$`c` is consulted to find delaborators for applications of the constant $`c`, and the name `mdata.`﻿$`k` is consulted to find delaborators for {name}`Expr.mdata` constructors with a single key $`k` in their metadata.

:::syntax attr (title := "Delaborator Registration")
The {attr}`delab` attribute registers a delaborator for the indicated constructor or metadata key of {lean}`Expr`.
```grammar
delab $_:ident
```

The {keyword}`app_delab ` attribute registers a delaborator for applications of the indicated constant after {tech key:="resolve"}[resolving] it in the current {tech key:="section scope"}[scope].
```grammar
app_delab $_:ident
```
:::

::::leanSection
```lean (show := false)
open Lean.PrettyPrinter.Delaborator.SubExpr
```
:::paragraph
The monad {name}`DelabM` is a {tech}[reader monad] that includes access to the current position in the {lean}`Expr`.
Recursive delaboration is performed by adjusting the reader monad's tracked position, rather than by explicitly passing a subexpression to another function.
The most important functions for working with subexpressions in delaborators are in the namespace `Lean.PrettyPrinter.Delaborator.SubExp`:
 * {name}`getExpr` retrieves the current expression for analysis.
 * {name}`withAppFn` adjusts the current position to be that of the function in an application.
 * {name}`withAppArg` adjusts the current position to be that of the argument in an application
 * {name}`withAppFnArgs` decomposes the current expression into a non-application function and its arguments, focusing on each.
 * {name}`withBindingBody` descends into the body of a function or function type.

Further functions to descend into the remaining constructors of {name}`Expr` are available.
:::
::::


::::::::

::::draft
:::planned 122

 * Delaboration example and combinator reference
 * Pretty printing
 * Parenthesizers
:::
::::
