/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.Language.Namespaces
import Manual.Coercions


import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

#doc (Manual) "Namespaces and Sections" =>
%%%
tag := "namespaces-sections"
htmlSplit := .never
%%%

Names are organized into hierarchical {deftech}_namespaces_, which are collections of names.
Namespaces are the primary means of organizing APIs in Lean: they provide an ontology of operations, grouping related items.
Additionally, while this is not done by giving them names in the namespace, the effects of features such as {ref "language-extension"}[syntax extensions], {tech}[instances], and {tech}[attributes] can be attached to a namespace.

Sorting operations into namespaces organizes libraries conceptually, from a global perspective.
Any given Lean file will, however, typically not use all names equally.
{tech}[Sections] provide a means of ordering a local view of the globally-available collection of names, as well as a way to precisely control the scope of compiler options along with language extensions, instances, and attributes.
They also allow parameters shared by many declarations to be declared centrally and propagated as needed using the {keywordOf Lean.Parser.Command.variable}`variable` command.


{include 1 Manual.Language.Namespaces}

# Section Scopes
%%%
tag := "scopes"
%%%

Many commands have an effect for the current {deftech}[_section scope_] (sometimes just called "scope" when clear).
Every Lean module has a section scope.
Nested scopes are created via the {keywordOf Lean.Parser.Command.namespace}`namespace` and {keywordOf Lean.Parser.Command.section}`section` commands, as well as the {keywordOf Lean.Parser.Command.in}`in` command combinator.

The following data are tracked in section scopes:

: The Current Namespace

  The {deftech}_current namespace_ is the namespace into which new declarations will be defined.
  Additionally, {tech (key:="resolve")}[name resolution] includes all prefixes of the current namespace in the scope for global names.

: Opened Namespaces

  When a namespace is {deftech}_opened_, its names become available without an explicit prefix in the current scope.
  Additionally, scoped attributes and {ref "syntax-rules"}[scoped syntax extensions] in namespaces that have been opened are active in the current section scope.

: Options

  Compiler options are reverted to their original values at the end of the scope in which they were modified.

: Section Variables

  {tech}[Section variables] are names (or {tech}[instance implicit] parameters) that are automatically added as parameters to definitions.
  They are also added as universally-quantified assumptions to theorems when they occur in the theorem's statement.


## Controlling Section Scopes
%%%
tag := "scope-commands"
%%%

The {keywordOf Lean.Parser.Command.section}`section` command creates a new {deftech}[section] scope, but does not modify the current namespace, opened namespaces, or section variables.
Changes made to the section scope are reverted when the section ends.
Sections may optionally be named; the {keywordOf Lean.Parser.Command.end}`end` command that closes a named section must use the same name.
If section names have multiple components (that is, if they contain `.`-separated names), then multiple nested sections are introduced.
Section names have no other effect, and are a readability aid.

:::syntax command (title := "Sections")
The {keywordOf Lean.Parser.Command.section}`section` command creates a section scope that lasts either until an `end` command or the end of the file.
```grammar
section $[$id:ident]?
```
:::

:::example "Named Section"

The name {name Greetings.english}`english` is defined in the `Greetings` namespace.

```lean
def Greetings.english := "Hello"
```

Outside its namespace, it cannot be evaluated.

```lean (error := true) (name := english1)
#eval english
```
```leanOutput english1
Unknown identifier `english`
```

Opening a section allows modifications to the global scope to be contained.
This section is named `Greetings`.
```lean
section Greetings
```

Even though the section name matches the definition's namespace, the name is not in scope because section names are purely for readability and ease of refactoring.

```lean (error := true)  (name := english2)
#eval english
```
```leanOutput english2
Unknown identifier `english`
```

Opening the namespace `Greetings` brings {name}`Greetings.english` as {name Greetings.english}`english`:


```lean  (name := english3)
open Greetings

#eval english
```
```leanOutput english3
"Hello"
```

The section's name must be used to close it.

```lean (error := true) (name := english4) (keep := false)
end
```
```leanOutput english4
Missing name after `end`: Expected the current scope name `Greetings`

Hint: To end the current scope `Greetings`, specify its name:
  end ̲G̲r̲e̲e̲t̲i̲n̲g̲s̲
```

```lean
end Greetings
```

When the section is closed, the effects of the {keywordOf Lean.Parser.Command.open}`open` command are reverted.
```lean (error := true)  (name := english5)
#eval english
```
```leanOutput english5
Unknown identifier `english`
```
:::

The {keywordOf Lean.Parser.Command.namespace}`namespace` command creates a new section scope.
Within this section scope, the current namespace is the name provided in the command, interpreted relative to the current namespace in the surrounding section scope.
Like sections, changes made to the section scope are reverted when the namespace's scope ends.

To close a namespace, the {keywordOf Lean.Parser.Command.end}`end` command requires a suffix of the current namespace, which is removed.
All section scopes introduced by the {keywordOf Lean.Parser.Command.namespace}`namespace` command that introduced part of that suffix are closed.

:::syntax command (title := "Namespace Declarations")
The `namespace` command modifies the current namespace by appending the provided identifier.

creates a section scope that lasts either until an {keywordOf Lean.Parser.Command.end}`end` command or the end of the file.
```grammar
namespace $id:ident
```
:::


:::syntax command (title := "Section and Namespace Terminators")
Without an identifier, {keywordOf Lean.Parser.Command.end}`end` closes the most recently opened section, which must be anonymous.
```grammar
end
```

With an identifier, it closes the most recently opened section section or namespace.
If it is a section, the identifier be a suffix of the concatenated names of the sections opened since the most recent {keywordOf Lean.Parser.Command.namespace}`namespace` command.
If it is a namespace, then the identifier must be a suffix of the current namespace's extensions since the most recent {keywordOf Lean.Parser.Command.section}`section` that is still open; afterwards, the current namespace will have had this suffix removed.
```grammar
end $id:ident
```
:::

The {keywordOf Lean.Parser.Command.mutual}`end` that closes a {keywordOf Lean.Parser.Command.mutual}`mutual` block is part of the syntax of {keywordOf Lean.Parser.Command.mutual}`mutual`, rather than the {keywordOf Lean.Parser.Command.end}`end` command.

:::example "Nesting Namespaces and Sections"
Namespaces and sections may be nested.
A single {keywordOf Lean.Parser.Command.end}`end` command may close one or more namespaces or one or more sections, but not a mix of the two.

After setting the current namespace to `A.B.C` with two separate commands, `B.C` may be removed with a single {keywordOf Lean.Parser.Command.end}`end`:
```lean
namespace A.B
namespace C
end B.C
```
At this point, the current namespace is `A`.

Next, an anonymous section and the namespace `D.E` are opened:
```lean
section
namespace D.E
```
At this point, the current namespace is `A.D.E`.
An {keywordOf Lean.Parser.Command.end}`end` command cannot close all three due to the intervening section:
```lean (error := true) (name := endADE) (keep := false)
end A.D.E
```
```leanOutput endADE
Invalid name after `end`: Expected `D.E`, but found `A.D.E`
```
Instead, namespaces and sections must be ended separately.
```lean
end D.E
end
end A
```
:::

Rather than opening a section for a single command, the {keywordOf Lean.Parser.Command.in}`in` combinator can be used to create single-command section scope.
The {keywordOf Lean.Parser.Command.in}`in` combinator is right-associative, allowing multiple scope modifications to be stacked.

:::syntax command (title := "Local Section Scopes")
The `in` command combinator introduces a section scope for a single command.
```grammar
$c:command in
$c:command
```
:::

:::example "Using {keywordOf Lean.Parser.Command.in}`in` for Local Scopes"
The contents of a namespace can be made available for a single command using {keywordOf Lean.Parser.Command.in}`in`.
```lean
def Dessert.cupcake := "delicious"

open Dessert in
#eval cupcake
```

After the single command, the effects of {keywordOf Lean.Parser.Command.open}`open` are reverted.

```lean (error := true) (name := noCake)
#eval cupcake
```
```leanOutput noCake
Unknown identifier `cupcake`
```
:::

## Section Variables
%%%
tag := "section-variables"
%%%

{deftech}_Section variables_ are parameters that are automatically added to declarations that mention them.
This occurs whether or not the option {option}`autoImplicit` is {lean}`true`.
Section variables may be implicit, strict implicit, or explicit; instance implicit section variables are treated specially.

When the name of a section variable is encountered in a non-theorem declaration, it is added as a parameter.
Any instance implicit section variables that mention the variable are also added.
If any of the variables that were added depend on other variables, then those variables are added as well; this process is iterated until no more dependencies remain.
All section variables are added in the order in which they are declared, before all other parameters.
Section variables are added only when they occur in the _statement_ of a theorem.
Otherwise, modifying the proof of a theorem could change its statement if the proof term made use of a section variable.

Variables are declared using the {keywordOf Lean.Parser.Command.variable}`variable` command.


:::syntax command (title := "Variable Declarations")
```grammar
variable $b:bracketedBinder $b:bracketedBinder*
```
:::

The bracketed binders allowed after `variable` match the {ref "bracketed-parameter-syntax"}[syntax used in definition headers].

:::example "Section Variables"
In this section, automatic implicit parameters are disabled, but a number of section variables are defined.

```lean
section
set_option autoImplicit false
universe u
variable {α : Type u} (xs : List α) [Zero α] [Add α]
```

Because automatic implicit parameters are disabled, the following definition fails:
```lean (error := true) (name := secvars) (keep := false)
def addAll (lst : List β) : β :=
  lst.foldr (init := 0) (· + ·)
```
```leanOutput secvars
Unknown identifier `β`
```

On the other hand, not even {lean}`xs` needs to be written directly in the definition:

```lean
def addAll :=
  xs.foldr (init := 0) (· + ·)
```

:::

To add a section variable to a theorem even if it is not explicitly mentioned in the statement, mark the variable with the {keywordOf Lean.Parser.Command.include}`include` command.
All variables marked for inclusion are added to all theorems.
The {keywordOf Lean.Parser.Command.omit}`omit` command removes the inclusion mark from a variable; it's typically a good idea to use it with {keywordOf Lean.Parser.Command.in}`in`.


```lean (show := false)
section
variable {p : Nat → Prop}
variable (pFifteen : p 15)
```
:::::example "Included and Omitted Section Variables"

This section's variables include a predicate as well as everything needed to prove that it holds universally, along with a useless extra assumption.

```lean
section
variable {p : Nat → Prop}
variable (pZero : p 0) (pStep : ∀ n, p n → p (n + 1))
variable (pFifteen : p 15)
```

However, only {lean}`p` is added to this theorem's assumptions, so it cannot be proved.
```lean (error := true) (keep := false)
theorem p_all : ∀ n, p n := by
  intro n
  induction n
```

The {keywordOf Lean.Parser.Command.include}`include` command causes the additional assumptions to be added unconditionally:
```lean (keep := false) (name := lint)
include pZero pStep pFifteen

theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```
Because the spurious assumption {lean}`pFifteen` was inserted, Lean issues a warning:
```leanOutput lint
automatically included section variable(s) unused in theorem 'p_all':
  pFifteen
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit pFifteen in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

This can be avoided by using {keywordOf Lean.Parser.Command.omit}`omit`to remove {lean}`pFifteen`:
```lean (keep := false)
include pZero pStep pFifteen

omit pFifteen in
theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```

```lean
end
```

:::::
```lean (show := false)
end
```
