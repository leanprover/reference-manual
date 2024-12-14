/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Language.Classes
import Manual.Language.Files
import Manual.Language.Types
import Manual.Language.RecursiveDefs

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

#doc (Manual) "The Lean Language" =>

{include 0 Manual.Language.Files}

{include 0 Manual.Language.Types}

# Module Contents

As described {ref "module-structure"}[in the section on the syntax of files], a Lean module consists of a header followed by a sequence of commands.

## Commands and Declarations

After the header, every top-level phrase of a Lean module is a command.
Commands may add new types, define new constants, or query Lean for information.
Commands may even {ref "language-extension"}[change the syntax used to parse subsequent commands].

::: planned 100
 * Describe the various families of available commands (definition-like, `#eval`-like, etc).
 * Refer to specific chapters that describe major commands, such as `inductive`.
:::

### Definition-Like Commands

::: planned 101
 * Precise descriptions of these commands and their syntax
 * Comparison of each kind of definition-like command to the others
:::

The following commands in Lean are definition-like: {TODO}[Render commands as their name (a la tactic index)]
 * {syntaxKind}`def`
 * {syntaxKind}`abbrev`
 * {syntaxKind}`example`
 * {syntaxKind}`theorem`

All of these commands cause Lean to {tech key:="elaborator"}[elaborate] a term based on a signature.
With the exception of {syntaxKind}`example`, which discards the result, the resulting expression in Lean's core language is saved for future use in the environment.
The {keywordOf Lean.Parser.Command.declaration}`instance` command is described in the {ref "instance-declarations"}[section on instance declarations].

:::syntax Lean.Parser.Command.declaration
```grammar
$_:declModifiers
$_:definition
```
:::

:::syntax Lean.Parser.Command.definition
```grammar
def $_ $_ := $_
```

```grammar
def $_ $_
  $[| $_ => $_]*
```

```grammar
def $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.theorem
```grammar
theorem $_ $_ := $_
```

```grammar
theorem $_ $_
  $[| $_ => $_]*
```

```grammar
theorem $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.abbrev
```grammar
abbrev $_ $_ := $_
```

```grammar
abbrev $_ $_
  $[| $_ => $_]*
```

```grammar
abbrev $_ $_ where
  $_*
```
:::



:::syntax Lean.Parser.Command.example
```grammar
example $_ $_ := $_
```

```grammar
example $_ $_
  $[| $_ => $_]*
```

```grammar
example $_ $_ where
  $_*
```
:::

{deftech}_Opaque constants_ are defined constants that cannot be reduced to their definition.

:::syntax Lean.Parser.Command.opaque
```grammar
opaque $_ $_
```
:::

:::syntax Lean.Parser.Command.axiom
```grammar
axiom $_ $_
```
:::


### Modifiers
%%%
tag := "declaration-modifiers"
%%%

::: planned 52

A description of each modifier allowed in the production `declModifiers`, including {deftech}[documentation comments].

:::

:::syntax declModifiers alias:=Lean.Parser.Command.declModifiers

```grammar
$_
$_
$_
$_
$_
$_
```

:::

### Signatures

:::planned 53

Describe signatures, including the following topics:
 * Explicit, implicit, instance-implicit, and strict implicit parameter binders
 * {deftech key := "optional parameter"}[Optional] and {deftech}[automatic parameters]
 * {deftech}_Automatic implicit_ parameters
 * Argument names and by-name syntax
 * Which parts can be omitted where? Why?

:::

### Headers

The {deftech}[_header_] of a definition or declaration specifies the signature of the new constant that is defined.

::: TODO
* Precision and examples; list all of them here
* Mention interaction with autoimplicits
:::

## Namespaces
%%%
tag := "namespaces"
%%%

:::planned 210

Describe {deftech}[namespaces], aliases, and the semantics of `export` and `open`.
Which language features are controlled by the currently open namespaces?

:::

## Section Scopes
%%%
tag := "scopes"
%%%

::: planned 54

Many commands have an effect for the current {deftech}[_section scope_] (sometimes just called "scope" when clear).
A section scope ends when a namespace ends, a section ends, or a file ends.
They can also be anonymously and locally created via `in`.
Section scopes track the following:
 * The {deftech}_current namespace_
 * The {deftech key:="open namespace"}_open namespaces_
 * The values of all {deftech}_options_
 * {deftech}[Section variable] and universe declarations

This section will describe this mechanism.

:::

:::syntax attrKind (open := false)
Globally-scoped declarations (the default) are in effect whenever the {tech}[module] in which they're established is transitively imported.
They are indicated by the absence of another scope modifier.
```grammar
```

Locally-scoped declarations are in effect only for the extent of the {tech}[section scope] in which they are established.
```grammar
local
```

Scoped declarations are in effect whenever the {tech key:="open namespace"}[namespace] in which they are established is opened.
```grammar
scoped
```
:::

# Axioms

:::planned 78
Describe {deftech}_axioms_ in detail
:::

{include 0 Manual.Language.RecursiveDefs}





# Attributes
%%%
tag := "attributes"
%%%

:::planned 144
 * Concrete syntax of {deftech}[attributes]
 * Use cases
 * Scope
 * When can they be added?
:::

{include 0 Manual.Language.Classes}

# Dynamic Typing

{docstring TypeName}

{docstring Dynamic}

{docstring Dynamic.mk}

{docstring Dynamic.get?}

# Coercions
%%%
tag := "coercions"
%%%

:::planned 146
 * {deftech}[Coercions]
 * When they are inserted
 * Varieties of coercions
 * When should each be used?
:::
