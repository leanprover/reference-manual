/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

#doc (Manual) "Files" =>
%%%
tag := "files"
%%%

The smallest unit of compilation in Lean is a single {deftech}[module].
Modules correspond to source files, and are imported into other modules based on their filenames.
In other words, the names and folder structures of files are significant in Lean code.

# Modules
%%%
tag := "modules"
%%%

Every Lean file defines a module.
A module's name is derived from a combination of its filename and the way in which Lean was invoked: Lean has a _root directory_ in which it expects to find code, and the module's name is the names of the directories from the root to the filename, with dots (`.`) interspersed and `.lean` removed.
For example, if Lean is invoked with `Projects/MyLib/src` as its root, the file `Projects/MyLib/src/Literature/Novel/SciFi.lean` would contain a module named `Literature.Novel.SciFi`.

::: TODO
Describe case sensitivity/preservation for filenames here
:::

## Encoding and Representation
%%%
tag := "module-encoding"
%%%

Lean modules are Unicode text files encoded in UTF-8. {TODO}[Figure out the status of BOM and Lean]
Lines may end either with newline characters (`"\n"`, Unicode `'LINE FEED (LF)' (U+000A)`) or with a form feed and newline sequence (`"\r\n"`, Unicode `'CARRIAGE RETURN (CR)' (U+000D)` followed by `'LINE FEED (LF)' (U+000A)`).
However, Lean normalizes line endings when parsing or comparing files, so all files are compared as if all their line endings are `"\n"`.
::: TODO
Marginal note: this is to make cached files and `#guard_msgs` and the like work even when git changes line endings. Also keeps offsets stored in parsed syntax objects consistent.
:::

## Concrete Syntax
%%%
tag := "module-syntax"
%%%


Lean's concrete syntax is extensible.
In a language like Lean, it's not possible to completely describe the syntax once and for all, because libraries may define syntax in addition to new constants or {tech}[inductive types].
Rather than completely describing the language here, the overall framework is described, while the syntax of each language construct is documented in the section to which it belongs.

### Whitespace
%%%
tag := "whitespace"
%%%


Tokens in Lean may be separated by any number of {deftech}[_whitespace_] character sequences.
Whitespace may be a space (`" "`, Unicode `'SPACE (SP)' (U+0020)`), a valid newline sequence, or a comment. {TODO}[xref]
Neither tab characters nor carriage returns not followed by newlines are valid whitespace sequences.

### Comments
%%%
tag := "comments"
%%%


Comments are stretches of the file that, despite not being whitespace, are treated as such.
Lean has two syntaxes for comments:

: Line comments

  A `--` that does not occur as part of a token begins a _line comment_. All characters from the initial `-` to the newline are treated as whitespace.{index (subterm := "line")}[comment]

: Block comments

  A `/-` that does not occur as part of a token and is not immediately followed by a `-` character begins a _block comment_.{index (subterm := "block")}[comment] `/--` begins a documentation string {TODO}[xref] rather than a comment.

### Keywords and Identifiers
%%%
tag := "keywords-and-identifiers"
%%%


An {deftech}[identifier] consists of one or more identifier components, separated by `'.'`.{index}[identifier]

{deftech}[Identifier components] consist of a letter or letter-like character or an underscore (`'_'`), followed by zero or more identifier continuation characters.
Letters are English letters, upper- or lowercase, and the letter-like characters include a range of non-English alphabetic scripts, including the Greek script which is widely used in Lean, as well as the members of the Unicode letter-like symbol block, which contains a number of double-struck characters (including `ℕ` and `ℤ`) and abbreviations.
Identifier continuation characters consist of letters, letter-like characters, underscore (`'_'`), exclamation mark (`!`), question mark (`?`), subscripts, and single quotes (`'`).
As an exception, underscore alone is not a valid identifier.

````lean (show := false)
def validIdentifier (str : String) : IO String :=
  Lean.Parser.identFn.test str

/-- info: "Success! Final stack:\n  `ℕ\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "ℕ"

/-- info: "Failure: expected identifier\nFinal stack:\n  <missing>\nRemaining: \"?\"" -/
#guard_msgs in
#eval validIdentifier "?"

/-- info: "Success! Final stack:\n  `ℕ?\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "ℕ?"

/-- info: "Failure: expected identifier\nFinal stack:\n  <missing>\nRemaining: \"_\"" -/
#guard_msgs in
#eval validIdentifier "_"

/-- info: "Success! Final stack:\n  `_3\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "_3"

/-- info: "Success! Final stack:\n  `_.a\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "_.a"

/-- info: "Success! Final stack:\n  `αποδεικνύοντας\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "αποδεικνύοντας"


/- Here's some things that probably should be identifiers but aren't at the time of writing -/

/-- info: "Success! Final stack:\n  `κύκ\nRemaining:\n\"λος\"" -/
#guard_msgs in
#eval validIdentifier "κύκλος"

/-- info: "Failure: expected token\nFinal stack:\n  <missing>\nRemaining: \"øvelse\"" -/
#guard_msgs in
#eval validIdentifier "øvelse"

/-- info: "Failure: expected token\nFinal stack:\n  <missing>\nRemaining: \"Übersetzung\"" -/
#guard_msgs in
#eval validIdentifier "Übersetzung"

/-- info: "Failure: expected token\nFinal stack:\n  <missing>\nRemaining: \"переклад\"" -/
#guard_msgs in
#eval validIdentifier "переклад"

````

Identifiers components may also be surrounded by double guillemets (`'«'` and `'»'`).
Such identifier components may contain any character at all, aside from `'»'`, even `'«'` and newlines.

```lean (show := false)
/-- info: "Success! Final stack:\n  `«\n  »\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "«\n»"

/-- info: "Success! Final stack:\n  `««one line\n  and another»\nAll input consumed." -/
#guard_msgs in
#eval validIdentifier "««one line\nand another»"
```

Some potential identifier components may be reserved keywords.
The specific set of reserved keywords depends on the set of active syntax extensions, which may depend on the set of imported modules and the currently-opened {TODO}[xref/deftech for namespace] namespaces; it is impossible to enumerate for Lean as a whole.
These keywords must also be quoted with guillemets to be used as identifier components in most syntactic contexts.
Contexts in which keywords may be used as identifiers without guillemets, such as constructor names in inductive types, are {deftech}_raw identifier_ contexts.{index (subterm:="raw")}[identifier]

Identifiers that contain one or more `'.'` characters, and thus consist of more than one identifier component, are called {deftech}[hierarchical identifiers].
Hierarchical identifiers are used to represent both module names and names in a namespace.

## Structure
%%%
tag := "module-structure"
%%%


:::syntax Lean.Parser.Module.module (open := false)
```grammar
$hdr:header $cmd:command*
```

A module consists of a {deftech}_module header_ followed by a sequence of {deftech}_commands_.

:::


### Module Headers
%%%
tag := "module-headers"
%%%


The module header consists of a sequence of {deftech}[`import` statements].

:::syntax Lean.Parser.Module.header (open := false)
```grammar
$i:import*
```

An optional keyword `prelude`, for use in Lean's implementation, is also allowed:

```grammar
prelude $«import»*
```
:::


:::syntax Lean.Parser.Module.prelude (open := false)
```grammar
prelude
```

The `prelude` keyword indicates that the module is part of the implementation of the Lean {deftech}_prelude_, which is the code that is available without explicitly importing any modules—it should not be used outside of Lean's implementation.
:::

:::syntax Lean.Parser.Module.import
```grammar
import $mod:ident
```

Imports the module.
Importing a module makes its contents available in the current module, as well as those from modules transitively imported by its imports.

Modules do not necessarily correspond to namespaces.
Modules may add names to any namespace, and importing a module has no effect on the set of currently open namespaces.

The imported module name is translated to a filename by replacing dots (`'.'`) in its name with directory separators.
Lean searches its include path for the corresponding importable module file.
:::

### Commands
%%%
tag := "commands"
%%%


{tech}[Commands] are top-level statements in Lean.
Some examples are inductive type declarations, theorems, function definitions, namespace modifiers like `open` or `variable`, and interactive queries such as `#check`.
The syntax of commands is user-extensible.
Specific Lean commands are documented in the corresponding chapters of this manual, rather than being listed here.

::: TODO
Make the index include links to all commands, then xref from here
:::

## Contents
%%%
tag := "module-contents"
%%%


A module includes an {TODO}[def and xref] environment, which includes both the inductive type and constant definitions from an environment and any data stored in {TODO}[xref] its environment extensions.
As the module is processed by Lean, commands add content to the environment.
A module's environment can be serialized to a {deftech (key:="olean")}[`.olean` file], which contains both the environment and a compacted heap region with the run-time objects needed by the environment.
This means that an imported module can be loaded without re-executing all of its commands.


# Packages, Libraries, and Targets
%%%
tag := "code-distribution"
%%%


Lean code is organized into {deftech}_packages_, which are units of code distribution.
A {tech}[package] may contain multiple libraries or executables.

Code in a package that is intended for use by other Lean packages is organized into {deftech (key:="library")}[libraries].
Code that is intended to be compiled and run as independent programs is organized into {deftech (key:="executable")}[executables].
Together, libraries and executables are referred to as {deftech}_targets_ in Lake, the standard Lean build tool. {TODO}[section xref]

:::TODO
Write Lake section, coordinate this content with it
:::
