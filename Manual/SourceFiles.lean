/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Source Files and Modules" =>
%%%
tag := "files"
htmlSplit := .never
%%%

The smallest unit of compilation in Lean is a single {deftech}[module].
Modules correspond to source files, and are imported into other modules based on their filenames.
In other words, the names and folder structures of files are significant in Lean code.

Every Lean file defines a module.
A module's name is derived from a combination of its filename and the way in which Lean was invoked: Lean has a _root directory_ in which it expects to find code, and the module's name is the names of the directories from the root to the filename, with dots (`.`) interspersed and `.lean` removed.
For example, if Lean is invoked with `Projects/MyLib/src` as its root, the file `Projects/MyLib/src/Literature/Novel/SciFi.lean` would contain a module named `Literature.Novel.SciFi`.

::: TODO
Describe case sensitivity/preservation for filenames here
:::

# Encoding and Representation
%%%
tag := "module-encoding"
%%%

Lean modules are Unicode text files encoded in UTF-8. {TODO}[Figure out the status of BOM and Lean]
Lines may end either with newline characters (`"\n"`, Unicode `'LINE FEED (LF)' (U+000A)`) or with a form feed and newline sequence (`"\r\n"`, Unicode `'CARRIAGE RETURN (CR)' (U+000D)` followed by `'LINE FEED (LF)' (U+000A)`).
However, Lean normalizes line endings when parsing or comparing files, so all files are compared as if all their line endings are `"\n"`.
::: TODO
Marginal note: this is to make cached files and `#guard_msgs` and the like work even when git changes line endings. Also keeps offsets stored in parsed syntax objects consistent.
:::

# Concrete Syntax
%%%
tag := "module-syntax"
%%%


Lean's concrete syntax is {ref "language-extension"}[extensible].
In a language like Lean, it's not possible to completely describe the syntax once and for all, because libraries may define syntax in addition to new constants or {tech}[inductive types].
Rather than completely describing the language here, the overall framework is described, while the syntax of each language construct is documented in the section to which it belongs.

## Whitespace
%%%
tag := "whitespace"
%%%


Tokens in Lean may be separated by any number of {deftech}[_whitespace_] character sequences.
Whitespace may be a space (`" "`, Unicode `'SPACE (SP)' (U+0020)`), a valid newline sequence, or a comment. {TODO}[xref]
Neither tab characters nor carriage returns not followed by newlines are valid whitespace sequences.

## Comments
%%%
tag := "comments"
%%%


Comments are stretches of the file that, despite not being whitespace, are treated as such.
Lean has two syntaxes for comments:

: Line comments

  A `--` that does not occur as part of a token begins a _line comment_. All characters from the initial `-` to the newline are treated as whitespace.{index (subterm := "line")}[comment]

: Block comments

  A `/-` that does not occur as part of a token and is not immediately followed by a `-` character begins a _block comment_.{index (subterm := "block")}[comment]
  The block comment continues until a terminating `-/` is found.
  Block comments may be nested; a `-/` only terminates the comment if prior nested block comment openers `/-` have been terminated by a matching `-/`.

`/--` and `/-!` begin {deftech}_documentation_ {TODO}[xref] rather than comments, which are also terminated with `-/` and may contain nested block comments.
Even though documentation resembles comments, they are their own syntactic category; their valid placement is determined by Lean's grammar.



## Keywords and Identifiers
%%%
tag := "keywords-and-identifiers"
%%%


An {tech}[identifier] consists of one or more identifier components, separated by `'.'`.{index}[identifier]

{deftech}[Identifier components] consist of a letter or letter-like character or an underscore (`'_'`), followed by zero or more identifier continuation characters.
Letters are English letters, upper- or lowercase, and the letter-like characters include a range of non-English alphabetic scripts, including the Greek script which is widely used in Lean, as well as the members of the Unicode letter-like symbol block, which contains a number of double-struck characters (including `ℕ` and `ℤ`) and abbreviations.
Identifier continuation characters consist of letters, letter-like characters, underscores (`'_'`), exclamation marks (`!`), question marks (`?`), subscripts, and single quotes (`'`).
As an exception, underscore alone is not a valid identifier.

````lean (show := false)
def validIdentifier (str : String) : IO String :=
  Lean.Parser.identFn.test str

/-- info: "Success! Final stack:\n  `ℕ\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"?\"" -/
#check_msgs in
#eval validIdentifier "?"

/-- info: "Success! Final stack:\n  `ℕ?\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ?"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"_\"" -/
#check_msgs in
#eval validIdentifier "_"

/-- info: "Success! Final stack:\n  `_3\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_3"

/-- info: "Success! Final stack:\n  `_.a\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_.a"

/-- info: "Success! Final stack:\n  `αποδεικνύοντας\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "αποδεικνύοντας"


/- Here's some things that probably should be identifiers but aren't at the time of writing -/

/-- info: "Success! Final stack:\n  `κύκ\nRemaining:\n\"λος\"" -/
#check_msgs in
#eval validIdentifier "κύκλος"

/-- info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"øvelse\"" -/
#check_msgs in
#eval validIdentifier "øvelse"

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"Übersetzung\""
-/
#check_msgs in
#eval validIdentifier "Übersetzung"

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"переклад\""
-/
#check_msgs in
#eval validIdentifier "переклад"

````

Identifiers components may also be surrounded by double {deftech}[guillemets] (`'«'` and `'»'`).
Such identifier components may contain any character at all aside from `'»'`, even `'«'`, `'.'`, and newlines.
The guillemets are not part of the resulting identifier component, so `«x»` and `x` denote the same identifier.
`«Nat.add»`, on the other hand, is an identifier with a single component, while `Nat.add` has two.




```lean (show := false)
/-- info: "Success! Final stack:\n  `«\n  »\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«\n»"

/-- info: "Success! Final stack:\n  `««one line\n  and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "««one line\nand another»"

/-- info: "Success! Final stack:\n  `«one line\x00and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x00and another»"

/-- info: "Success! Final stack:\n  `«one line\x0band another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x0Band another»"
```

Some potential identifier components may be reserved keywords.
The specific set of reserved keywords depends on the set of active syntax extensions, which may depend on the set of imported modules and the currently-opened {TODO}[xref/deftech for namespace] namespaces; it is impossible to enumerate for Lean as a whole.
These keywords must also be quoted with guillemets to be used as identifier components in most syntactic contexts.
Contexts in which keywords may be used as identifiers without guillemets, such as constructor names in inductive types, are {deftech}_raw identifier_ contexts.{index (subterm:="raw")}[identifier]

Identifiers that contain one or more `'.'` characters, and thus consist of more than one identifier component, are called {deftech}[hierarchical identifiers].
Hierarchical identifiers are used to represent both module names and names in a namespace.

# Structure
%%%
tag := "module-structure"
%%%


:::syntax Lean.Parser.Module.module (open := false) (title := "Modules")
```grammar
$hdr:header $cmd:command*
```

A module consists of a {deftech}_module header_ followed by a sequence of {deftech}_commands_.

:::


## Module Headers
%%%
tag := "module-headers"
%%%


Module headers list the modules that should be elaborated prior to the current module.
Their declarations are visible in the current module.

:::syntax Lean.Parser.Module.header (open := false) (title := "Module Headers")
The module header consists of a sequence of {deftech}[`import` statements]:
```grammar
$i:import*
```

The optional {keyword}`prelude` keyword should only be used in Lean's source code:
```grammar
prelude
$i:import*
```
:::

If present, the {keyword}`prelude` keyword indicates that the module is part of the implementation of the Lean {deftech}_prelude_, which is the code that is available without explicitly importing any modules—it should not be used outside of Lean's implementation.

:::syntax Lean.Parser.Module.prelude (open := false) (title := "Prelude Modules")
```grammar
prelude
```

:::

:::syntax Lean.Parser.Module.import (title := "Imports")
```grammar
import $mod:ident
```

Imports the module.
Importing a module makes its contents available in the current module, as well as those from modules transitively imported by its imports.

Modules do not necessarily correspond to namespaces.
Modules may add names to any namespace, and importing a module has no effect on the set of currently open namespaces.

The imported module name is translated to a filename by replacing dots (`'.'`) in its name with directory separators and appending `.lean` or `.olean`.
Lean searches its include path for the corresponding intermediate build product or importable module file.
:::

## Commands
%%%
tag := "commands"
%%%


{tech}[Commands] are top-level statements in Lean.
Some examples are inductive type declarations, theorems, function definitions, namespace modifiers like `open` or `variable`, and interactive queries such as `#check`.
The syntax of commands is user-extensible, and commands may even {ref "language-extension"}[add new syntax that is used to parse subsequent commands].
Specific Lean commands are documented in the corresponding chapters of this manual, rather than being listed here.

::: TODO
Make the index include links to all commands, then xref from here
:::

# Elaborated Modules
%%%
tag := "module-contents"
%%%

When Lean elaborates a module, the result is an {TODO}[def and xref] environment.
The environment includes the constants, {tech}[inductive types], {tech}[theorems], {tech key:="type class"}[type classes], {tech}[instances], and everything else declared in the module, along with side tables that track data as diverse as {tech}[simp sets], namespace aliases, and {tech}[documentation comments].

As the module is processed by Lean, commands add content to the environment.
A module's environment can be serialized to a {deftech (key:="olean")}[`.olean` file], which contains both the environment and a compacted heap region with the run-time objects needed by the environment.
This means that an imported module can be loaded without re-executing all of its commands.


# Packages, Libraries, and Targets
%%%
tag := "code-distribution"
%%%


Lean modules are organized into {deftech}_packages_, which are units of code distribution.
A {tech}[package] may contain multiple libraries or executables.

Code in a package that is intended for use by other Lean packages is organized into {deftech (key:="library")}[libraries].
Code that is intended to be compiled and run as independent programs is organized into {deftech (key:="executable")}[executables].
Packages, libraries, and executables are described in detail in the section on {ref "lake"}[Lake, the standard Lean build tool].
