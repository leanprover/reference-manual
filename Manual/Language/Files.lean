import Verso.Genre.Manual

import Manual.Meta

open Verso.Genre Manual

#doc (Manual) "Files" =>

# Modules

Every Lean file defines a module.
A module's name is derived from a combination of its filename and the way in which Lean was invoked: Lean has a _root directory_ in which it expects to find code, and the module's name is the names of the directories from the root to the filename, with dots (`.`) interspersed and `.lean` removed.
For example, if Lean is invoked with `Projects/MyLib/src` as its root, the file `Projects/MyLib/src/Literature/Novel/SciFi.lean` would contain a module named `Literature.Novel.SciFi`.

::: TODO
Describe case sensitivity/preservation for filenames here
:::

## Encoding and Representation

Lean modules are Unicode text files encoded in UTF-8. {TODO}[Figure out the status of BOM and Lean]
Lines may end either with newline characters (`"\n"`, Unicode `'LINE FEED (LF)' (U+000A)`) or with a form feed and newline sequence (`"\r\n"`, Unicode `'CARRIAGE RETURN (CR)' (U+000D)` followed by `'LINE FEED (LF)' (U+000A)`).
However, Lean normalizes line endings when parsing or comparing files, so all files are compared as if all their line endings are `"\n"`.
::: TODO
Marginal note: this is to make cached files and `#guard_msgs` and the like work even when git changes line endings. Also keeps offsets stored in parsed syntax objects consistent.
:::

## Concrete Syntax

Lean's concrete syntax is extensible.
In a language like Lean, it's not possible to completely describe the syntax once and for all, because libraries may define syntax in addition to new constants or datatypes.
Rather than completely describing the language here, the overall framework is described, while the syntax of each language construct is documented in the section to which it belongs.

### Whitespace

Tokens in Lean may be separated by any number of {deftech}[_whitespace_] character sequences.
Whitespace may be a space (`" "`, Unicode `'SPACE (SP)' (U+0020)`), a valid newline sequence, or a comment. {TODO}[xref]
Neither tab characters nor carriage returns not followed by newlines are valid whitespace sequences.

### Comments

Comments are stretches of the file that, despite not being whitespace, are treated as such.
Lean has two syntaxes for comments:

: Line comments

  A `--` that does not occur as part of a token begins a _line comment_. All characters from the initial `-` to the newline are treated as whitespace.{index (subterm := "line")}[comment]

: Block comments

  A `/-` that does not occur as part of a token and is not immediately followed by a `-` character begins a _block comment_.{index (subterm := "block")}[comment] `/--` begins a documentation string {TODO}[xref] rather than a comment.

### Keywords and Identifiers

An {deftech}[identifier] consists of one or more identifier components, separated by `'.'`.{index}[identifier]

{deftech}[Identifier components] consist of a letter or letterlike character or an underscore (`'_'`), followed by zero or more identifier continuation characters.
Letters are English letters, upper- or lowercase, and the letterlike characters include a range of non-English alphabetic scripts, including the Greek script which is widely used in Lean, as well as the members of the Unicode letterlike symbol block, which contains a number of double-struck characters (including `ℕ` and `ℤ`) and abbreviations.
Identifier continuation characters consist of letters, letterlike characters, underscore (`'_'`), exclamation mark (`!`), question mark (`?`), subscripts, and single quotes (`'`).
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
Contexts in which keywords may be used as identifiers without guillemets, such as constructor names in inductive datatypes, are _raw identifier_ contexts.{index (subterm:="raw")}[identifier]

Identifiers that contain one or more `'.'` characters, and thus consist of more than one identifier component, are called {deftech}[hierarchical identifiers].
Hierarchical identifiers are used to represent both module names and names in a namespace.


# Packages, Libraries, and Targets

Lean code is organized into {deftech}_packages_, which are units of code distribution.
A {tech}[package] may contain multiple libraries or executables.

Code in a package that is intended for use by other Lean packages is organized into {deftech (key:="library")}[libraries].
