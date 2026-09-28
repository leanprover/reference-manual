/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean

#doc (Manual) "Parser Invariants" =>
%%%
tag := "parser-syntax-invariants"
%%%


:::sectionNote
This section is primarily useful for authors of custom parsers that extend Lean's syntax in ways that are not supported by the standard extension mechanisms.
Ordinary syntax extensions automatically satisfy the invariants described in this section.
:::

Lean's built-in parsing framework produces syntax trees that satisfy a number of invariants that are not guaranteed by the {name}`Syntax` type.
These invariants do not need to hold for all syntax; only that which is directly produced from a file.
Syntax trees that result from {ref "macro-and-elab"}[macros], {ref "quotation"}[quotation], {ref "delaborators"}[delaborators], or other sources are not expected to obey these invariants.

Syntax extensions that are defined through {ref "notations"}[notations] and {ref "syntax-rules"}[syntax rules] automatically satisfy the invariants.
However, it is also possible to extend Lean's parser using lower-level tools, in which case parser authors must ensure that the parser's output is correct.

In particular, the language server and {tech (key := "Lean elaborator")}[elaborator] expect these invariants to hold.
When they do not, interactive features may stop working with no error reported.

The parser invariants are only expected to hold when a parser completes without reporting any errors (that is, when {name Lean.Parser.ParserState.allErrors}`ParserState.allErrors` returns an empty array).
The result of a successful parse must not contain {name Syntax.missing}`missing` syntax.
Failing parsers insert {name Syntax.missing}`missing` syntax at the site of failures, resulting in a parse tree that may not be entirely useless.
While many language features do not work as well on incomplete syntax trees, the elaborator and the language server attempt to provide useful information even about Lean code that is not syntactically well-formed.


# Syntax Kinds

Every syntax kind produced by the parser must have a formatter and parenthesizer.
Lean uses the formatter and parenthesizer to display the syntax in error messages, proof states, and other user feedback.

:::paragraph
The formatter and parenthesizer can be obtained in two ways:
* The {attrs}`@[formatter k]` and {attrs}`@[parenthesizer k]` attributes allow formatters and parenthesizers to be registered directly for syntax kind `k`.
* If there is no registered formatter or parenthesizer, then Lean interprets `k` as the name of the parser that produced the syntax and, if `k` is a constant of type {name}`ParserDescr`, attempts to obtain formatters and parenthesizers based on `k`'s definition.
  The value of a {name}`ParserDescr` description is interpreted to format or parenthesize the syntax, recursively using registered combinator formatters or combinator parenthesizers.
  Otherwise, the process fails with an error message.
:::

At declaration time, Lean automatically creates formatters and parenthesizers for parsers that are declared using {ref "syntax-rules"}[syntax declarations] or with category attributes such as {attrs}`@[term_parser]` by compiling their definitions using a process similar to the interpretation of parser descriptor values.
In the parser's definition, each parser is replaced by its formatter or parenthesizer, and each combinator by the formatter or parenthesizer registered via the {attrs}`@[combinator_formatter p]` or {attrs}`@[combinator_parenthesizer p]` attributes.
For parameterless parsers, the resulting formatter and parenthesizer are registered with the {attrs}`@[formatter k]` and {attrs}`@[parenthesizer k]` attributes when an examination of their definition shows that they unconditionally create a node of kind `k`.
For all parsers, {attrs}`@[combinator_formatter p]` or {attrs}`@[combinator_parenthesizer p]` entries are registered.

The {attr}`run_parser_attribute_hooks` attribute invokes this compilation process on a parser definition that does not result from a syntax rule or have a parser attribute.
If this is not done, modules that import the parser will not be able to format or parenthesize its syntax.
This failure manifests in _downstream_ modules that import the parser, so it can be difficult to notice.
Low-level parsers are typically defined using {name Parser.Parser.mk}`Parser.mk` rather than an existing combinator, so they require hand-written formatters and parenthesizers.

```lean -show -keep
-- Verify claims about formatter and parenthesizer registration
open Lean.Parser Lean.PrettyPrinter

-- Parameterless, unconditionally a node of kind `fixedKind`
@[term_parser]
def fixedKind : Parser := node `fixedKind (symbol "fixed" >> ident)

-- Parameterless, but the kind depends on the input
@[term_parser]
def eitherKind : Parser := node `kindA (symbol "ka") <|> node `kindB (symbol "kb")

-- Parameterized, unconditionally a node of kind `withParam`
@[run_parser_attribute_hooks]
def withParam (p : Parser) : Parser := node `withParam (symbol "wp" >> p)

/--
info: fixedKind: [fixedKind.formatter] [fixedKind.parenthesizer]
kindA: [] []
kindB: [] []
withParam: [] []
fixedKind: some (fixedKind.formatter) some (fixedKind.parenthesizer)
eitherKind: some (eitherKind.formatter) some (eitherKind.parenthesizer)
withParam: some (withParam.formatter) some (withParam.parenthesizer)
-/
#check_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let mut lines := #[]
  for k in [`fixedKind, `kindA, `kindB, `withParam] do
    lines := lines.push m!"{k}: {(formatterAttribute.getEntries env k).map (·.declName)} {(parenthesizerAttribute.getEntries env k).map (·.declName)}"
  for p in [``fixedKind, ``eitherKind, ``withParam] do
    lines := lines.push m!"{p}: {combinatorFormatterAttribute.getDeclFor? env p} {combinatorParenthesizerAttribute.getDeclFor? env p}"
  logInfo (MessageData.joinSep lines.toList "\n")
```

:::example "Formatter and Parenthesizer"
```imports -show
import Lean
```
```lean -show
open Lean
```
The parser {name}`palindromeIdent` matches identifiers that are the same when reversed:
```lean
open Lean.Parser Lean.Elab.Command

def palindromeIdentFn : ParserFn := fun c s =>
  let s := ident.fn c s
  let stx := s.stxStack.back
  if s.hasError || !stx.isIdent then s
  else
    let str := stx.getId.toString
    if str.toList == str.toList.reverse then s
    else s.mkUnexpectedTokenError "palindrome"

def palindromeIdent : Parser := { fn := palindromeIdentFn }
```

Because {name}`palindromeIdent` is not a {name}`ParserDescr`, it cannot be immediately used in term parsers, which require there to be a registered combinator formatter and combinator parenthesizer:
```lean +error -keep (name := palindromeAttr)
@[term_parser]
def palindromeTerm : Parser :=
  leading_parser "palindrome " >> palindromeIdent
```
```leanOutput palindromeAttr
don't know how to generate formatter for non-definition `{ fn := palindromeIdentFn }`
```

Adding the formatter and parenthesizer enables the parser to be used as expected in a term:
```lean
open Lean.PrettyPrinter in
@[combinator_formatter palindromeIdent]
def palindromeIdent.formatter : Formatter := Parser.ident.formatter

open Lean.PrettyPrinter in
@[combinator_parenthesizer palindromeIdent]
def palindromeIdent.parenthesizer : Parenthesizer :=
  Parser.ident.parenthesizer

@[term_parser]
def palindromeTerm : Parser :=
  leading_parser "palindrome " >> palindromeIdent

macro_rules
  | `(palindrome $p:ident) => pure p
```

```lean (name := palindromeCheck)
def level := 1

#check palindrome level
```
```leanOutput palindromeCheck
level : Nat
```

```lean +error (name := palindromeCheck2)
#check palindrome abc
```
```leanOutput palindromeCheck2
unexpected identifier; expected palindrome
```
:::


# Source Fidelity
%%%
tag := "parser-invariant-source-fidelity"
%%%

:::paragraph
All parsers must ensure that the syntax trees they produce are faithful to the original source code.
In other words, when a parser succeeds, the resulting syntax tree must account for each character that the parser consumed.
The character may be accounted for in any of the following ways:

* It can be part of the {ref "source-info"}[leading or trailing whitespace] of the syntax's source information.
* It can be part of an {name Syntax.atom}`atom`.
* It can be the raw value of an {name Syntax.ident}`ident`.

All substrings that occur in the tree, such as in identifier raw values and leading and trailing whitespace, must be substrings of the original input string.
Their byte offsets must reflect the actual positions at which they were obtained.
:::

A consequence of these properties is that both atom values and identifier raw values should be stored exactly as they occurred in the text.
There should be no normalization of escape sequences.
For example, parsing {lean}`"«Nat»"` should result in an identifier whose raw value is `"«Nat»"` and whose value is {lean}`` `Nat ``, and literals that represent the same string differently via choices of escapes should parse to distinct atoms.

```lean -show -keep
-- Verify claims about raw identifier values and literal atoms
open Lean Elab Command

def parseTerm (str : String) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term str with
  | .ok stx => pure stx
  | .error e => throwError e

-- The raw value keeps the guillemets; the value does not
/-- info: ("«Nat»", `Nat) -/
#check_msgs in
#eval do
  let stx ← parseTerm "«Nat»"
  let .ident _ raw val _ := stx | throwError "not an identifier"
  return (raw.toString, val)

-- Two spellings of one string are the same literal but distinct atoms
/-- info: (some "A", some "A", "\"\\x41\"", "\"A\"") -/
#check_msgs in
#eval do
  let a ← parseTerm "\"\\x41\""
  let b ← parseTerm "\"A\""
  return (a.isStrLit?, b.isStrLit?, a[0].getAtomVal, b[0].getAtomVal)
```

Each alternative in a {tech}[choice node] must cover the same original region of the input.
The alternatives provide different interpretations of the same region, rather than different regions.
Each direct child of the choice node is one of the alternatives, and none should be considered “canonical” or otherwise preferred.
There is no guarantee that the alternatives have the same node kind or that they have anything else in common.

Traversing a syntax tree from left to right, top to bottom, concatenating all leading whitespace, atom values, identifier raw values, and trailing whitespace must result in the same string as the prefix of the input that the parser consumed.
During this process, any arbitrary alternative may be selected for a choice node.
{name}`Syntax.reprint` implements this traversal.

# Whitespace
%%%
tag := "parser-invariant-whitespace"
%%%

The leading and trailing whitespace fields of {name}`SourceInfo.original` contain both whitespace and comments.
Every region of the input that is not an atom or an identifier's raw value must be accounted for as whitespace.
In all but the file's first token, the leading whitespace field must be empty, and all whitespace must be saved as trailing whitespace.
The first token in a source file must have the file's leading whitespace in its leading field.

While leading whitespace does not break the {ref "parser-invariant-source-fidelity"}[source fidelity] property, many components in Lean assume that there is no leading whitespace.
The `ws`, `noWs`, and `linebreak` parsers inspect the preceding token's trailing whitespace, for example; capturing this whitespace in the next token's leading field would mean that they operate incorrectly.
Similarly, the language server consults only trailing whitespace fields when associating empty space with a proof state to be shown.


# Source Information
%%%
tag := "parser-invariant-sourceinfo"
%%%

{name}`Syntax` produced by a parser must store all {ref "source-info"}[source information] on tokens (that is, atoms and identifiers).
This source information must always be {name SourceInfo.original}`original`; {name SourceInfo.synthetic}`synthetic` or missing source information on tokens is reserved for syntax created by a macro or the {ref "delaborators"}[delaborator].

{name}`Syntax.node` must always have its source information field set to {name}`SourceInfo.none`.
The range of a node is calculated from the source information of its first and last tokens.

Because tokens must be stored in source order to satisfy the {ref "parser-invariant-source-fidelity"}[source fidelity] invariant, the range of a node automatically contains the ranges of its children, and each child occupies a disjoint region of the input.
Furthermore, source positions are nondecreasing during a left-to-right traversal of the syntax.
The only exceptions to this property in correctly-produced parser output are choice nodes, whose alternatives must overlap.
However, within the choice node, each alternative must obey the source information invariant.

# Arity and Null Nodes
%%%
tag := "parser-invariant-arity"
%%%

Each node kind that the parser introduces must have a fixed arity.
In other words, the size of the node's array of children must be determined by its syntax kind.
Similarly, a node's kind {ref "parser-invariant-atoms"}[determines its atoms].
Absent optional components should be represented by empty null nodes.
Consumers check for the presence or absence of these values using {name}`Syntax.isNone` and {name}`Syntax.getOptional?`, which rely on the arity of the null node.
The potential presence of empty null nodes in parsed syntax means that not every subtree returned by a parser has a meaningful source range.

:::paragraph
Four syntax kinds may have variable arity:

: Null nodes ({name}`nullKind`)

  Null nodes may have any number of children.
  All repetition and optional values are represented by null nodes.
  For example, syntax that consists of an optional bracketed list of comma-separated terms can be represented as either an empty null node or a three-element null node, the second element of which is itself a null node that contains alternating terms and commas.

: Group nodes ({name}`groupKind`)

  Group nodes may have any number of children, but they are expected to have the same arity in any given context.
  They result from repetition and alternation operators whose components have arity greater than one, and are typically not needed in hand-written parsers.

: Choice nodes ({name}`choiceKind`)

  {tech}[Choice nodes] must have at least two children.
  They represent alternative parses of the same input to be resolved later during elaboration.

: Interpolations ({name}`interpolatedStrKind`)

  String interpolation nodes have an odd number of children, alternating between string segments and interpolated syntax.
  String segments have kind {name}`interpolatedStrLitKind`, each of which contains a single atom.

:::

Each parser should additionally have a fixed arity with respect to the internal parsing stack.
On each execution path, the parser should push the same number of syntax items to the stack, pushing {name}`Syntax.missing` if an error prevents the syntax from being created and an empty null node if the lack of a value is expected.

```lean -show -keep
-- Verify claims about null, group, choice, and interpolation node arity
open Lean Elab Command

partial def shape : Syntax → String
  | .node _ k args => s!"({k}" ++ String.join (args.toList.map (" " ++ shape ·)) ++ ")"
  | .atom _ v => v.quote
  | .ident _ _ v _ => s!"`{v}"
  | .missing => "<missing>"

def parseTerm (str : String) : CommandElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term str with
  | .ok stx => pure stx
  | .error e => throwError e

def showShape (str : String) : CommandElabM Unit := do
  logInfo (shape (← parseTerm str))

-- An optional bracketed list: an empty null node, or a three-element null node
-- whose middle element is the alternating list
syntax "tuple" ("[" term,* "]")? : term

/-- info: («termTuple[_]» "tuple" (null)) -/
#check_msgs in
#eval showShape "tuple"

/-- info: («termTuple[_]» "tuple" (null "[" (null `a "," `b) "]")) -/
#check_msgs in
#eval showShape "tuple [a, b]"

-- Presence is read off the null node's arity
/-- info: true -/
#check_msgs in
#eval do return (← parseTerm "tuple")[1].isNone

/-- info: false -/
#check_msgs in
#eval do return (← parseTerm "tuple [a, b]")[1].isNone

-- The empty null node has no source position
/-- info: true -/
#check_msgs in
#eval do return (← parseTerm "tuple")[1].getPos?.isNone

-- Repetition of a component with arity greater than one produces group nodes
syntax "rep" ("a" term)* : term

/-- info: (termRepA_ "rep" (null (group "a" `x) (group "a" `y))) -/
#check_msgs in
#eval showShape "rep a x a y"

-- Ambiguity produces a choice node with one child per alternative
syntax "amb" ident : term
syntax "amb" term : term

/-- info: (choice (termAmb__1 "amb" `x) (termAmb_ "amb" `x)) -/
#check_msgs in
#eval showShape "amb x"

-- Interpolated strings alternate literal segments and terms, starting and ending with a segment
/-- info: (termS!_ "s!" (interpolatedStrKind (interpolatedStrLitKind "\"a{") `x (interpolatedStrLitKind "}b\""))) -/
#check_msgs in
#eval showShape "s!\"a{x}b\""
```


# Kinds Determine Atoms
%%%
tag := "parser-invariant-atoms"
%%%

Lean's syntax pattern matching does not check the string content of a {name}`Syntax.atom`.
Instead, it checks node kinds, assuming that atoms' values are uniquely determined.
This means that parsers should not assume that their consumers will distinguish the atom values.
A choice among tokens should be expressed as distinct node kinds or as the {ref "parser-invariant-arity"}[arity of a null node], rather than as atom content.

Identifiers are compared by their decoded value, modulo erasing macro scopes, so they are not part of this invariant.
There are five exceptions to this rule, all of them used for literals.
In particular, atom values are compared for equality during syntax matching inside the syntax kinds recognized by {name}`isLitKind`, namely {lean}`` `str ``, {lean}`` `num ``, {lean}`` `char ``,  {lean}`` `name ``, and {lean}`` `scientific ``.
Parsers may assume that syntax patterns will distinguish these values when matching the returned syntax.

```lean -show -keep
-- Verify claims about literal and identifier matching
def whichLit : Syntax → String
  | `(5) => "five"
  | `("a") => "string a"
  | `('c') => "char c"
  | `(`n) => "name n"
  | `(1.5) => "scientific 1.5"
  | `(x) => "ident x"
  | _ => "other"

/-- info: "five" -/
#check_msgs in
#eval do return whichLit (← `(5))

/-- info: "other" -/
#check_msgs in
#eval do return whichLit (← `(6))

/-- info: "string a" -/
#check_msgs in
#eval do return whichLit (← `("a"))

/-- info: "other" -/
#check_msgs in
#eval do return whichLit (← `("b"))

/-- info: "char c" -/
#check_msgs in
#eval do return whichLit (← `('c'))

/-- info: "other" -/
#check_msgs in
#eval do return whichLit (← `('d'))

/-- info: "name n" -/
#check_msgs in
#eval do return whichLit (← `(`n))

/-- info: "other" -/
#check_msgs in
#eval do return whichLit (← `(`m))

/-- info: "scientific 1.5" -/
#check_msgs in
#eval do return whichLit (← `(1.5))

/-- info: "other" -/
#check_msgs in
#eval do return whichLit (← `(2.5))

/-- info: "ident x" -/
#check_msgs in
#eval do return whichLit (← `(x))

/-- info: "other" -/
#check_msgs in
#eval do return whichLit (← `(y))
```

:::example "Atom Content"
```imports -show
import Lean
```
```lean -show
open Lean
```
This syntax declaration creates a new term that accepts two different atoms:
```lean
syntax "kw" ("green" <|> "blue") : term
```
Internally, each branch of the alternatives is assigned its own node with a kind name derived from the atom that it recognizes, allowing syntax pattern matching to ignore the actual atom values:
```lean (name := kwKinds)
#eval do
  let greenStx ← `(kw green)
  let blueStx ← `(kw blue)
  logInfo m!"{greenStx.raw[1].getKind} {blueStx.raw[1].getKind}"
```
```leanOutput kwKinds
token.green token.blue
```

This recognizer function checks only these node kinds:
```lean (name := kwMatch)
def whichKw : Syntax → String
  | `(kw green) => "green"
  | `(kw blue) => "blue"
  | _ => "other"

#eval do
  logInfo m!"{whichKw (← `(kw green))} {whichKw (← `(kw blue))}"
```
```leanOutput kwMatch
green blue
```

This can be seen by replacing the value of one atom with another:
```lean (name := fake)
#eval do
  let greenStx ← `(kw green)
  let greenStx := greenStx.raw.replaceM (m := Id) fun
    | .atom info "green" => pure (some (Syntax.atom info "blue"))
    | _ => pure none
  logInfo m!"Contents: {greenStx}\nSeen as: {whichKw greenStx}"
```
```leanOutput fake
Contents: (termKwGreenBlue "kw" (token.green "blue"))
Seen as: green
```


When the alternative's cases are sequences, a group node is inserted.
Lean does not add node kind wrappers because a singleton atom is not being parsed.
Here, both alternatives have the same kind, {lean}`` `group ``:
```lean (name := kw2Kinds)
syntax "kw2" (("green" term) <|> ("blue" term)) : term

#eval do
  let greenStx ← `(kw2 green 1)
  let blueStx ← `(kw2 blue 1)
  logInfo m!"{greenStx.raw[1].getKind} {blueStx.raw[1].getKind}"
```
```leanOutput kw2Kinds
group group
```

This means that a syntax pattern match fails to distinguish them:
```lean (name := kw2Match)
def whichKw2 : Syntax → String
  | `(kw2 green $_) => "green"
  | _ => "other"

#eval do
  logInfo m!"{whichKw2 (← `(kw2 green 1))} {whichKw2 (← `(kw2 blue 1))}"
```
```leanOutput kw2Match
green green
```

The issue can also be seen in a syntax match that attempts to use both cases:
```lean +error (name := kw2Redundant)
def whichKw2' : Syntax → String
  | `(kw2 green $_) => "green"
  | `(kw2 blue $_) => "blue"
  | _ => "other"
```
```leanOutput kw2Redundant
redundant alternative #2
```

:::


# Parse Errors

If parsing failed, then the returned syntax tree is not expected to obey the other invariants.
Parsing is considered to have failed when {name Lean.Parser.ParserState.allErrors}`ParserState.allErrors` returns a non-empty array.
{name}`Syntax.missing` should occur only if there was a parse error.
Not all parse errors result in syntax trees that contain {name Syntax.missing}`missing`, however; for example, the parse error that occurs if tab characters are mixed with indentation does not correspond to any particular missing sub-term.
Returning a tree that contains {name Syntax.missing}`missing` allows the parser to provide a partial parse tree that may be useful for interactive features such as completion.
Instead of using {name}`Syntax.missing`, empty sequences or optional elements that are not present should be represented by empty null nodes.
To check whether a {name}`Syntax` tree contains {name Syntax.missing}`missing`, use {name}`Syntax.hasMissing`.


# Commands

{tech}[Command] parsing proceeds in a loop in which each iteration parses a command and then elaborates it prior to parsing the next command.
This allows each command's elaboration to affect the parsing of subsequent commands (e.g. by defining new syntax or opening a namespace).
The parsing loop also includes error recovery heuristics.

Each command must contain at least one token with source information.
The only exception is that the final command in a module is always the command {name}`Lean.Parser.Command.eoi`, with an empty token located at the precise end of the file.

A single command parser should obey all the parser invariants.
However, there are a few ways that their composition in the command loop might not satisfy all the invariants.
This behavior is expected, and tools that analyze the result of parsing a Lean module must take it into account.

A {deftech}_terminal command_ is a command that halts Lean's processing of the file.
After a terminal command, further commands are neither parsed nor elaborated.
Terminal commands include {keywordOf Lean.Parser.Command.exit}`#exit`, which is used to intentionally stop processing files, as well as unrecoverable errors such as an {keywordOf Lean.Parser.Command.import}`import` after the {tech}[file header].{margin}[The {ref "module-structure"}[structure of modules], including the module header, is described in the section on source files.
]
To check whether a command is terminal, use {name}`Lean.Parser.isTerminalCommand`.

```lean -show -keep
-- Verify claims about the command loop, terminal commands, and the end-of-input command
open Lean Parser Elab Command

def commandKinds (input : String) : CommandElabM (List Name) := do
  let ictx := mkInputContext input "<input>"
  let pmctx : ParserModuleContext := { env := ← getEnv, options := {} }
  let mut st : ModuleParserState := {}
  let mut msgs : MessageLog := {}
  let mut kinds := []
  repeat
    let (stx, st', msgs') := parseCommand ictx pmctx st msgs
    st := st'; msgs := msgs'
    kinds := kinds ++ [stx.getKind]
    if isTerminalCommand stx then break
  return kinds

def lastCommand (input : String) : CommandElabM Syntax := do
  let ictx := mkInputContext input "<input>"
  let pmctx : ParserModuleContext := { env := ← getEnv, options := {} }
  let mut st : ModuleParserState := {}
  let mut msgs : MessageLog := {}
  repeat
    let (stx, st', msgs') := parseCommand ictx pmctx st msgs
    st := st'; msgs := msgs'
    if isTerminalCommand stx then return stx
  unreachable!

-- A clean file ends with the end-of-input command
/-- info: [`Lean.Parser.Command.declaration, `Lean.Parser.Command.eoi] -/
#check_msgs in
#eval commandKinds "def f := 1\n"

-- Nothing after `#exit` is parsed
/-- info: [`Lean.Parser.Command.declaration, `Lean.Parser.Command.exit] -/
#check_msgs in
#eval commandKinds "def f := 1\n#exit\ndef g := 2\n"

-- An `import` after the header is terminal
/-- info: [`Lean.Parser.Command.declaration, `Lean.Parser.Command.import] -/
#check_msgs in
#eval commandKinds "def f := 1\nimport Foo\ndef g := 2\n"

-- The end-of-input command has an empty token at the end of the file
/-- info: (`Lean.Parser.Command.eoi, "", some 11, some 11, 11) -/
#check_msgs in
#eval do
  let input := "def f := 1\n"
  let stx ← lastCommand input
  return (stx.getKind, stx[0].getAtomVal, stx.getPos?.map String.Pos.Raw.byteIdx, stx.getTailPos?.map String.Pos.Raw.byteIdx, input.utf8ByteSize)

def parseCommands (input : String) :
    CommandElabM (List Name × Nat × Bool) := do
  let ictx := mkInputContext input "<input>"
  let pmctx : ParserModuleContext := { env := ← getEnv, options := {} }
  let mut st : ModuleParserState := {}
  let mut msgs : MessageLog := {}
  let mut kinds := []
  let mut anyMissing := false
  repeat
    let (stx, st', msgs') := parseCommand ictx pmctx st msgs
    st := st'; msgs := msgs'
    kinds := kinds ++ [stx.getKind]
    anyMissing := anyMissing || stx.hasMissing
    if isTerminalCommand stx then break
  return (kinds, msgs.toArray.size, anyMissing)

-- A stray token yields a diagnostic and no syntax tree
/-- info: ([`Lean.Parser.Command.declaration, `Lean.Parser.Command.eoi], 1, false) -/
#check_msgs in
#eval parseCommands ")\ndef f := 1\n"

-- While recovering, a further token-less command is discarded without a diagnostic
/-- info: ([`Lean.Parser.Command.declaration, `Lean.Parser.Command.eoi], 1, false) -/
#check_msgs in
#eval parseCommands ") )\ndef f := 1\n"

-- A tab in leading whitespace is a parse error with no missing syntax
/-- info: ([`Lean.Parser.Command.declaration, `Lean.Parser.Command.eoi], 1, false) -/
#check_msgs in
#eval parseCommands "\tdef f := 1\n"
```



# Checking Invariants

:::paragraph
When testing a parser, it can be helpful to check whether it preserves these syntax invariants.
When applied to a corpus of inputs, the result of each parse can be checked:

: Original {name}`SourceInfo` and no leading whitespace

  Checking that all source information is {name SourceInfo.original}`original`, that leading whitespace is saved only for the first token, and that no {name}`Syntax.node` has source information requires only a simple recursive function.

: Fidelity

  Fidelity should only be checked when parsing succeeds.
  To check source fidelity, use {name}`Syntax.reprint`, which uses source information to recover the string representation of syntax, failing when the syntax contains choice nodes with alternatives that reprint differently.
  {name}`Syntax.reprint` should succeed with a string that's equal to the region of the input that the parser consumed.
  {name}`Syntax.reprint` does not fail when the syntax contains non-original source information; it simply prints the token with a single leading and a single trailing space.
  Because parsers are entitled to assume that the prior token consumed all trailing whitespace, this test is only valid for inputs that do not begin with whitespace.

: Parse errors and {name Syntax.missing}`missing` syntax

  To check that {name}`Syntax.missing` occurs only in the presence of parser errors, use {name}`Syntax.hasMissing` and check whether {name}`Parser.ParserState.allErrors` returns an empty array.

: Fixed arities

  To check that each parser has a fixed stack arity, check the size of the parser state's syntax stack before and after each test run.
  To check that each syntax kind has a fixed node arity, use a recursive traversal that counts node arguments.
:::

:::example "Testing Low-Level Parsers"
```imports -show
import Lean
```
```lean -show
open Lean
```

The low-level parser {name}`crossedOut` requires that an identifier be surrounded by equal-length sequences of tilde characters (`'~'`):

```lean
open Lean.Parser Lean.Elab.Command

def tildesFn : ParserFn :=
  rawFn (takeWhile1Fn (· == '~') "tildes") (trailingWs := true)

def closeTildesFn (n : Nat) : ParserFn := fun c s =>
  let s := tildesFn c s
  if s.hasError || s.stxStack.back.getAtomVal.length == n then s
  else s.mkUnexpectedTokenError s!"{n} tildes"

def crossedOutFn : ParserFn :=
  nodeFn `crossedOut <| andthenFn tildesFn fun c s =>
    let n := s.stxStack.back.getAtomVal.length
    andthenFn ident.fn (closeTildesFn n) c s

def crossedOut : Parser :=
  { fn := crossedOutFn,
    info := { collectKinds := (·.insert `crossedOut) } }
```

It is not yet possible to make {name}`crossedOut` into a term parser because it lacks a formatter and parenthesizer.
```lean +error (name := noFormatter) -keep
attribute [term_parser] crossedOut
```
```leanOutput noFormatter
don't know how to generate formatter for non-definition `{ info := { collectKinds := fun x => x.insert `crossedOut },
  fn := crossedOutFn }`
```

Registering the formatter and parenthesizer allows the {attr}`term_parser` attribute to be applied.
```lean
open Lean.PrettyPrinter Formatter in
@[combinator_formatter crossedOut]
def crossedOut.formatter : Formatter :=
  node.formatter `crossedOut do
    visitAtom .anonymous
    Parser.ident.formatter
    visitAtom .anonymous

open Lean.PrettyPrinter Parenthesizer in
@[combinator_parenthesizer crossedOut]
def crossedOut.parenthesizer : Parenthesizer :=
  node.parenthesizer `crossedOut do
    visitToken
    Parser.ident.parenthesizer
    visitToken

attribute [term_parser] crossedOut
```

Because {name}`crossedOut` is not a {name}`ParserDescr`, the formatters must also be registered for the pretty printer:
```lean
attribute [formatter crossedOut] crossedOut.formatter
attribute [parenthesizer crossedOut] crossedOut.parenthesizer
```

A quick macro definition allows the parser to be used in real terms.
Because atom values are not checked directly by syntax matches, any number of tildes is accepted by a single rule.
```lean
macro_rules
  | `(~~~~ $x:ident ~~~~) => pure x
```

```lean (name := crossedOutCheck)
def five := 5

#check ~~ five ~~
```
```leanOutput crossedOutCheck
five : Nat
```

```lean (name := crossedOutCheck2)
#check ~~~~ five ~~~~
```
```leanOutput crossedOutCheck2
five : Nat
```

```lean +error (name := crossedOutMismatch)
#check ~~ five ~~~
```
```leanOutput crossedOutMismatch
unexpected token '~~~'; expected 2 tildes
```

```lean -show -keep
-- Verify that the registered formatter is used to display the syntax
/-- info: ~~~five~~~ -/
#check_msgs in
#eval show CommandElabM Unit from do
  let stx ← `(~~~ $(mkIdent `five) ~~~)
  logInfo (← liftCoreM (PrettyPrinter.ppTerm stx))
```

The first step in testing the parser is to run it against an input.
Because Lean parsers require an environment, the parser can be run in the command elaboration monad:
```lean
def runCrossedOut (input : String) : CommandElabM ParserState := do
  let env ← getEnv
  let ictx := mkInputContext input "<input>"
  let pmctx : ParserModuleContext := { env, options := {} }
  let s : ParserState := { cache := initCacheForInput input, pos := 0 }
  return crossedOut.fn.run ictx pmctx (getTokenTable env) s
```

The tests themselves run in a monad with state and exceptions.
The state tracks the arity of each syntax kind in order to ensure that they are constant, while exceptions are thrown on invariant violations.
```lean
abbrev CheckM := StateT (NameMap Nat) (Except String)
```

The first invariant to check is that tokens have original source information with no leading whitespace, that the trailing whitespace is actually adjacent to the token, and that the token's text is actually at the indicated position in the input:
```lean
def checkToken (input : String) (info : SourceInfo) (text : String) :
    Except String Unit := do
  let .original leading pos trailing endPos := info
    | throw s!"token {text} lacks original source info"
  unless leading.toString.isEmpty do
    throw s!"token {text} has leading whitespace"
  let actual : Substring.Raw :=
    { str := input, startPos := pos, stopPos := endPos }
  unless actual.toString == text do
    throw s!"token {text} not at its position"
  unless trailing.startPos == endPos do
    throw s!"trailing whitespace of {text} not adjacent"
```

The next set of invariants to check is that nodes have no source information, and that each node kind has a constant arity.
This check invokes the token checks while traversing the syntax.
```lean
partial def checkTree (input : String) : Syntax → CheckM Unit
  | .node info k args => do
    unless info matches .none do
      throw s!"node {k} has source info"
    let variableArity :=
      [nullKind, groupKind, choiceKind, interpolatedStrKind]
    unless variableArity.contains k do
      match (← get).find? k with
      | some n =>
        unless n == args.size do
          throw s!"kind {k} has arities {n} and {args.size}"
      | none => modify (·.insert k args.size)
    args.forM (checkTree input)
  | .atom info val => checkToken input info val
  | .ident info raw _ _ => checkToken input info raw.toString
  | .missing => pure ()
```

The rest of the invariants can be checked without recursive traversals.
Because this parser is intended to be used in the middle of a Lean file, rather than as the first token of a module, the test ensures that the input does not begin with whitespace.
Any whitespace should have been consumed by the preceding token's parser.
```lean
def checkInvariants (input : String) : CommandElabM Unit := do
  if input.startsWith Char.isWhitespace then
    throwError "Can't test parser when input begins with whitespace"

  let s ← runCrossedOut input

  unless s.allErrors.isEmpty do
    logInfo "Parse error - not checking further"
    return

  unless s.stackSize == 1 do
    throwError m!"Unexpected stack arity {s.stackSize}"

  let stx := s.stxStack.back

  if stx.hasMissing then
    throwError "Found missing syntax without error"

  unless stx.reprint == some input do
    throwError "does not reprint to the input"

  match (checkTree input stx).run' {} with
  | .error e => throwError e
  | .ok () => logInfo "Passed"
```

```lean (name := checkOk)
#eval checkInvariants "~~~ x  ~~~ -- done\n"
```
```leanOutput checkOk
Passed
```

```lean (name := checkErr)
#eval checkInvariants "~~ x ~~~"
```
```leanOutput checkErr
Parse error - not checking further
```
:::
