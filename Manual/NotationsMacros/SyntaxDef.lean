/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
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

#doc (Manual) "Defining New Syntax" =>
%%%
tag := "syntax-ext"
%%%

Lean's uniform representation of syntax is very general and flexible.
This means that extensions to Lean's parser do not require extensions to the representation of parsed syntax.

# Syntax Model
%%%
tag := "syntax-data"
%%%

Lean's parser produces a concrete syntax tree, of type {name}`Lean.Syntax`.
{name}`Lean.Syntax` is an inductive type that represents all of Lean's syntax, including commands, terms, tactics, and any custom extensions.
All of these are represented by a few basic building blocks:

: {deftech}[Atoms]

  Atoms are the fundamental terminals of the grammar, including literals (such as those for characters and numbers), parentheses, operators, and keywords.

: {deftech}[Identifiers]

  :::keepEnv
  ```lean (show := false)
  variable {α : Type u}
  variable {x : α}
  ```
  Identifiers represent names, such as {lean}`x`, {lean}`Nat`, or {lean}`Nat.add`.
  Identifier syntax includes a list of pre-resolved names that the identifier might refer to.
  :::

: {deftech}[Nodes]

  Nodes represent the parsing of nonterminals.
  Nodes contain a {deftech}_syntax kind_, which identifies the syntax rule that the node results from, along with an array of child {name Lean.Syntax}`Syntax` values.

: Missing Syntax

  When the parser encounters an error, it returns a partial result, so Lean can provide some feedback about partially-written programs or programs that contain mistakes.
  Partial results contain one or more instances of missing syntax.

Atoms and identifiers are collectively referred to as {deftech}_tokens_.

{docstring Lean.Syntax}

{docstring Lean.Syntax.Preresolved}

# Syntax Node Kinds

Syntax node kinds typically identify the parser that produced the node.
This is one place where the names given to operators or notations (or their automatically-generated internal names) occur.
While only nodes contain a field that identifies their kind, identifiers have the kind {name Lean.identKind}`identKind` by convention, while atoms have their internal string as their kind by convention.
Lean's parser wraps each keyword atom `KW` in a singleton node whose kind is `` `token.KW ``.
The kind of a syntax value can be extracted using {name Lean.Syntax.getKind}`Syntax.getKind`.

{docstring Lean.SyntaxNodeKind}

{docstring Lean.Syntax.isOfKind}

{docstring Lean.Syntax.getKind}

{docstring Lean.Syntax.setKind}

# Token and Literal Kinds

A number of named kinds are associated with the basic tokens produced by the parser.
Typically, single-token syntax productions consist of a {name Lean.Syntax.node}`node` that contains a single {name Lean.Syntax.atom}`atom`; the kind saved in the node allows the value to be recognized.
Atoms for literals are not interpreted by the parser: string atoms include their leading and trailing double-quote characters along with any escape sequences contained within, and hexadecimal numerals are saved as a string that begins with {lean}`"0x"`.
{ref "typed-syntax-helpers"}[Helpers] such as {name}`Lean.TSyntax.getString` are provided to perform this decoding on demand.

```lean (show := false) (keep := false)
-- Verify claims about atoms and nodes
open Lean in
partial def noInfo : Syntax → Syntax
  | .node _ k children => .node .none k (children.map noInfo)
  | .ident _ s x pre => .ident .none s x pre
  | .atom _ s => .atom .none s
  | .missing => .missing
/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "0xabc123"]
-/
#check_msgs in
#eval noInfo <$> `(term|0xabc123)

/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"ab\\tc\""]
-/
#check_msgs in
#eval noInfo <$> `(term|"ab\tc")
```

{docstring Lean.identKind}

{docstring Lean.strLitKind}

{docstring Lean.interpolatedStrKind}

{docstring Lean.interpolatedStrLitKind}

{docstring Lean.charLitKind}

{docstring Lean.numLitKind}

{docstring Lean.scientificLitKind}

{docstring Lean.nameLitKind}

{docstring Lean.fieldIdxKind}

# Internal Kinds

{docstring Lean.groupKind}

{docstring Lean.nullKind}

{docstring Lean.choiceKind}

{docstring Lean.hygieneInfoKind}

# Source Positions
%%%
tag := "source-info"
%%%

Atoms, identifiers, and nodes optionally contain {deftech}[source information] that tracks their correspondence with the original file.
The parser saves source information for all tokens, but not for nodes; position information for parsed nodes is reconstructed from their first and last tokens.
Not all {name Lean.Syntax}`Syntax` data results from the parser: it may be the result of {tech}[macro expansion], in which case it typically contains a mix of generated and parsed syntax, or it may be the result of {tech key:="delaborator"}[delaborating] an internal term to display it to a user.
In these use cases, nodes may themselves contain source information.

Source information comes in two varieties:

: {deftech}[Original]

  Original source information comes from the parser.
  In addition to the original source location, it also contains leading and trailing whitespace that was skipped by the parser, which allows the original string to be reconstructed.
  This whitespace is saved as offsets into the string representation of the original source code (that is, as {name}`Substring`) to avoid having to allocate copies of substrings.

: {deftech}[Synthetic]

  Synthetic source information comes from metaprograms (including macros) or from Lean's internals.
  Because there is no original string to be reconstructed, it does not save leading and trailing whitespace.
  Synthetic source positions are used to provide accurate feedback even when terms have been automatically transformed, as well as to track the correspondence between elaborated expressions and their presentation in Lean's output.
  A synthetic position may be marked {deftech}_canonical_, in which case some operations that would ordinarily ignore synthetic positions will treat it as if it were not.

{docstring Lean.SourceInfo}

# Inspecting Syntax

```lean (show := false)
section Inspecting
open Lean
```

There are three primary ways to inspect {lean}`Syntax` values:

 : The {lean}`Repr` Instance

  The {lean}`Repr Syntax` instance produces a very detailed representation of syntax in terms of the constructors of the {lean}`Syntax` type.

 : The {lean}`ToString` Instance

  The {lean}`ToString Syntax` instance produces a compact view, representing certain syntax kinds with particular conventions that can make it easier to read at a glance.
  This instance suppresses source position information.

 : The Pretty Printer

  Lean's pretty printer attempts to render the syntax as it would look in a source file, but fails if the nesting structure of the syntax doesn't match the expected shape.

::::keepEnv
:::example "Representing Syntax as Constructors"
The {name}`Repr` instance's representation of syntax can be inspected by quoting it in the context of {keywordOf Lean.Parser.Command.eval}`#eval`, which can run actions in the command elaboration monad {name Lean.Elab.Command.CommandElabM}`CommandElabM`.
To reduce the size of the example output, the helper {lean}`removeSourceInfo` is used to remove source information prior to display.
```lean
partial def removeSourceInfo : Syntax → Syntax
  | .atom _ str => .atom .none str
  | .ident _ str x pre => .ident .none str x pre
  | .node _ k children => .node .none k (children.map removeSourceInfo)
  | .missing => .missing
```

```lean (name := reprStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (repr (removeSourceInfo stx.raw))
```
```leanOutput reprStx1
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `«term_+_»
  #[Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "2"],
    Lean.Syntax.atom (Lean.SourceInfo.none) "+", Lean.Syntax.missing]
```

In the second example, {tech}[macro scopes] inserted by quotation are visible on the call to {name}`List.length`.
```lean (name := reprStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (repr (removeSourceInfo stx.raw))
```
The contents of the {tech}[pre-resolved identifier] {name}`List.length` are visible here:
```leanOutput reprStx2
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Term.app
  #[Lean.Syntax.ident
      (Lean.SourceInfo.none)
      "List.length".toSubstring
      (Lean.Name.mkNum `List.length._@.Manual.NotationsMacros.SyntaxDef._hyg 2)
      [Lean.Syntax.Preresolved.decl `List.length [], Lean.Syntax.Preresolved.namespace `List.length],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `null
      #[Lean.Syntax.node
          (Lean.SourceInfo.none)
          `«term[_]»
          #[Lean.Syntax.atom (Lean.SourceInfo.none) "[",
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Rose\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Daffodil\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Lily\""]],
            Lean.Syntax.atom (Lean.SourceInfo.none) "]"]]]
```
:::
::::

The {name}`ToString` instance represents the constructors of {name}`Syntax` as follows:

 * The {name Syntax.ident}`ident` constructor is represented as the underlying name. Source information and pre-resolved names are not shown.
 * The {name Syntax.atom}`atom` constructor is represented as a string.
 * The {name Syntax.missing}`missing` constructor is represented by `<missing>`.
 * The representation of the {name Syntax.node}`node` constructor depends on the kind.
   If the kind is {lean}`` `null ``, then the node is represented by its child nodes order in square brackets.
   Otherwise, the node is represented by its kind followed by its child nodes, both surrounded by parentheses.

:::example "Syntax as Strings"
The string representation of syntax can be inspected by quoting it in the context of {keywordOf Lean.Parser.Command.eval}`#eval`, which can run actions in the command elaboration monad {name Lean.Elab.Command.CommandElabM}`CommandElabM`.

```lean (name := toStringStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (toString stx)
```
```leanOutput toStringStx1
(«term_+_» (num "2") "+" <missing>)
```

In the second example, {tech}[macro scopes] inserted by quotation are visible on the call to {name}`List.length`.
```lean (name := toStringStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (toString stx)
```
```leanOutput toStringStx2
(Term.app
 `List.length._@.Manual.NotationsMacros.SyntaxDef._hyg.2
 [(«term[_]» "[" [(str "\"Rose\"") "," (str "\"Daffodil\"") "," (str "\"Lily\"")] "]")])
```
:::

Pretty printing syntax is typically most useful when including it in a message to a user.
Normally, Lean automatically invokes the pretty printer when necessary.
However, {name}`ppTerm` can be explicitly invoked if needed.

::::keepEnv
:::example "Pretty-Printed Syntax"
```lean (show := false)
open Lean Elab Command
```

The string representation of syntax can be inspected by quoting it in the context of {keywordOf Lean.Parser.Command.eval}`#eval`, which can run actions in the command elaboration monad {name Lean.Elab.Command.CommandElabM}`CommandElabM`.
Because new syntax declarations also equip the pretty printer with instructions for displaying them, the pretty printer requires a configuration object.
This context can be constructed with a helper:
```lean
def getPPContext : CommandElabM PPContext := do
  return {
    env := (← getEnv),
    opts := (← getOptions),
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
```

```lean (name := ppStx1)
#eval show CommandElabM Unit from do
  let stx ← `(2 + 5)
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx1
2 + 5
```

In the second example, the {tech}[macro scopes] inserted on {name}`List.length` by quotation cause it to be displayed with a dagger (`✝`).
```lean (name := ppStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx2
List.length✝ ["Rose", "Daffodil", "Lily"]
```

Pretty printing wraps lines and inserts indentation automatically.
A {tech}[coercion] typically converts the pretty printer's output to the type expected by {name}`logInfo`, using a default layout width.
The width can be controlled by explicitly calling {name Std.Format.pretty}`pretty` with a named argument.
```lean (name := ppStx3)
#eval do
  let flowers := #["Rose", "Daffodil", "Lily"]
  let manyFlowers := flowers ++ flowers ++ flowers
  let stx ← `(List.length [$(manyFlowers.map (quote (k := `term))),*])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo (fmt.pretty (width := 40))
```
```leanOutput ppStx3
List.length✝
  ["Rose", "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily"]
```
:::


::::

```lean (show := false)
end Inspecting
```

# Typed Syntax
%%%
tag := "typed-syntax"
%%%

Syntax may additionally be annotated with a type that specifies which {tech}[syntax category] it belongs to.
{TODO}[Describe the problem here - complicated invisible internal invariants leading to weird error msgs]
The {name Lean.TSyntax}`TSyntax` structure contains a type-level list of syntax categories along with a syntax tree.
The list of syntax categories typically contains precisely one element, in which case the list structure itself is not shown.

{docstring Lean.TSyntax}

{docstring Lean.SyntaxNodeKinds}

{tech}[Quasiquotations] prevent the substitution of typed syntax that does not come from the correct syntactic category.
For many of Lean's built-in syntactic categories, there is a set of {tech}[coercions] that appropriately wrap one kind of syntax for another category, such as a coercion from the syntax of string literals to the syntax of terms.
Additionally, many helper functions that are only valid on some syntactic categories are defined for the appropriate typed syntax only.

```lean (show := false)
/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
open Lean in
#synth CoeHTCT (TSyntax `str) (TSyntax `term)
```

The constructor of {name Lean.TSyntax}`TSyntax` is public, and nothing prevents users from constructing values that break internal invariants.
The use of {name Lean.TSyntax}`TSyntax` should be seen as a way to reduce common mistakes, rather than rule them out entirely.


In addition to {name Lean.TSyntax}`TSyntax`, there are types that represent arrays of syntax, with or without separators.
These correspond to {TODO}[xref] repeated elements in syntax declarations or antiquotations.

{docstring Lean.TSyntaxArray}

{docstring Lean.Syntax.TSepArray}

# Aliases

A number of aliases are provided for commonly-used typed syntax varieties.
These aliases allow code to be written at a higher level of abstraction.

{docstring Lean.Term}

{docstring Lean.Command}

{docstring Lean.Syntax.Level}

{docstring Lean.Syntax.Tactic}

{docstring Lean.Prec}

{docstring Lean.Prio}

{docstring Lean.Ident}

{docstring Lean.StrLit}

{docstring Lean.CharLit}

{docstring Lean.NameLit}

{docstring Lean.NumLit}

{docstring Lean.ScientificLit}

{docstring Lean.HygieneInfo}

# Helpers for Typed Syntax
%%%
tag := "typed-syntax-helpers"
%%%

For literals, Lean's parser produces a singleton node that contains an {name Lean.Syntax.atom}`atom`.
The inner atom contains a string with source information, while the node's kind specifies how the atom is to be interpreted.
This may involve decoding string escape sequences or interpreting base-16 numeric literals.
The helpers in this section perform the correct interpretation.

{docstring Lean.TSyntax.getId}

{docstring Lean.TSyntax.getName}

{docstring Lean.TSyntax.getNat}

{docstring Lean.TSyntax.getScientific}

{docstring Lean.TSyntax.getString}

{docstring Lean.TSyntax.getChar}

{docstring Lean.TSyntax.getHygieneInfo}

# Syntax Categories
%%%
tag := "syntax-categories"
%%%

Lean's parser contains a table of {deftech}_syntax categories_, which correspond to nonterminals in a context-free grammar.
Some of the most important categories are terms, commands, universe levels, priorities, precedences, and the categories that represent tokens such as literals.
Typically, each {tech}[syntax kind] corresponds to a category.
New categories can be declared using {keywordOf Lean.Parser.Command.syntaxCat}`declare_syntax_cat`.

:::syntax command (title := "Declaring Syntactic Categories")
Declares a new syntactic category.

```grammar
$[$_:docComment]?
declare_syntax_cat $_ $[(behavior := $_)]?
```
:::

The leading identifier behavior is an advanced feature that usually does not need to be modified.
It controls the behavior of the parser when it encounters an identifier, and can sometimes cause the identifier to be treated as a non-reserved keyword instead.
This is used to avoid turning the name of every {ref "tactics"}[tactic] into a reserved keyword.

{docstring Lean.Parser.LeadingIdentBehavior}

# Syntax Rules
%%%
tag := "syntax-rules"
%%%

Each {tech}[syntax category] is associated with a set of {deftech}_syntax rules_, which correspond to productions in a context-free grammar.
Syntax rules can be defined using the {keywordOf Lean.Parser.Command.syntax}`syntax` command.

:::syntax command (title := "Syntax Rules")
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind
syntax$[:$p]? $[(name := $x)]? $[(priority := $p)]? $_* : $c
```
:::

As with operator and notation declarations, the contents of the documentation comments are shown to users while they interact with the new syntax.
Attributes may be added to invoke compile-time metaprograms on the resulting definition.

Syntax rules interact with {tech}[section scopes] in the same manner as attributes, operators, and notations.
By default, syntax rules are available to the parser in any module that transitively imports the one in which they are established, but they may be declared `scoped` or `local` to restrict their availability either to contexts in which the current namespace has been opened or to the current {tech}[section scope], respectively.

When multiple syntax rules for a category can match the current input, the {tech}[local longest-match rule] is used to select one of them.
Like notations and operators, if there is a tie for the longest match then the declared priorities are used to determine which parse result applies.
If this still does not resolve the ambiguity, then all the results that tied are saved.
The elaborator is expected to attempt all of them, succeeding when exactly one can be elaborated.

The syntax rule's precedence, written immediately after the {keywordOf Lean.Parser.Command.syntax}`syntax` keyword, restricts the parser to use this new syntax only when the precedence context is at least the provided value.
{TODO}[Default precedence]
Just as with operators and notations, syntax rules may be manually provided with a name; if they are not, an otherwise-unused name is generated.
Whether provided or generated, this name is used as the syntax kind in the resulting {name Lean.Syntax.node}`node`.

The body of a syntax declaration is even more flexible than that of a notation.
String literals specify atoms to match.
Subterms may be drawn from any syntax category, rather than just terms, and they may be optional or repeated, with or without interleaved comma separators.
Identifiers in syntax rules indicate syntax categories, rather than naming subterms as they do in notations.


Finally, the syntax rule specifies which syntax category it extends.
It is an error to declare a syntax rule in a nonexistent category.

```lean (show := false)
-- verify preceding para
/-- error: unknown category 'nuhUh' -/
#check_msgs in
syntax "blah" : nuhUh
```


:::syntax stx (open := false) (title := "Syntax Specifiers")
The syntactic category `stx` is the grammar of specifiers that may occur in the body of a {keywordOf Lean.Parser.Command.syntax}`syntax` command.

String literals are parsed as {tech}[atoms] (including both keywords such as `if`, `#eval`, or `where`):
```grammar
$s:str
```
Leading and trailing spaces in the strings do not affect parsing, but they cause Lean to insert spaces in the corresponding position when displaying the syntax in {tech}[proof states] and error messages.
Ordinarily, valid identifiers occurring as atoms in syntax rules become reserved keywords.
Preceding a string literal with an ampersand (`&`) suppresses this behavior:
```grammar
&$s:str
```

Identifiers specify the syntactic category expected in a given position, and may optionally provide a precedence:{TODO}[Default prec here?]
```grammar
$x:ident$[:$p]?
```

The `*` modifier is the Kleene star, matching zero or more repetitions of the preceding syntax.
It can also be written using `many`.
```grammar
$s:stx *
```
The `+` modifier matches one or more repetitions of the preceding syntax.
It can also be written using `many1`.
```grammar
$s:stx +
```
The `?` modifier makes a subterm optional, and matches zero or one, but not more, repetitions of the preceding syntax.
It can also be written as `optional`.
```grammar
$s:stx ?
```
```grammar
optional($s:stx)
```

The `,*` modifier matches zero or more repetitions of the preceding syntax with interleaved commas.
It can also be written using `sepBy`.
```grammar
$_:stx ,*
```

The `,+` modifier matches one or more repetitions of the preceding syntax with interleaved commas.
It can also be written using `sepBy1`.
```grammar
$_:stx ,+
```

The `,*,?` modifier matches zero or more repetitions of the preceding syntax with interleaved commas, allowing an optional trailing comma after the final repetition.
It can also be written using `sepBy` with the `allowTrailingSep` modifier.
```grammar
$_:stx ,*,?
```

The `,+,?` modifier matches one or more repetitions of the preceding syntax with interleaved commas, allowing an optional trailing comma after the final repetition.
It can also be written using `sepBy1` with the `allowTrailingSep` modifier.
```grammar
$_:stx ,+,?
```

The `<|>` operator, which can be written `orelse`, matches either syntax.
However, if the first branch consumes any tokens, then it is committed to, and failures will not be backtracked:
```grammar
$_:stx <|> $_:stx
```
```grammar
orelse($_:stx, $_:stx)
```

The `!` operator matches the complement of its argument.
If its argument fails, then it succeeds, resetting the parsing state.
```grammar
! $_:stx
```

Syntax specifiers may be grouped using parentheses.
```grammar
($_:stx)
```

Repetitions may be defined using `many` and `many1`.
The latter requires at least one instance of the repeated syntax.
```grammar
many($_:stx)
```
```grammar
many1($_:stx)
```

Repetitions with separators may be defined using `sepBy` and `sepBy1`, which respectively match zero or more occurrences and one or more occurrences, separated by some other syntax.
They come in three varieties:
 * The two-parameter version uses the atom provided in the string literal to parse the separators, and does not allow trailing separators.
 * The three-parameter version uses the third parameter to parse the separators, using the atom for pretty-printing.
 * The four-parameter version optionally allows the separator to occur an extra time at the end of the sequence.
    The fourth argument must always literally be the keyword `allowTrailingSep`.

```grammar
sepBy($_:stx, $_:str)
```
```grammar
sepBy($_:stx, $_:str, $_:stx)
```
```grammar
sepBy($_:stx, $_:str, $_:stx, allowTrailingSep)
```
```grammar
sepBy1($_:stx, $_:str)
```
```grammar
sepBy1($_:stx, $_:str, $_:stx)
```
```grammar
sepBy1($_:stx, $_:str, $_:stx, allowTrailingSep)
```
:::

::::keepEnv
:::example "Parsing Matched Parentheses and Brackets"

A language that consists of matched parentheses and brackets can be defined using syntax rules.
The first step is to declare a new {tech}[syntax category]:
```lean
declare_syntax_cat balanced
```
Next, rules can be added for parentheses and square brackets.
To rule out empty strings, the base cases consist of empty pairs.
```lean
syntax "(" ")" : balanced
syntax "[" "]" : balanced
syntax "(" balanced ")" : balanced
syntax "[" balanced "]" : balanced
syntax balanced balanced : balanced
```

In order to invoke Lean's parser on these rules, there must also be an embedding from the new syntax category into one that may already be parsed:
```lean
syntax (name := termBalanced) "balanced " balanced : term
```

These terms cannot be elaborated, but reaching an elaboration error indicates that parsing succeeded:
```lean
/--
error: elaboration function for 'termBalanced' has not been implemented
  balanced ()
-/
#guard_msgs in
example := balanced ()

/--
error: elaboration function for 'termBalanced' has not been implemented
  balanced []
-/
#guard_msgs in
example := balanced []

/--
error: elaboration function for 'termBalanced' has not been implemented
  balanced [[]()([])]
-/
#guard_msgs in
example := balanced [[] () ([])]
```

Similarly, parsing fails when they are mismatched:
```syntaxError mismatch
example := balanced [() (]]
```
```leanOutput mismatch
<example>:1:25-1:26: unexpected token ']'; expected ')' or balanced
```
:::
::::

::::keepEnv
:::example "Parsing Comma-Separated Repetitions"
A variant of list literals that requires double square brackets and allows a trailing comma can be added with the following syntax:
```lean
syntax "[[" term,*,? "]]" : term
```

Adding a {deftech}[macro] that describes how to translate it into an ordinary list literal allows it to be used in tests.
```lean
macro_rules
  | `(term|[[$e:term,*]]) => `([$e,*])
```

```lean (name := evFunnyList)
#eval [["Dandelion", "Thistle",]]
```
```leanOutput evFunnyList
["Dandelion", "Thistle"]
```

:::
::::

# Indentation
%%%
tag := "syntax-indentation"
%%%

Internally, the parser maintains a saved source position.
Syntax rules may include instructions that interact with these saved positions, causing parsing to fail when a condition is not met.
Indentation-sensitive constructs, such as {keywordOf Lean.Parser.Term.do}`do`, save a source position, parse their constituent parts while taking this saved position into account, and then restore the original position.

In particular, Indentation-sensitvity is specified by combining {name Lean.Parser.withPosition}`withPosition` or {name Lean.Parser.withPositionAfterLinebreak}`withPositionAfterLinebreak`, which save the source position at the start of parsing some other syntax, with {name Lean.Parser.checkColGt}`colGt`, {name Lean.Parser.checkColGe}`colGe`, and {name Lean.Parser.checkColEq}`colEq`, which compare the current column with the column from the most recently-saved position.
{name Lean.Parser.checkLineEq}`lineEq` can also be used to ensure that two positions are on the same line in the source file.

:::parserAlias withPosition
:::

:::parserAlias withoutPosition
:::

:::parserAlias withPositionAfterLinebreak
:::

:::parserAlias colGt
:::

:::parserAlias colGe
:::

:::parserAlias colEq
:::

:::parserAlias lineEq
:::


::::keepEnv
:::example "Aligned Columns"
This syntax for saving notes takes a bulleted list of items, each of which must be aligned at the same column.
```lean
syntax "note " ppLine withPosition((colEq "◦ " str ppLine)+) : term
```

There is no elaborator or macro associated with this syntax, but the following example is accepted by the parser:
```lean (error := true) (name := noteEx1)
#check
  note
    ◦ "One"
    ◦ "Two"
```
```leanOutput noteEx1
elaboration function for '«termNote__◦__»' has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```

The syntax does not require that the list is indented with respect to the opening token, which would require an extra `withPosition` and a `colGt`.
```lean (error := true) (name := noteEx15)
#check
  note
◦ "One"
◦ "Two"
```
```leanOutput noteEx15
elaboration function for '«termNote__◦__»' has not been implemented
  note
    ◦ "One"
    ◦ "Two"
```


The following examples are not syntactically valid because the columns of the bullet points do not match.
```syntaxError noteEx2
#check
  note
    ◦ "One"
   ◦ "Two"
```
```leanOutput noteEx2
<example>:4:3-4:4: expected end of input
```

```syntaxError noteEx2
#check
  note
   ◦ "One"
     ◦ "Two"
```
```leanOutput noteEx2
<example>:4:5-4:6: expected end of input
```
:::
::::
