/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Manual.NotationsMacros.Operators
import Manual.NotationsMacros.Precedence
import Manual.NotationsMacros.Notations

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Notations and Macros" =>
%%%
tag := "language-extension"
%%%

Different mathematical fields have their own notational conventions, and many notations are re-used with differing meanings in different fields.
It is important that formal developments are able to use established notations: formalized mathematics is already difficult, and the mental overhead of translating between syntaxes can be substantial.
At the same time, it's important to be able to control the scope of notational extensions.
Many fields use related notations with very different meanings, and it should be possible to combine developments from these separate fields in a way where both readers and the system know which convention is in force in any given region of a file.

Lean addresses the problem of notational extensibility with a variety of mechanisms, each of which solves different aspects of the problem.
They can be combined flexibly to achieve the necessary results:

 * The {ref "parser"}_extensible parser_ {index}[parser] allows a great variety of notational conventions to be implemented declaratively, and combined flexibly.
 * {ref "macro-and-elab"}[Macros] allow new syntax to be easily mapped to existing syntax, which is a simple way to provide meaning to new constructs.
  Due to {tech}[hygiene] and automatic propagation of source positions, this process doesn't interfere with Lean's interactive features.
 * {ref "macro-and-elab"}[Elaborators] provide new syntax with the same tools available to Lean's own syntax in cases where a macro is insufficiently expressive.
 * {ref "notations"}[Notations] allow the simultaneous definition of a parser extension, a macro, and a pretty printer.{TODO}[check the details on pretty printers and syntax vs notation]
 * Low-level parser extensions allow the parser to be extended in ways that modify its rules for tokens and whitespace, or that even completely replace Lean's syntax. This is an advanced topic that requires familiarity with Lean internals; nevertheless, the possibility of doing this without modifying the compiler is important. This reference manual is written using a language extension that replaces Lean's concrete syntax with a Markdown-like language for writing documents, but the source files are still Lean files.

{include 0 Manual.NotationsMacros.Operators}

{include 0 Manual.NotationsMacros.Precedence}

{include 0 Manual.NotationsMacros.Notations}


# Defining New Syntax

Lean's uniform representation of syntax is very general and flexible.
This means that extensions to Lean's parser do not require extensions to the representation of parsed syntax.

## Syntax Model

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

### Syntax Node Kinds

Syntax node kinds typically identify the parser that produced the node.
This is one place where the names given to operators or notations (or their automatically-generated internal names) occur.
While only nodes contain a field that identifies their kind, identifiers have the kind {name Lean.identKind}`identKind` by convention, while atoms have their internal string as their kind by convention.
The kind of a syntax value can be extracted using {name Lean.Syntax.getKind}`Syntax.getKind`.

{docstring Lean.SyntaxNodeKind}

{docstring Lean.Syntax.isOfKind}

{docstring Lean.Syntax.getKind}

{docstring Lean.Syntax.setKind}

#### Token and Literal Kinds

A number of named kinds are associated with the basic tokens produced by the parser.
Typically, single-token syntax productions consist of a {name Lean.Syntax.node}`node` that contains a single {name Lean.Syntax.atom}`atom`; the kind saved in the node allows the value to be recognized.
Atoms for literals are not interpreted by the parser: string atoms include their leading and trailing double-quote characters along with any escape sequences contained within, and hexadecimal numerals are saved as a string that begins with {lean}`"0x"`.
Helpers such as {name}`Lean.TSyntax.getString` are provided to perform this decoding on demand.

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
#guard_msgs in
#eval noInfo <$> `(term|0xabc123)

/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"ab\\tc\""]
-/
#guard_msgs in
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

#### Internal Kinds

{docstring Lean.groupKind}

{docstring Lean.nullKind}

{docstring Lean.choiceKind}

{docstring Lean.hygieneInfoKind}

### Source Positions
%%%
tag := "source-info"
%%%

Atoms, identifiers, and nodes optionally contain {deftech}[source information] that tracks their correspondence with the original file.
The parser saves source information for all tokens, but not for nodes; position information for parsed nodes is reconstructed from their first and last tokens.
Not all {name Lean.Syntax}`Syntax` data results from the parser: it may be the result of {tech}[macro expansion], in which case it typically contains a mix of generated and parsed syntax, or it may be the result of {tech key:="delaborate"}[delaborating] an internal term to display it to a user.
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

### Typed Syntax

Syntax may additionally be annotated with a type that specifies which {tech}[syntax category] it belongs to.
{TODO}[Describe the problem here - complicated invisible internal invariants leading to weird error msgs]
The {name Lean.TSyntax}`TSyntax` structure contains a type-level list of syntax categories along with a syntax tree.
The list of syntax categories typically contains precisely one element, in which case the list structure itself is not shown.

{docstring Lean.TSyntax}

{tech}[Quasiquotations] prevent the substitution of typed syntax that does not come from the correct syntactic category.
For many of Lean's built-in syntactic categories, there is a set of {tech}[coercions] that appropriately wrap one kind of syntax for another category, such as a coercion from the syntax of string literals to the syntax of terms.
Additionally, many helper functions that are only valid on some syntactic categories are defined for the appropriate typed syntax only.

```lean (show := false)
/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
open Lean in
#synth CoeHTCT (TSyntax `str) (TSyntax `term)
```

The constructor of {name Lean.TSyntax}`TSyntax` is public, and nothing prevents users from constructing values that break internal invariants.
The use of {name Lean.TSyntax}`TSyntax` should be seen as a way to reduce common mistakes, rather than rule them out entirely.

#### Aliases

A number of aliases are provided for commonly-used typed syntax varieties.
These aliases allow code to be written at a higher level of abstraction.

{docstring Lean.Term}

{docstring Lean.Command}

{docstring Lean.Level}

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

#### Helpers for Typed Syntax

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

## Syntax Categories
%%%
tag := "syntax-categories"
%%%

Lean's parser contains a table of {deftech}_syntax categories_, which correspond to nonterminals in a context-free grammar.
Some of the most important categories are terms, commands, universe levels, priorities, precedences, and the categories that represent tokens such as literals.
Typically, each {tech}[syntax kind] corresponds to a category.
New categories can be declared using {keywordOf Lean.Parser.Command.syntaxCat}`declare_syntax_cat`.

:::syntax command
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

## Syntax Rules

Each {tech}[syntax category] is associated with a set of {deftech}_syntax rules_, which correspond to productions in a context-free grammar.
Syntax rules can be defined using the {keywordOf Lean.Parser.Command.syntax}`syntax` command.

:::syntax command
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
#guard_msgs in
syntax "blah" : nuhUh
```


:::syntax stx (open := false)
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

The `*` modifier is the Kleene star, matching zero or more repetitions of the preceding syntax:
```grammar
$s:stx *
```
The `+` modifier matches one or more repetitions of the preceding syntax:
```grammar
$s:stx +
```
The `?` modifier makes a subterm optional, and matches zero or one, but not more, repetitions of the preceding syntax:
```grammar
$s:stx ?
```

The `,*` modifier matches zero or more repetitions of the preceding syntax with interleaved commas:
```grammar
$_:stx ,*
```

The `,+` modifier matches one or more repetitions of the preceding syntax with interleaved commas:
```grammar
$_:stx ,+
```

The `,*,?` modifier matches zero or more repetitions of the preceding syntax with interleaved commas, allowing an optional trailing comma after the final repetition:
```grammar
$_:stx ,*,?
```

The `,+,?` modifier matches one or more repetitions of the preceding syntax with interleaved commas, allowing an optional trailing comma after the final repetition:
```grammar
$_:stx ,+,?
```

The `<|>` operator matches either syntax.
However, if the first branch consumes any tokens, then it is committed to, and failures will not be backtracked:
```grammar
$_:stx <|> $_:stx
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
:::

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
<example>:1:25: expected ')' or balanced
```
:::


# Macros
%%%
tag := "macros"
%%%

:::planned 71
 * `macro_rules`
   * Syntax patterns
   * Backtracking on expansion failure
 * {deftech}[Hygiene] and {deftech}[quasiquotation]
 * The `macro` command
:::

{deftech}_Macros_ are transformations from {name Lean.Syntax}`Syntax` to {name Lean.Syntax}`Syntax` that occur during {tech key:="elaborator"}[elaboration] and during {ref "tactic-macros"}[tactic execution].
Replacing syntax with the result of transforming it with a macro is called {deftech}_macro expansion_.
Multiple macros may be associated with a single {tech}[syntax kind], and they are attempted in order of definition.
Macros are run in a {tech}[monad] that has access to some compile-time metadata and has the ability to either emit an error message or to delegate to subsequent macros, but the macro monad is much less powerful than the elaboration monads.

```lean (show := false)
section
open Lean (Syntax MacroM)
```

Macros are associated with {tech}[syntax kinds].
An internal table maps syntax kinds to macros of type {lean}`Syntax → MacroM Syntax`.
Macros delegate to the next entry in the table by throwing the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception.
A given {name}`Syntax` value _is a macro_ when there is a macro associated with its syntax kind that does not throw {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax`.
If a macro throws any other exception, an error is reported to the user.
{tech}[Syntax categories] are irrelevant to macro expansion; however, because each syntax kind is typically associated with a single syntax category, they do not interfere in practice.

::::keepEnv
:::example "Macro Error Reporting"
The following macro reports an error when its parameter is the literal numeral five.
It expands to its argument in all other cases.
```lean
syntax &"notFive" term:arg : term
open Lean in
macro_rules
  | `(term|notFive 5) => Macro.throwError "'5' is not allowed here"
  | `(term|notFive $e) => pure e
```

When applied to terms that are not syntactically the numeral five, elaboration succeeds:
```lean (name := notFiveAdd)
#eval notFive (2 + 3)
```
```leanOutput notFiveAdd
5
```

When the error case is triggered, the user receives an error message:
```lean (name := notFiveFive) (error := true)
#eval notFive 5
```
```leanOutput notFiveFive
'5' is not allowed here
```
:::
::::

Before elaborating a piece of syntax, the elaborator checks whether its {tech}[syntax kind] has macros associated with it.
These are attempted in order.
If a macro succeeds, potentially returning syntax with a different kind, the check is repeated and macros are expanded again until the outermost layer of syntax is no longer a macro.
Elaboration or tactic execution can then proceed.
Only the outermost layer of syntax (typically a {name Lean.Syntax.node}`node`) is expanded, and the output of macro expansion may contain nested syntax that is a macro.
These nested macros are expanded in turn when the elaborator reaches them.

```lean (keep := false) (show := false)
-- Test claim in preceding paragraph that it's OK for macros to give up prior to elab
syntax "doubled " term:arg : term

macro_rules
  | `(term|doubled $n:num) => `($n * 2)
  | `(term|doubled $_) => Lean.Macro.throwUnsupported

/-- info: 10 -/
#guard_msgs in
#eval doubled 5

/--
error: elaboration function for 'termDoubled_' has not been implemented
  doubled (5 + 2)
-/
#guard_msgs in
#eval doubled (5 + 2)

elab_rules : term
  | `(term|doubled $e:term) => Lean.Elab.Term.elabTerm e none

/-- info: 7 -/
#guard_msgs in
#eval doubled (5 + 2)
```

## Hygiene
%%%
tag := "macro-hygiene"
%%%

A macro is {deftech (key:="hygiene")}_hygienic_ if its expansion cannot result in identifier capture.
{deftech}[Identifier capture] is when an identifier ends up referring to a binding site other than that which is in scope where the identifier occurs in the source code.
There are two types of identifier capture:
 * If a macro's expansion introduces binders, then identifiers that are parameters to the macro may end up referring to the introduced binders if their names happen to match.
 * If a macro's expansion is intended to refer to a name, but the macro is used in a context that either locally binds this name or in which a new global name has been introduced, it may end up referring to the wrong name.

The first kind of variable capture can be avoided by ensuring that every binding introduced by a macro uses a freshly generated, globally-unique name, while the second can be avoided by always using fully-qualified names to refer to constants.
The fresh names must be generated again at each invocation of the macro to avoid variable capture in recursive macros.
These techniques are error-prone.
Variable capture issues are difficult to test for because they rely on coincidences of name choices, and consistently applying these techniques results in noisy code.

Lean features automatic hygiene: in almost all cases, macros are automatically hygienic.
Capture by introduced bindings is avoided by annotating identifiers introduced by a macro with {deftech}_macro scopes_, which uniquely identify each invocation of macro expansion.
If the binding and the use of the identifier have the same macro scopes, then they were introduced by the same step of macro expansion and should refer to one another.
Similarly, uses of global names in code generated by a macro are not captured by local bindings in the context in which they are expanded because these use sites have macro scopes that are not present in the binding occurrence.
Capture by newly-introduced global names are prevented by annotating potential global name references with the set of matching globals in code produced in the macro's body.
Identifiers annotated with potential referents are called {deftech}_pre-resolved identifiers_, and the {lean}`Syntax.Preresolved` field on the {name}`Syntax.ident` constructor is used to store the potential referents.

The introduction of macro scopes and pre-resolved identifiers to generated syntax occurs during {tech}[quotation].
Macros that construct syntax by other means than quotation should also ensure hygiene by some other means.
For more details on Lean's hygiene algorithm, please consult {citet beyondNotations ullrich23}[].

## The Macro Monad
%%%
tag := "macro-monad"
%%%

The macro monad {name Lean.MacroM}`MacroM` is sufficiently powerful to implement hygiene and report errors.
Macro expansion does not have the ability to modify the environment directly, to carry out unification, to examine the current local context, or to do anything else that only makes sense in one particular context.
This allows the same macro mechanism to be used throughout Lean, and it makes macros much easier to write than {tech}[elaborators].

{docstring Lean.MacroM}

{docstring Lean.Macro.expandMacro?}

{docstring Lean.Macro.trace}

### Exceptions and Errors
%%%
tag := "macro-exceptions"
%%%

The {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception is used for control flow during macro expansion.
It indicates that the current macro is incapable of expanding the received syntax, but that an error has not occurred.
The exceptions thrown by {name Lean.Macro.throwError}`throwError` and {name Lean.Macro.throwErrorAt}`throwErrorAt` terminate macro expansion, reporting the error to the user.

{docstring Lean.Macro.throwUnsupported}

{docstring Lean.Macro.Exception.unsupportedSyntax}

{docstring Lean.Macro.throwError}

{docstring Lean.Macro.throwErrorAt}

### Hygiene-Related Operations
%%%
tag := "macro-monad-hygiene"
%%%

{tech}[Hygiene] is implemented by adding {tech}[macro scopes] to the identifiers that occur in syntax.
Ordinarily, the process of {tech}[quotation] adds all necessary scopes, but macros that construct syntax directly must add macro scopes to the identifiers that they introduce.

{docstring Lean.Macro.withFreshMacroScope}

{docstring Lean.Macro.addMacroScope}

### Querying the Environment
%%%
tag := "macro-environment"
%%%

Macros have only limited support for querying the environment.
They can check whether a constant exists and resolve names, but further introspection is unavailable.

{docstring Lean.Macro.hasDecl}

{docstring Lean.Macro.getCurrNamespace}

{docstring Lean.Macro.resolveNamespace}

{docstring Lean.Macro.resolveGlobalName}

## Quasiquotation
%%%
tag := "quasiquotation"
%%%

{deftech}_Quotation_ marks code for representation as data of type {name}`Syntax`.
Quoted code is parsed, but not elaborated—while it must be syntactically correct, it need not make sense.
Quotation makes it much easier to programmatically generate code: rather than reverse-engineering the specific nesting of {name Lean.Syntax.node}`node` values that Lean's parser would produce, the parser can be directly invoked to create them.
This is also more robust in the face of refactoring of the grammar that may change the internals of the parse tree without affecting the user-visible concrete syntax.
Quotation in Lean is surrounded by ``​`(`` and `)`.

The syntactic category or parser being quoted may be indicated by placing its name after the opening backtick and parenthesis, followed by a vertical bar (`|`).
As a special case, the name `tactic` may be used to parse either tactics or sequences of tactics.
If no syntactic category or parser is provided, Lean attempts to parse the quotation both as a term and as a non-empty sequence of commands.
Term quotations have higher priority than command quotations, so in cases of ambiguity, the interpretation as a term is chosen; this can be overridden by explicitly indicating that the quotation is of a command sequence.

::::keepEnv
:::example "Term vs Command Quotation Syntax"
```lean (show := false)
open Lean
```

In the following example, the contents of the quotation could either be a function application or a sequence of commands.
Both match the same region of the file, so the {tech}[local longest-match rule] is not relevant.
Term quotation has a higher priority than command quotation, so the quotation is interpreted as a term.
Terms expect their {tech}[antiquotations] to have type {lean}``TSyntax `term`` rather than {lean}``TSyntax `command``.
```lean (error := true) (name := cmdQuot)
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1 $cmd2)
```
The result is two type errors like the following:
```leanOutput cmdQuot
application type mismatch
  cmd1.raw
argument
  cmd1
has type
  TSyntax `command : Type
but is expected to have type
  TSyntax `term : Type
```

The type of the quotation ({lean}``MacroM (TSyntax `command)``) is not used to select a result because syntax priorities are applied prior to elaboration.
In this case, specifying that the antiquotations are commands resolves the ambiguity because function application would require terms in these positions:
```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1:command $cmd2:command)
```
Similarly, inserting a command into the quotation eliminates the possibility that it could be a term:
```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) := `($cmd1 $cmd2 #eval "hello!")
```
:::
::::

```lean (show := false)
-- There is no way to extract parser priorities (they're only saved in the Pratt tables next to
-- compiled Parser code), so this test of priorities checks the observable relative priorities of the
-- quote parsers.

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `term)
-/
#guard_msgs in
#check (`($(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure
      {
        raw :=
          Syntax.node2 info `Lean.Parser.Term.app { raw := Syntax.missing }.raw
            (Syntax.node1 info `null { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `term)
-/
#guard_msgs in
#check (`($(⟨.missing⟩) $(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure
      {
        raw :=
          Syntax.node2 info `null { raw := Syntax.missing }.raw
            { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `command)
-/
#guard_msgs in
#check (`($(⟨.missing⟩):command $(⟨.missing⟩)) : MacroM _)

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `tactic)
-/
#guard_msgs in
#check (`(tactic| $(⟨.missing⟩):tactic) : MacroM _)

/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure
      {
        raw :=
          Syntax.node1 info `Lean.Parser.Tactic.seq1
            (Syntax.node3 info `null { raw := Syntax.missing }.raw (Syntax.atom info ";")
              { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `tactic.seq)
-/
#guard_msgs in
#check (`(tactic|
          $(⟨.missing⟩):tactic; $(⟨.missing⟩)) : MacroM _)
```

:::freeSyntax term (open := false)

Lean's syntax includes quotations for terms, commands, tactics, and sequences of tactics, as well as a general quotation syntax that allows any input that Lean can parse to be quoted.
Term quotations have the highest priority, followed by tactic quotations, general quotations, and finally command quotations.

```grammar
`(term|`($_:term))
*******
"`("$_:command+")"
*******
`(term|`(tactic| $_:tactic))
*******
`(term|`(tactic| $_:tactic;*))
*******
"`("p:ident"|"/-- Parse a {p} here -/")"
```
:::

```lean (show := false)
section M
variable {m : Type → Type}
open Lean (MonadRef MonadQuotation)
open Lean.Elab.Term (TermElabM)
open Lean.Elab.Command (CommandElabM)
open Lean.Elab.Tactic (TacticM)
```

Rather than having type {name}`Syntax`, quotations are monadic actions with type {lean}`m Syntax`.
Quotation is monadic because it implements {tech}[hygiene] by adding {tech}[macro scopes] and preresolving identifiers, as described in {ref "macro-hygiene"}[the section on hygiene].
The specific monad to be used is an implicit parameter to the quotation, and any monad for which there is an instance of the {name}`MonadQuotation` type classe is suitable.
{name}`MonadQuotation` extends {name}`MonadRef`, which gives the quotation access to the source location of the syntax that the macro expander or elaborator is currently processing. {name}`MonadQuotation` additionally includes the ability to add {tech}[macro scopes] to identifiers and use a fresh macro scope for a sub-task.
Monads that support quotation include {name}`MacroM`, {name}`TermElabM`, {name}`CommandElabM`, and {name}`TacticM`.

```lean (show := false)
end M
```


```lean (show := false)
-- Verify claim about monads above
open Lean in
example [Monad m] [MonadQuotation m] : m Syntax := `(term|2 + 2)
```

{deftech}_Quasiquotation_ is a form of quotation that may contain {deftech}_antiquotations_, which are regions of the quotation that are not quoted, but instead are expressions that are evaluated to yield syntax.
A quasiquotation is essentially a template; the outer quoted region provides a fixed framework that always yields the same outer syntax, while the antiquotations yield the parts of the final syntax that vary.
All quotations in Lean are quasiquotations, so no special syntax is needed to distinguish quasiquotations from other quotations.

Basic antiquotations consist of a dollar sign (`$`) followed by an identifier.
This means that the identifier's value, which should be a syntax tree, is to be substituted into this position of the quoted syntax.
Entire expressions may be used as antiquotations by wrapping them in parentheses.

```lean (show := false)
section
open Lean
example (e : Term) : MacroM Syntax := `(term| $e)

example (e : Term) : MacroM Syntax := `(term| $(e))

--example (e : Term) : MacroM Syntax := `(term| $ (e))


end
```



```lean (show := false)
section
open Lean (TSyntax SyntaxNodeKinds)
variable {c : SyntaxNodeKinds}
```

Lean's parser assigns every antiquotation a syntax category based on what the parser expects at the given position.
If the parser expects syntax category {lean}`c`, then the antiquotation's type must be {lean}`TSyntax c`.
Some syntax categories can be matched by elements of other categories.
For example, numeric and string literals are valid terms in addition to being their own syntax categories.
Antiquotations may be annotated with the expected category, which causes the parser to validate that the annotated category is acceptable in the given position and construct any intermediate layers that are required in the parse tree.

::::keepEnv
:::example "Antiquotation Annotations"
```lean (show := false)
open Lean
```

This example requires that {lean}`m` is a monad that can perform quotation.
```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```

By default, the antiquotation `$e` is expected to be a term, because that's the syntactic category that's immediately expected as the second argument to addition.
```lean (name := ex1)
def ex1 (e) := show m _ from `(2 + $e)
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `term) : m (TSyntax `term)
```

Annotating `$e` as a numeric literal succeeds, because numeric literals are also valid terms.
The expected type of the parameter `e` changes to ``TSyntax `num``.
```lean (name := ex2)
def ex2 (e) := show m _ from `(2 + $e:num)
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `num) : m (TSyntax `term)
```
:::
::::

```lean (show := false)
end
```

Antiquotations also support optionality and repetition with optional separators.


::::keepEnv
:::example "Repetition Annotations"
```lean (show := false)
open Lean
```

This example requires that {lean}`m` is a monad that can perform quotation.
```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```

By default, the antiquotation `$e` is expected to be an array of terms separated by commas, as is expected in the body of a list:
```lean (name := ex1)
def ex1 (xs) := show m _ from `(#[$xs,*])
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Syntax.TSepArray `term ",") : m (TSyntax `term)
```

However, Lean includes a collection of coercions between various representations of arrays that will automatically insert or remove separators, so an ordinary array of terms is also acceptable:
```lean (name := ex2)
def ex2 (xs : Array (TSyntax `term)) := show m _ from `(#[$xs,*])
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array (TSyntax `term)) : m (TSyntax `term)
```

:::
::::

```lean (show := false)
section
open Lean Syntax
variable {k k' : SyntaxNodeKinds} {sep : String} [Coe (TSyntax k) (TSyntax k')]
-- Demonstrate the coercions between different kinds of repeated syntax

/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k' sep)

/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
#synth CoeHTCT (Array (TSyntax k)) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#guard_msgs in
#synth CoeHTCT (TSepArray k sep) (TSyntaxArray k)

end
```

:::freeSyntax antiquot (open := true) (title := "Token Antiquotations")

Token antiquotations replace the source information (of type {name Lean.SourceInfo}`SourceInfo`) on a token with the source information from some other syntax.

```grammar
str"%$"ident
```
:::

::: TODO
Syntax of antiquotes (requires hack)

All kinds of antiquotes:
 * `$x`
 * `$x:cat`
 * `$(tm)`
 * `$x\*`
 * `$[$x]?/*,`
 * `"foo"%$tk`
:::


:::example "Quasiquotation"

Both forms of antiquotation are used in this example.
Because natural numbers are not syntax, {name Lean.quote}`quote` is used to transform a number into syntax that represents it.

```lean
open Lean in
example [Monad m] [MonadQuotation m] (x : Term) (n : Nat) : m Syntax :=
  `($x + $(quote (n + 2)))
```
:::

::::keepEnv
:::example "Expanding Quasiquotation"
```lean
open Lean in
def f [Monad m] [MonadQuotation m] (x : Term) (n : Nat) : m Syntax :=
  `(fun k => $x + $(quote (n + 2)) + k)
#print f
```

:::
::::

## Matching Syntax

::: TODO
 * Quasiquotations
   * Troubleshooting: longest match
:::

## Macro Attribute

## The `macro_rules` and `macro` commands

# Elaborators
%%%
tag := "elaborators"
%%%

:::planned 72
For now, a quick overview of elaborators - detailed description to be written in a later revision
:::
