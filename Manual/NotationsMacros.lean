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
import Manual.NotationsMacros.SyntaxDef
import Manual.NotationsMacros.Elab
import Manual.NotationsMacros.Delab

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Notations and Macros" =>
%%%
tag := "language-extension"
%%%

Different mathematical fields have their own notational conventions, and many notations are re-used with differing meanings in different fields.
It is important that formal developments are able to use established notations: formalizing mathematics is already difficult, and the mental overhead of translating between syntaxes can be substantial.
At the same time, it's important to be able to control the scope of notational extensions.
Many fields use related notations with very different meanings, and it should be possible to combine developments from these separate fields in a way where both readers and the system know which convention is in force in any given region of a file.

Lean addresses the problem of notational extensibility with a variety of mechanisms, each of which solves a different aspect of the problem.
They can be combined flexibly to achieve the necessary results:

 * The {ref "parser"}_extensible parser_ {index}[parser] allows a great variety of notational conventions to be implemented declaratively, and combined flexibly.
 * {ref "macro-and-elab"}[Macros] allow new syntax to be easily mapped to existing syntax, which is a simple way to provide meaning to new constructs.
  Due to {tech}[hygiene] and automatic propagation of source positions, this process doesn't interfere with Lean's interactive features.
 * {ref "macro-and-elab"}[Elaborators] provide new syntax with the same tools available to Lean's own syntax in cases where a macro is insufficiently expressive.
 * {ref "notations"}[Notations] allow the simultaneous definition of a parser extension, a macro, and a pretty printer.
   When defining infix, prefix, or postfix operators, {ref "operators"}[custom operators] automatically take care of precedence and associativity.
 * Low-level parser extensions allow the parser to be extended in ways that modify its rules for tokens and whitespace, or that even completely replace Lean's syntax. This is an advanced topic that requires familiarity with Lean internals; nevertheless, the possibility of doing this without modifying the compiler is important. This reference manual is written using a language extension that replaces Lean's concrete syntax with a Markdown-like language for writing documents, but the source files are still Lean files.

{include 0 Manual.NotationsMacros.Operators}

{include 0 Manual.NotationsMacros.Precedence}

{include 0 Manual.NotationsMacros.Notations}

{include 0 Manual.NotationsMacros.SyntaxDef}

# Macros
%%%
tag := "macros"
%%%

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
  | `(term|notFive 5) =>
    Macro.throwError "'5' is not allowed here"
  | `(term|notFive $e) =>
    pure e
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

In particular, macro expansion occurs in three situations in Lean:

 1. During term elaboration, macros in the outermost layer of the syntax to be elaborated are expanded prior to invoking the {ref "elaborators"}[syntax's term elaborator].

 2. During command elaboration, macros in the outermost layer of the syntax to be elaborated are expanded prior to invoking the {ref "elaborators"}[syntax's command elaborator].

 3. During tactic execution, macros in the outermost layer of the syntax to be elaborated are expanded {ref "tactic-macros"}[prior to executing the syntax as a tactic].


```lean (keep := false) (show := false)
-- Test claim in preceding paragraph that it's OK for macros to give up prior to elab
syntax "doubled " term:arg : term

macro_rules
  | `(term|doubled $n:num) => `($n * 2)
  | `(term|doubled $_) => Lean.Macro.throwUnsupported

/-- info: 10 -/
#check_msgs in
#eval doubled 5

/--
error: elaboration function for 'termDoubled_' has not been implemented
  doubled (5 + 2)
-/
#check_msgs in
#eval doubled (5 + 2)

elab_rules : term
  | `(term|doubled $e:term) => Lean.Elab.Term.elabTerm e none

/-- info: 7 -/
#check_msgs in
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
Capture by newly-introduced global names is prevented by annotating potential global name references with the set of global names that match at quotation time in code produced in the macro's body.
Identifiers annotated with potential referents are called {deftech}_pre-resolved identifiers_, and the {lean}`Syntax.Preresolved` field on the {name}`Syntax.ident` constructor is used to store the potential referents.
During elaboration, if an identifier has pre-resolved global names associated with it, then other global names are not considered as valid reference targets.

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

## Quotation
%%%
tag := "quotation"
%%%

{deftech}_Quotation_ marks code for representation as data of type {name}`Syntax`.
Quoted code is parsed, but not elaborated—while it must be syntactically correct, it need not make sense.
Quotation makes it much easier to programmatically generate code: rather than reverse-engineering the specific nesting of {name Lean.Syntax.node}`node` values that Lean's parser would produce, the parser can be directly invoked to create them.
This is also more robust in the face of refactoring of the grammar that may change the internals of the parse tree without affecting the user-visible concrete syntax.
Quotation in Lean is surrounded by `` `( `` and `)`.

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
Application type mismatch: In the application
  cmd1.raw
the argument
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
#check_msgs in
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
#check_msgs in
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
#check_msgs in
#check (`($(⟨.missing⟩):command $(⟨.missing⟩)) : MacroM _)

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.getMainModule
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `tactic)
-/
#check_msgs in
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
#check_msgs in
#check (`(tactic|
          $(⟨.missing⟩):tactic; $(⟨.missing⟩)) : MacroM _)
```

:::freeSyntax term (open := false) (title := "Quotations")

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
Quotation is monadic because it implements {tech}[hygiene] by adding {tech}[macro scopes] and pre-resolving identifiers, as described in {ref "macro-hygiene"}[the section on hygiene].
The specific monad to be used is an implicit parameter to the quotation, and any monad for which there is an instance of the {name}`MonadQuotation` type class is suitable.
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

### Quasiquotation
%%%
tag := "quasiquotation"
%%%

{deftech}_Quasiquotation_ is a form of quotation that may contain {deftech}_antiquotations_, which are regions of the quotation that are not quoted, but instead are expressions that are evaluated to yield syntax.
A quasiquotation is essentially a template; the outer quoted region provides a fixed framework that always yields the same outer syntax, while the antiquotations yield the parts of the final syntax that vary.
All quotations in Lean are quasiquotations, so no special syntax is needed to distinguish quasiquotations from other quotations.
The quotation process does not add macro scopes to identifiers that are inserted via antiquotations, because these identifiers either come from another quotation (in which case they already have macro scopes) or from the macro's input (in which case they should not have macro scopes, because they are not introduced by the macro).

Basic antiquotations consist of a dollar sign (`$`) immediately followed by an identifier.
This means that the value of the corresponding variable, which should be a syntax tree, is to be substituted into this position of the quoted syntax.
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
If the parser expects syntax category {lean}`c`, then the antiquotation's type is {lean}`TSyntax c`.


Some syntax categories can be matched by elements of other categories.
For example, numeric and string literals are valid terms in addition to being their own syntax categories.
Antiquotations may be annotated with the expected category by suffixing them with a colon and the category name, which causes the parser to validate that the annotated category is acceptable in the given position and construct any intermediate layers that are required in the parse tree.

:::freeSyntax antiquot title:="Antiquotations" open := false
```grammar
"$"ident(":"ident)?
*******
"$("term")"(":"ident)?
```
Whitespace is not permitted between the dollar sign ('$') that initiates an antiquotation and the identifier or parenthesized term that follows.
Similarly, no whitespace is permitted around the colon that annotates the syntax category of the antiquotation.
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

:::::keepEnv
::::example "Antiquotation Annotations"
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

Spaces are not allowed between the dollar sign and the identifier.
```syntaxError ex2err1
def ex2 (e) := show m _ from `(2 + $ e:num)
```
```leanOutput ex2err1
<example>:1:34-1:36: unexpected token '$'; expected '`(tactic|' or no space before spliced term
```

Spaces are also not allowed before the colon:
```syntaxError ex2err2
def ex2 (e) := show m _ from `(2 + $e :num)
```
```leanOutput ex2err2
<example>:1:37-1:39: unexpected token ':'; expected ')'
```
::::
:::::

```lean (show := false)
end
```

:::::keepEnv
::::example "Expanding Quasiquotation"
Printing the definition of {name}`f` demonstrates the expansion of a quasiquotation.
```lean (name := expansion)
open Lean in
def f [Monad m] [MonadQuotation m]
    (x : Term) (n : Nat) : m Syntax :=
  `(fun k => $x + $(quote (n + 2)) + k)
#print f
```
```leanOutput expansion
def f : {m : Type → Type} → [Monad m] → [Lean.MonadQuotation m] → Lean.Term → Nat → m Syntax :=
fun {m} [Monad m] [Lean.MonadQuotation m] x n => do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let scp ← Lean.getCurrMacroScope
  let mainModule ← Lean.getMainModule
  pure
      {
          raw :=
            Syntax.node2 info `Lean.Parser.Term.fun (Syntax.atom info "fun")
              (Syntax.node4 info `Lean.Parser.Term.basicFun
                (Syntax.node1 info `null (Syntax.ident info "k".toSubstring' (Lean.addMacroScope mainModule `k scp) []))
                (Syntax.node info `null #[]) (Syntax.atom info "=>")
                (Syntax.node3 info `«term_+_»
                  (Syntax.node3 info `«term_+_» x.raw (Syntax.atom info "+") (Lean.quote `term (n + 2)).raw)
                  (Syntax.atom info "+")
                  (Syntax.ident info "k".toSubstring' (Lean.addMacroScope mainModule `k scp) []))) }.raw
```

:::paragraph
```lean (show := false)
section
open Lean (Term)
open Lean.Quote
variable {x : Term} {n : Nat}
```

In this output, the quotation is a {keywordOf Lean.Parser.Term.do}`do` block.
It begins by constructing the source information for the resulting syntax, obtained by querying the compiler about the current user syntax being processed.
It then obtains the current macro scope and the name of the module being processed, because macro scopes are added with respect to a module to enable independent compilation and avoid the need for a global counter.
It then constructs a node using helpers such as {name}`Syntax.node1` and {name}`Syntax.node2`, which create a {name}`Syntax.node` with the indicated number of children.
The macro scope is added to each identifier, and {name Lean.TSyntax.raw}`TSyntax.raw` is used to extract the contents of typed syntax wrappers.
The antiquotations of {lean}`x` and {lean type:="Term"}`quote (n + 2)` occur directly in the expansion, as parameters to {name}`Syntax.node3`.

```lean (show := false)
end
```
:::

::::
:::::


### Splices
%%%
tag := "splices"
%%%

In addition to including other syntax via antiquotations, quasiquotations can include {deftech}_splices_.
Splices indicate that the elements of an array are to be inserted in order.
The repeated elements may include separators, such as the commas between list or array elements.
Splices may consist of an ordinary antiquotation with a {deftech}_splice suffix_, or they may be {deftech}_extended splices_ that provide additional repeated structure.

Splice suffixes consist of either an asterisk or a valid atom followed by an asterisk (`*`).
Suffixes may follow any identifier or term antiquotation.
An antiquotation with the splice suffix `*` corresponds to a use of `many` or `many1`; both the `*` and `+` suffixes in syntax rules correspond to the `*` splice suffix.
An antiquotation with a splice suffix that includes an atom prior to the asterisk corresponds to a use of `sepBy` or `sepBy1`.
The splice suffix `?` corresponds to a use of `optional` or the `?` suffix in a syntax rule.
Because `?` is a valid identifier character, identifiers must be parenthesized to use it as a suffix.

While there is overlap between repetition specifiers for syntax and antiquotation suffixes, they have distinct syntaxes.
When defining syntax, the suffixes `*`, `+`, `,*`, `,+`, `,*,?`, and `,+,?` are built in to Lean.
There is no shorter way to specify separators other than `,`.
Antiquotation suffixes are either just `*` or whatever atom was provided to `sepBy` or `sepBy1` followed by `*`.
The syntax repetitions `+` and `*` correspond to the splice suffix `*`; the repetitions `,*`, `,+`, `,*,?`, and `,+,?` correspond to `,*`.
The optional suffix `?` in syntax and splices correspond with each other.


:::table (header := true)
 * - Syntax Repetition
   - Splice Suffix
 * - `+` `*`
   - `*`
 * - `,*` `,+` `,*,?` `,+,?`
   - `,*`
 * - `sepBy(_, "S")` `sepBy1(_, "S")`
   - `S*`
 * - `?`
   - `?`
:::


::::keepEnv
:::example "Suffixed Splices"
```lean (show := false)
open Lean
open Lean.Elab.Command (CommandElabM)
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
def ex2 (xs : Array (TSyntax `term)) :=
  show m _ from `(#[$xs,*])
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array (TSyntax `term)) : m (TSyntax `term)
```

Repetition annotations may also be used with term antiquotations and syntax category annotations.
This example is in {name Lean.Elab.Command.CommandElabM}`CommandElabM` so the result can be conveniently logged.
```lean (name := ex3)
def ex3 (size : Nat) := show CommandElabM _ from do
  let mut nums : Array Nat := #[]
  for i in [0:size] do
    nums := nums.push i
  let stx ← `(#[$(nums.map (Syntax.mkNumLit ∘ toString)):num,*])
  -- Using logInfo here causes the syntax to be rendered via
  -- the pretty printer.
  logInfo stx

#eval ex3 4
```
```leanOutput ex3
#[0, 1, 2, 3]
```
:::
::::

::::keepEnv
:::example "Non-Comma Separators"
The following unconventional syntax for lists separates numeric elements by either em dashes or double asterisks, rather than by commas.
```lean
syntax "⟦" sepBy1(num, " — ") "⟧": term
syntax "⟦" sepBy1(num, " ** ") "⟧": term
```
This means that `—*` and `***` are valid splice suffixes between the `⟦` and `⟧` atoms.
In the case of `***`, the first two asterisks are the atom in the syntax rule, while the third is the repetition suffix.
```lean
macro_rules
  | `(⟦$n:num—*⟧) => `(⟦$n***⟧)
  | `(⟦$n:num***⟧) => `([$n,*])
```
```lean (name := nonComma)
#eval ⟦1 — 2 — 3⟧
```
```leanOutput nonComma
[1, 2, 3]
```
:::
::::

::::keepEnv
:::example "Optional Splices"
The following syntax declaration optionally matches a term between two tokens.
The parentheses around the nested `term` are needed because `term?` is a valid identifier.
```lean (show := false)
open Lean
```
```lean
syntax "⟨| " (term)? " |⟩": term
```

The `?` splice suffix for a term expects an {lean}`Option Term`:
```lean
def mkStx [Monad m] [MonadQuotation m]
    (e : Option Term) : m Term :=
  `(⟨| $(e)? |⟩)
```
```lean (name := checkMkStx)
#check mkStx
```
```leanOutput checkMkStx
mkStx {m : Type → Type} [Monad m] [MonadQuotation m] (e : Option Term) : m Term
```

Supplying {name}`some` results in the optional term being present.
```lean (name := someMkStx)
#eval do logInfo (← mkStx (some (quote 5)))
```
```leanOutput someMkStx
⟨| 5 |⟩
```

Supplying {name}`none` results in the optional term being absent.
```lean (name := noneMkStx)
#eval do logInfo (← mkStx none)
```
```leanOutput noneMkStx
⟨| |⟩
```

:::
::::

```lean (show := false)
section
open Lean Syntax
variable {k k' : SyntaxNodeKinds} {sep : String} [Coe (TSyntax k) (TSyntax k')]
-- Demonstrate the coercions between different kinds of repeated syntax

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k' sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (Array (TSyntax k)) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSepArray k sep) (TSyntaxArray k)

end
```

### Token Antiquotations
%%%
tag := "token-antiquotations"
%%%

In addition to antiquotations of complete syntax, Lean features {deftech}_token antiquotations_ which allow the source information of an atom to be replaced with the source information from some other syntax.
The resulting synthetic source information is marked {tech}[canonical] so that it will be used for error messages, proof states, and other feedback.
This is primarily useful to control the placement of error messages or other information that Lean reports to users.
A token antiquotation does not allow an arbitrary atom to be inserted via evaluation.
A token antiquotation consists of an atom (that is, a keyword)

:::freeSyntax antiquot (open := true) (title := "Token Antiquotations")
Token antiquotations replace the source information (of type {name Lean.SourceInfo}`SourceInfo`) on a token with the source information from some other syntax.

```grammar
atom"%$"ident
```
:::


::: TODO

More complex splices with brackets

:::

## Matching Syntax
%%%
tag := "quote-patterns"
%%%

Quasiquotations can be used in pattern matching to recognize syntax that matches a template.
Just as antiquotations in a quotation that's used as a term are regions that are treated as ordinary non-quoted expressions, antiquotations in patterns are regions that are treated as ordinary Lean patterns.
Quote patterns are compiled differently from other patterns, so they can't be intermixed with non-quote patterns in a single {keywordOf Lean.Parser.Term.match}`match` expression.
Like ordinary quotations, quote patterns are first processed by Lean's parser.
The parser's output is then compiled into code that determines whether there is a match.
Syntax matching assumes that the syntax being matched was produced by Lean's parser, either via quotation or directly in user code, and uses this to omit some checks.
For example, if nothing but a particular keyword can be present in a given position, the check may be omitted.

Syntax matches a quote pattern in the following cases:


 : Atoms

  Keyword atoms (such as {keywordOf termIfThenElse}`if` or {keywordOf Lean.Parser.Term.match}`match`) result in singleton nodes whose kind is `token.` followed by the atom.
  In many cases, it is not necessary to check for specific atom values because the grammar allows only a single keyword, and no checking will be performed.
  If the syntax of the term being matched requires the check, then the node kind is compared.

  Literals, such as string or numeric literals, are compared via their underlying string representation.
  The pattern `` `(0x15) `` and the quotation `` `(21) `` do not match.

 : Nodes

  If both the pattern and the value being matched represent {name}`Syntax.node`, there is a match when both have the same syntax kind, the same number of children, and each child pattern matches the corresponding child value.

 : Identifiers

  If both the pattern and the value being matched are identifiers, then their literal {name Lean.Name}`Name` values are compared for equality modulo macro scopes.
  Identifiers that “look” the same match, and it does not matter if they refer to the same binding.
  This design choice allows quote pattern matching to be used in contexts that don't have access to a compile-time environment in which names can be compared by reference.


Because quotation pattern matching is based on the node kinds emitted by the parser, quotations that look identical may not match if they come from different syntax categories.
If in doubt, including the syntax category in the quotation can help.

## Defining Macros
%%%
tag := "defining-macros"
%%%


There are two primary ways to define macros: the {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command and the {keywordOf Lean.Parser.Command.macro}`macro` command.
The {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command associates a macro with existing syntax, while the {keywordOf Lean.Parser.Command.macro}`macro` command simultaneously defines new syntax and a macro that translates it to existing syntax.
The {keywordOf Lean.Parser.Command.macro}`macro` command can be seen as a generalization of {keywordOf Lean.Parser.Command.notation}`notation` that allows the expansion to be generated programmatically, rather than simply by substitution.

### The `macro_rules` Command
%%%
tag := "macro_rules"
%%%

:::syntax command (title := "Rule-Based Macros With {keyword}`macro_rules`")

The {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command takes a sequence of rewrite rules, specified as syntax pattern matches, and adds each as a macro.
The rules are attempted in order, before previously-defined macros, and later macro definitions may add further macro rules.

```grammar
$[$d:docComment]?
$[@[$attrs,*]]?
$_:attrKind macro_rules $[(kind := $k)]?
  $[| `(free{(p:ident"|")?/-- Suitable syntax for {p} -/}) => $e]*
```
:::

The patterns in the macros must be quotation patterns.
They may match syntax from any syntax category, but a given pattern can only ever match a single syntax kind.
If no category or parser is specified for the quotation, then it may match terms or (sequences of) commands, but never both.
In case of ambiguity, the term parser is chosen.

Internally, macros are tracked in a table that maps each {tech}[syntax kind] to its macros.
The {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command may be explicitly annotated with a syntax kind.

If a syntax kind is explicitly provided, the macro definition checks that each quotation pattern has that kind.
If the parse result for the quotation was a {tech}[choice node] (that is, if the parse was ambiguous), then the pattern is duplicated once for each alternative with the specified kind.
It is an error if none of the alternatives have the specified kind.

If no kind is provided explicitly, then the kind determined by the parser is used for each pattern.
The patterns are not required to all have the same syntax kind; macros are defined for each syntax kind used by at least one of the patterns.
It is an error if the parse result for a quotation pattern was a {tech}[choice node] (that is, if the parse was ambiguous).

The documentation comment associated with {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` is displayed to users if the syntax itself has no documentation comment.
Otherwise, the documentation comment for the syntax itself is shown.

As with {ref "notations"}[notations] and {ref "operators"}[operators], macro rules may be declared `scoped` or `local`.
Scoped macros are only active when the current namespace is open, and local macro rules are only active in the current {tech}[section scope].

::::keepEnv
:::example "Idiom Brackets"
Idiom brackets are an alternative syntax for working with applicative functors.
If the idiom brackets contain a function application, then the function is wrapped in {name}`pure` and applied to each argument using `<*>`. {TODO}[Operator hyperlinking to docs]
Lean does not support idiom brackets by default, but they can be defined using a macro.
```lean
syntax (name := idiom) "⟦" (term:arg)+ "⟧" : term

macro_rules
  | `(⟦$f $args*⟧) => do
    let mut out ← `(pure $f)
    for arg in args do
      out ← `($out <*> $arg)
    return out
```

This new syntax can be used immediately.
```lean
def addFirstThird [Add α] (xs : List α) : Option α :=
  ⟦Add.add xs[0]? xs[2]?⟧
```
```lean (name := idiom1)
#eval addFirstThird (α := Nat) []
```
```leanOutput idiom1
none
```
```lean (name := idiom2)
#eval addFirstThird [1]
```
```leanOutput idiom2
none
```
```lean (name := idiom3)
#eval addFirstThird [1,2,3,4]
```
```leanOutput idiom3
some 4
```
:::
::::

::::keepEnv
:::example "Scoped Macros"
Scoped macro rules are active only in their namespace.
When the namespace `ConfusingNumbers` is open, numeric literals will be assigned an incorrect meaning.
````lean
namespace ConfusingNumbers
````

The following macro recognizes terms that are odd numeric literals, and replaces them with double their value.
If it unconditionally replaced them with double their value, then macro expansion would become an infinite loop because the same rule would always match the output.

```lean
scoped macro_rules
  | `($n:num) => do
    if n.getNat % 2 = 0 then Lean.Macro.throwUnsupported
    let n' := (n.getNat * 2)
    `($(Syntax.mkNumLit (info := n.raw.getHeadInfo) (toString n')))
```

Once the namespace ends, the macro is no longer used.
````lean
end ConfusingNumbers
````

Without opening the namespace, numeric literals function in the usual way.
```lean (name := nums1)
#eval (3, 4)
```
```leanOutput nums1
(3, 4)
```

When the namespace is open, the macro replaces {lean}`3` with {lean}`6`.
```lean (name := nums2)
open ConfusingNumbers

#eval (3, 4)
```
```leanOutput nums2
(6, 4)
```

It is not typically useful to change the interpretation of numeric or other literals in macros.
However, scoped macros can be very useful when adding new rules to extensible tactics such as {tactic}`trivial` that work well with the contents of the namespaces but should not always be used.
:::
::::

Behind the scenes, a {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command generates one macro function for each syntax kind that is matched in its quote patterns.
This function has a default case that throws the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception, so further macros may be attempted.


A single {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command with two rules is not always equivalent to two separate single-match commands.
First, the rules in a {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` are tried from top to bottom, but recently-declared macros are attempted first, so the order would need to be reversed.
Additionally, if an earlier rule in the macro throws the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception, then the later rules are not tried; if they were instead in separate {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` commands, then they would be attempted.

::::example "One vs. Two Sets of Macro Rules"

```lean (show := false)
open Lean.Macro
```

The `arbitrary!` macro is intended to expand to some arbitrarily-determined value of a given type.

```lean
syntax (name := arbitrary!) "arbitrary! " term:arg : term
```

:::keepEnv
```lean
macro_rules
  | `(arbitrary! ()) => `(())
  | `(arbitrary! Nat) => `(42)
  | `(arbitrary! ($t1 × $t2)) => `((arbitrary! $t1, arbitrary! $t2))
  | `(arbitrary! Nat) => `(0)
```

Users may extend it by defining further sets of macro rules, such as this rule for {lean}`Empty` that fails:
```lean
macro_rules
  | `(arbitrary! Empty) => throwUnsupported
```

```lean (name := arb1)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb1
(42, 42)
```
:::

:::keepEnv
If all of the macro rules had been defined as individual cases, then the result would have instead used the later case for {lean}`Nat`.
This is because the rules in a single {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command are checked from top to bottom, but more recently-defined {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` commands take precedence over earlier ones.

```lean
macro_rules
  | `(arbitrary! ()) =>
    `(())
macro_rules
  | `(arbitrary! Nat) =>
    `(42)
macro_rules
  | `(arbitrary! ($t1 × $t2)) =>
    `((arbitrary! $t1, arbitrary! $t2))
macro_rules
  | `(arbitrary! Nat) =>
    `(0)
macro_rules
  | `(arbitrary! Empty) =>
    throwUnsupported
```

```lean (name := arb2)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb2
(0, 0)
```
:::

Additionally, if any rule throws the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception, no further rules in that command are checked.
```lean
macro_rules
  | `(arbitrary! (List Nat)) => throwUnsupported
  | `(arbitrary! (List $_)) => `([])

macro_rules
  | `(arbitrary! (Array Nat)) => `(#[42])
macro_rules
  | `(arbitrary! (Array $_)) => throwUnsupported
```

The case for {lean}`List Nat` fails to elaborate, because macro expansion did not translate the {keywordOf arbitrary!}`arbitrary!` syntax into something supported by the elaborator.
```lean (name := arb3) (error := true)
#eval arbitrary! (List Nat)
```
```leanOutput arb3
elaboration function for 'arbitrary!' has not been implemented
  arbitrary! (List Nat)
```

The case for {lean}`Array Nat` succeeds, because the first set of macro rules are attempted after the second throws the exception.
```lean (name := arb4)
#eval arbitrary! (Array Nat)
```
```leanOutput arb4
#[42]
```
::::


### The `macro` Command
%%%
tag := "macro-command"
%%%

```lean (show := false)
section
open Lean
```

The {keywordOf Lean.Parser.Command.macro}`macro` command simultaneously defines a new {tech}[syntax rule] and associates it with a {tech}[macro].
Unlike {keywordOf Lean.Parser.Command.notation}`notation`, which can define only new term syntax and in which the expansion is a term into which the parameters are to be substituted, the {keywordOf Lean.Parser.Command.macro}`macro` command may define syntax in any {tech}[syntax category] and it may use arbitrary code in the {name}`MacroM` monad to generate the expansion.
Because macros are so much more flexible than notations, Lean cannot automatically generate an unexpander; this means that new syntax implemented via the {keywordOf Lean.Parser.Command.macro}`macro` command is available for use in _input_ to Lean, but Lean's output does not use it without further work.

:::syntax command (title := "Macro Declarations")
```grammar
$[$_:docComment]?
$[@[$attrs,*]]?
$_:attrKind macro$[:$p]? $[(name := $_)]? $[(priority := $_)]? $xs:macroArg* : $k:ident =>
  $tm
```
:::

:::syntax Lean.Parser.Command.macroArg (open := false) (title := "Macro Arguments")
A macro's arguments are either syntax items (as used in the {keywordOf Lean.Parser.Command.syntax}`syntax` command) or syntax items with attached names.
```grammar
$s:stx
```
```grammar
$x:ident:$stx
```
:::

In the expansion, the names that are attached to syntax items are bound; they have type {name Lean.TSyntax}`TSyntax` for the appropriate syntax kinds.
If the syntax matched by the parser does not have a defined kind (e.g. because the name is applied to a complex specification), then the type is {lean}`TSyntax Name.anonymous`.

```lean (show := false) (keep := false)
-- Check the typing rules
open Lean Elab Term Macro Meta

elab "dbg_type " e:term ";" body:term : term => do
  let e' ← elabTerm e none
  let t ← inferType e'
  logInfoAt e t
  elabTerm body none

/--
info: TSyntax `str
---
info: TSyntax Name.anonymous
---
info: Syntax.TSepArray `num ","
-/
#check_msgs in
macro "gah!" thing:str other:(str <|> num) arg:num,* : term => do
  dbg_type thing; pure ()
  dbg_type other; pure ()
  dbg_type arg; pure ()
  return quote s!"{thing.raw} ||| {other.raw} ||| {arg.getElems}"

/-- info: "(str \"\\\"one\\\"\") ||| (num \"44\") ||| #[(num \"2\"), (num \"3\")]" : String -/
#check_msgs in
#check gah! "one" 44 2,3

```

The documentation comment is associated with the new syntax, and the attribute kind (none, `local`, or `scoped`) governs the visibility of the macro just as it does for notations: `scoped` macros are available in the namespace in which they are defined or in any {tech}[section scope] that opens that namespace, while `local` macros are available only in the local section scope.

Behind the scenes, the {keywordOf Lean.Parser.Command.macro}`macro` command is itself implemented by a macro that expands it to a {keywordOf Lean.Parser.Command.syntax}`syntax` command and a {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command.
Any attributes applied to the macro command are applied to the syntax definition, but not to the {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` command.

```lean (show := false)
end
```

### The Macro Attribute
%%%
tag := "macro-attribute"
%%%

{tech}[Macros] can be manually added to a syntax kind using the {keywordOf Lean.Parser.Attr.macro}`macro` attribute.
This low-level means of specifying macros is typically not useful, except as a result of code generation by macros that themselves generate macro definitions.

:::syntax attr (title := "The {keyword}`macro` Attribute")
The {keywordOf Lean.Parser.Attr.macro}`macro` attribute specifies that a function is to be considered a {tech}[macro] for the specified syntax kind.
```grammar
macro $_:ident
```
:::

::::keepEnv
:::example "The Macro Attribute"
```lean (show := false)
open Lean Macro
```
```lean
/-- Generate a list based on N syntactic copies of a term -/
syntax (name := rep) "[" num " !!! " term "]" : term

@[macro rep]
def expandRep : Macro
  | `([ $n:num !!! $e:term]) =>
    let e' := Array.mkArray n.getNat e
    `([$e',*])
  | _ =>
    throwUnsupported
```

Evaluating this new expression demonstrates that the macro is present.
```lean (name := attrEx1)
#eval [3 !!! "hello"]
```
```leanOutput attrEx1
["hello", "hello", "hello"]
```
:::
::::

{include 0 Manual.NotationsMacros.Elab}

{include 0 Manual.NotationsMacros.Delab}
