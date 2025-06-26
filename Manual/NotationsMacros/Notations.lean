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

#doc (Manual) "Notations" =>
%%%
tag := "notations"
%%%

The term {deftech}_notation_ is used in two ways in Lean: it can refer to the general concept of concise ways of writing down ideas, and it is the name of a language feature that allows notations to be conveniently implemented with little code.
Like custom operators, Lean notations allow the grammar of terms to be extended with new forms.
However, notations are more general: the new syntax may freely intermix required keywords or operators with subterms, and they provide more precise control over precedence levels.
Notations may also rearrange their parameters in the resulting subterms, while infix operators provide them to the function term in a fixed order.
Because notations may define operators that use a mix of prefix, infix, and postfix components, they can be called {deftech}_mixfix_ operators.

:::syntax command (title := "Notation Declarations")
Notations are defined using the {keywordOf Lean.Parser.Command.notation}`notation` command.

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind notation$[:$_:prec]? $[(name := $_:ident)]? $[(priority := $_:prio)]? $[$_:notationItem]* => $_:term
```
:::

:::syntax Lean.Parser.Command.notationItem (open := false) (title := "Notation Items")
The body of a notation definition consists of a sequence of {deftech}_notation items_, which may be either string literals or identifiers with optional precedences.
```grammar
$s:str
```
```grammar
$x:ident$[:$_:prec]?
```
:::

As with operator declarations, the contents of the documentation comments are shown to users while they interact with the new syntax.
Adding the {attr}`inherit_doc` attribute causes the documentation comment of the function at the head of the term into which the notation expands to be copied to the new syntax.
Other attributes may be added to invoke other compile-time metaprograms on the resulting definition.

Notations interact with {tech}[section scopes] in the same manner as attributes and operators.
By default, notations are available in any module that transitively imports the one in which they are established, but they may be declared `scoped` or `local` to restrict their availability either to contexts in which the current namespace has been opened or to the current {tech}[section scope], respectively.

Like operators, the {tech}[local longest-match rule] is used while parsing notations.
If more than one notation ties for the longest match, the declared priorities are used to determine which parse result applies.
If this still does not resolve the ambiguity, then all are saved, and the elaborator is expected to attempt all of them, succeeding when exactly one can be elaborated.

Rather than a single operator with its fixity and token, the body of a notation declaration consists of a sequence of {deftech}_notation items_, which may be either new {tech}[atoms] (including both keywords such as `if`, `#eval`, or `where` and symbols such as `=>`, `+`, `↗`, `⟦`, or `⋉`) or positions for terms.
Just as they do in operators, string literals identify the placement of atoms.
Leading and trailing spaces in the strings do not affect parsing, but they cause Lean to insert spaces in the corresponding position when displaying the syntax in {tech}[proof states] and error messages.
Identifiers indicate positions where terms are expected, and name the corresponding term so it can be inserted in the notation's expansion.

While custom operators have a single notion of precedence, there are many involved in a notation.
The notation itself has a precedence, as does each term to be parsed.
The notation's precedence determines which contexts it may be parsed in: the parser only attempts to parse productions whose precedence is at least as high as the current context.
For example, because multiplication has higher precedence than addition, the parser will attempt to parse an infix multiplication term while parsing the arguments to addition, but not vice versa.
The precedence of each term to be parsed determines which other productions may occur in them.

If no precedence is supplied for the notation itself, the default value depends on the form of the notation.
If the notation both begins and ends with an atom (represented by string literals), then the default precedence is `max`.{TODO}[keywordOf]
This applies both to notations that consist only of a single atom and to notations with multiple items, in which the first and last items are both atoms.
Otherwise, the default precedence of the whole notation is `lead`.
If no precedence is provided for notation items that are terms, then they default to precedence `min`.

```lean (keep := false) (show := false)

-- Test for default precedences for notations

/-- Parser max -/
notation "takesMax " e:max => e
/-- Parser lead -/
notation "takesLead " e:lead => e
/-- Parser min -/
notation "takesMin " e:min => e

/-- Take the first one -/
notation e1 " <# " e2 => e1

/-- Take the first one in brackets! -/
notation "<<<<<" e1 " <<# " e2 ">>>>>" => e1

elab "#parse_test " "[" e:term "]"  : command => do
  Lean.logInfoAt e (toString e)
  pure ()

-- Here, takesMax vs takesLead distinguishes the notations

/-- info: («term_<#_» (termTakesMax_ "takesMax" (num "1")) "<#" (num "2")) -/
#check_msgs in
#parse_test [ takesMax 1 <# 2 ]

/-- info: (termTakesLead_ "takesLead" («term_<#_» (num "1") "<#" (num "2"))) -/
#check_msgs in
#parse_test [ takesLead 1 <# 2 ]


-- Here, takesMax vs takesLead does not distinguish the notations because both have precedence `max`

/--
info: (termTakesMax_ "takesMax" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#check_msgs in
#parse_test [ takesMax <<<<< 1 <<# 2 >>>>> ]

/--
info: (termTakesLead_ "takesLead" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#check_msgs in
#parse_test [ takesLead <<<<< 1 <<# 2 >>>>> ]
```

After the required double arrow ({keywordOf Lean.Parser.Command.notation}`=>`), the notation is provided with an expansion.
While operators are always expanded by applying their function to the operator's arguments in order, notations may place their term items in any position in the expansion.
The terms are referred to by name.
Term items may occur any number of times in the expansion.
Because notation expansion is a purely syntactic process that occurs prior to elaboration or code generation, duplicating terms in the expansion may lead to duplicated computation when the resulting term is evaluated, or even duplicated side effects when working in a monad.

::::keepEnv
:::example "Ignored Terms in Notation Expansion"
This notation ignores its first parameter:
```lean
notation (name := ignore) "ignore " _ign:arg e:arg => e
```

The term in the ignored position is discarded, and Lean never attempts to elaborate it, so terms that would otherwise result in errors can be used here:
```lean (name := ignore)
#eval ignore (2 + "whatever") 5
```
```leanOutput ignore
5
```

However, the ignored term must still be syntactically valid:
```syntaxError ignore' (category := command)
#eval ignore (2 +) 5
```
```leanOutput ignore'
<example>:1:17-1:18: unexpected token ')'; expected term
```
:::
::::

::::keepEnv
:::example "Duplicated Terms in Notation Expansion"

The {keywordOf dup}`dup!` notation duplicates its sub-term.

```lean
notation (name := dup) "dup!" t:arg => (t, t)
```

Because the term is duplicated, it can be elaborated separately with different types:
```lean
def e : Nat × Int := dup! (2 + 2)
```

Printing the resulting definition demonstrates that the work of addition will be performed twice:
```lean (name := dup)
#print e
```
```leanOutput dup
def e : Nat × Int :=
(2 + 2, 2 + 2)
```
:::
::::


When the expansion consists of the application of a function defined in the global environment and each term in the notation occurs exactly once, an {tech}[unexpander] is generated.
The new notation will be displayed in {tech}[proof states], error messages, and other output from Lean when matching function application terms otherwise would have been displayed.
As with custom operators, Lean does not track whether the notation was used in the original term; it is used at every opportunity in Lean's output.

# Operators and Notations
%%%
tag := "operators-and-notations"
%%%

Internally, operator declarations are translated into notation declarations.
Term notation items are inserted where the operator would expect arguments, and in the corresponding positions in the expansion.
For prefix and postfix operators, the notation's precedence as well as the precedences of its term items is the operator's declared precedence.
For non-associative infix operators, the notation's precedence is the declared precedence, but both arguments are parsed at a precedence level that is one higher, which prevents successive uses of the notation without parentheses.
Associative infix operators use the operator's precedence for the notation and for one argument, while a precedence that is one level higher is used for the other argument; this prevents successive applications in one direction only.
Left-associative operators use the higher precedence for their right argument, while right-associative operators use the higher precedence for their left argument.
