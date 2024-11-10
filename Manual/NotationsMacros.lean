/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Language.Classes
import Manual.Language.Functions
import Manual.Language.Files
import Manual.Language.InductiveTypes

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

# Custom Operators
%%%
tag := "operators"
%%%

Lean supports custom infix, prefix, and suffix operators.
New operators can be added by any Lean library, and the new operators have equal status to those that are part of the language.
Each new operator is assigned an interpretation as a function, after which uses of the operator are translated into uses of the function.
The operator's translation into a function call is referred to as its {deftech}_expansion_.
If this function is a {tech}[type class] {tech}[method], then the resulting operator can be overloaded by defining instances of the class.

All operators have a {deftech}[precedence].
Operator precedence determines the order of operations for unparenthesized expressions: because multiplication has a higher precedence than addition, {lean}`2 + 3 * 4` is equivalent to {lean}`2 + (3 * 4)`, and {lean}`2 * 3 + 4` is equivalent to {lean}`(2 * 3) + 4`.
Infix operators additionally have an {deftech}[associativity] that determines the meaning of a chain of operators that have the same precedence:

: {deftech}[Left-associative]

  These operators nest to the left.
  Addition is left- associative, so {lean}`2 + 3 + 4 + 5` is equivalent to {lean}`((2 + 3) + 4) + 5`.

: {deftech}[Right-associative]

  These operators nest to the right.
  The product type is right-associative, so {lean}`Nat × String × Unit × Option Int` is equivalent to {lean}`Nat × (String × (Unit × Option Int))`.

: {deftech}[Non-associative]

  Chaining these operators is a syntax error.
  Explicit parenthesization is required.
  Equality is non-associative, so the following is an error:

  ```syntaxError eqs (category := term)
  1 + 2 = 3 = 2 + 1
  ```
  The parser error is:
  ```leanOutput eqs
  <example>:1:10: expected end of input
  ```
::::keepEnv
:::example "Precedence for Prefix and Infix Operators"
```lean (show := false)
axiom A : Prop
axiom B : Prop
example : (¬A ∧ B = (¬A) ∧ B) = (¬A ∧ ((B = ¬A) ∧ B)) := rfl
example : (¬A ∧ B) = ((¬A) ∧ B) := rfl
```

The proposition {lean}`¬A ∧ B` is equivalent to {lean}`(¬A) ∧ B`, because `¬` has a higher precedence than `∧`.
Because `∧` has higher precedence than `=` and is right-associative, {lean}`¬A ∧ B = (¬A) ∧ B` is equivalent to {lean}`¬A ∧ ((B = ¬A) ∧ B)`.
:::
::::

Lean provides commands for defining new operators:
:::syntax command
Non-associative infix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`infix`:
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

Left-associative infix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`infixl`:
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infixl:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

Right-associative infix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`infixr`:
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infixr:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

Prefix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`prefix`:
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind prefix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

Postfix operators are defined using {keywordOf Lean.Parser.Command.mixfix}`postfix`:
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind postfix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```
:::

Each of these commands may be preceded by {tech}[documentation comments] and {tech}[attributes].
The documentation comment is shown when the user hovers their mouse over the operator, and attributes may invoke arbitrary metaprograms, just as for any other declaration.
The attribute {attr}`inherit_doc` causes the documentation of the function that implements the operator to be re-used for the operator itself.

Operators interact with {tech}[section scopes] in the same manner as attributes.
By default, operators are available in any module that transitively imports the one in which they are established, but they may be declared `scoped` or `local` to restrict their availability either to contexts in which the current namespace has been opened or to the current {tech}[section scope], respectively.

Operators require a {ref "precedence"}[precedence] specifier, following a colon.
There is no default precedence to fall back to for custom operators.

Operators may be explicitly named.
This name denotes the extension to Lean's syntax, and is primarily used for metaprogramming.
If no name is explicitly provided, then Lean generates one based on the operator.
The specifics of the assignment of this name should not be relied upon, both because the internal name assignment algorithm may change and because the introduction of similar operators in upstream dependencies may lead to a clash, in which case Lean will modify the assigned name until it is unique.

::::keepEnv
:::example "Assigned Operator Names"
Given this infix operator:
```lean
@[inherit_doc]
infix:90 " ⤴ " => Option.getD
```
the internal name {name}`«term_⤴_»` is assigned to the resulting parser extension.
:::
::::

::::keepEnv
:::example "Provided Operator Names"
Given this infix operator:
```lean
@[inherit_doc]
infix:90 (name := getDOp) " ⤴ " => Option.getD
```
the resulting parser extension is named {name}`getDOp`.
:::
::::

:::TODO
Describe the priority
:::

The actual operator is provided as a string literal.
The new operator must satisfy the following requirements:
 * It must contain at least one character.
 * The first character may not be a single or double quote (`'` or `"`).
 * It may not begin with a backtick (``​`​``) followed by a character that would be a valid prefix of a quoted name.
 * It may not begin with a digit.

The operator string literal may begin or end with a space.
These are not part of the operator's syntax, and their presence does not require spaces around uses of the operator.
However, the presence of spaces cause Lean to insert spaces when showing the operator to the user.
Omitting them causes the operator's arguments to be displayed immediately next to the operator itself.


:::keepEnv
```lean (show := false)
-- Test claim about internal whitespace in preceding paragraph
infix:99 " <<<< >>>> " => Nat.add

/-- info: 67 -/
#guard_msgs in
#eval 12 <<<< >>>> 55

-- Test claim about internal whitespace
infix:99 " <<<<  >>>> " => Nat.mul

/-- info: 660 -/
#guard_msgs in
#eval 12 <<<<  >>>> 55

--- Test negative claims about allowed atoms
/--
error: invalid atom
---
error: invalid syntax node kind 'bogus'
-/
#guard_msgs in
infix:9 (name := bogus) "" => Nat.mul

#guard_msgs in
infix:9 (name := nonbogus) " ` " => Nat.mul

/--
error: invalid atom
---
error: invalid syntax node kind 'bogus'
-/
#guard_msgs in
infix:9 (name := bogus) "`a" => Nat.mul

```
:::

Finally, the operator's meaning is provided, separated from the operator by {keywordOf Lean.Parser.Command.mixfix}`=>`.
This may be any Lean term.
Uses of the operator are desugared into function applications, with the provided term in the function position.
Prefix and postfix operators apply the term to their single argument as an explicit argument.
Infix operators apply the term to the left and right arguments, in that order.
Other than its ability to accept arguments at each call site, there are no specific requirements imposed on the term.
Operators may construct functions, so the term may expect more parameters than the operator.
Implicit and {tech}[instance-implicit] parameters are resolved at each application site, which allows the operator to be defined by a {tech}[type class] {tech}[method].

```lean (show := false) (keep := false)
-- Double-check claims about operators above
prefix:max "blah" => Nat.add
#check (blah 5)
```

If the term consists either of a name from the global environment or of an application of such a name to one or more arguments, then Lean automatically generates an {tech}[unexpander] for the operator.
This means that the operator will be displayed in {tech}[proof states], error messages, and other output from Lean when the function term otherwise would have been displayed.
Lean does not track whether the operator was used in the original term; it is inserted at every opportunity.

:::::keepEnv
::::example "Custom Operators in Lean's Output"
The function {lean}`perhapsFactorial` computes a factorial for a number if it's not too large.
```lean
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * fact n

def perhapsFactorial (n : Nat) : Option Nat :=
  if n < 8 then some (fact n) else none
```

The postfix interrobang operator can be used to represent it.
```lean
postfix:90 "‽" => perhapsFactorial
```

When attempting to prove that {lean}`∀ n, n ≥ 8 → (perhapsFactorial n).isNone`, the initial proof state uses the new operator, even though the theorem as written does not:
```proofState
∀ n, n ≥ 8 → (perhapsFactorial n).isNone := by skip
/--
⊢ ∀ (n : Nat), n ≥ 8 → n‽.isNone = true
-/

```
::::
:::::

# Precedences
%%%
tag := "precedence"
%%%

Infix operators, notations, and other syntactic extensions to Lean make use of explicit {tech}[precedence] annotations.
While precedences in Lean can technically be any natural number, by convention they range from {evalPrec}`min` to {evalPrec}`max`, respectively denoted `min` and `max`.{TODO}[Fix the keywordOf operator and use it here]
Function application has the highest precedence.

:::syntax prec (open := false)
Most operator precedences consist of explicit numbers.
The named precedence levels denote the outer edges of the range, close to the minimum or maximum, and are typically used by more involved syntax extensions.
```grammar
$n:num
```

Precedences may also be denoted as sums or differences of precedences; these are typically used to assign precedences that are relative to one of the named precedences.
```grammar
$p + $p
```
```grammar
$p - $p
```
```grammar
($p)
```

The maximum precedence is used to parse terms that occur in a function position.
Operators should typically not use use this level, because it can interfere with users' expectation that function application binds more tightly than any other operator, but it is useful in more involved syntax extensions to indicate how other constructs interact with function application.
```grammar
max
```

Argument precedence is one less than the maximum precedence.
This level is useful for defining syntax that should be treated as an argument to a function, such as {keywordOf Lean.Parser.Term.fun}`fun` or {keywordOf Lean.Parser.Term.do}`do`.
```grammar
arg
```

Lead precedence is less that argument precedence, and should be used for custom syntax that should not occur as a function argument, such as {keywordOf Lean.Parser.Term.let}`let`.
```grammar
lead
```

The minimum precedence can be used to ensure that an operator binds less tightly than all other operators.
```grammar
min
```
:::

# Notations
%%%
tag := "notations"
%%%

The term {deftech}_notation_ is used in two ways in Lean: it can refer to the general concept of concise ways of writing down ideas, and it is the name of a language feature that allows notations to be conveniently implemented with little code.
Like custom operators, Lean notations allow the grammar of terms to be extended with new forms.
However, notations are more general: the new syntax may freely intermix required keywords or operators with subterms, and they provide more precise control over precedence levels.
Notations may also rearrange their parameters in the resulting subterms, while infix operators provide them to the function term in a fixed order.
Because notations may define operators that use a mix of prefix, infix, and postfix components, they can be called {deftech}_mixfix_ operators.

:::syntax command
Notations are defined using the {keywordOf Lean.Parser.Command.notation}`notation` command.

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind notation$[:$_:prec]? $[(name := $_:ident)]? $[(priority := $_:prio)]? $[$_:notationItem]* => $_:term
```
:::

:::syntax Lean.Parser.Command.notationItem (open := false)
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

:::TODO
What is the priority?
:::

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
#guard_msgs in
#parse_test [ takesMax 1 <# 2 ]

/-- info: (termTakesLead_ "takesLead" («term_<#_» (num "1") "<#" (num "2"))) -/
#guard_msgs in
#parse_test [ takesLead 1 <# 2 ]


-- Here, takesMax vs takesLead does not distinguish the notations because both have precedence `max`

/--
info: (termTakesMax_ "takesMax" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#guard_msgs in
#parse_test [ takesMax <<<<< 1 <<# 2 >>>>> ]

/--
info: (termTakesLead_ "takesLead" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#guard_msgs in
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
<example>:1:17: expected term
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

## Operators and Notations
%%%
tag := "operators-and-notations"
%%%

Internally, operator declarations are translated into notation declarations.
Term notation items are inserted where the operator would expect arguments, and in the corresponding positions in the expansion.
For prefix and postfix operators, the notation's precedence as well as the precedences of its term iters is the operator's declared precedence.
For non-associative infix operators, the notation's precedence is the declared precedence, but both arguments are parsed at a precedence level that is one higher, which prevents successive uses of the notation without parentheses.
Associative infix operators use the operator's precedence for the notation and for one argument, while a precedence that is one level higher is used for the other argument; this prevents successive applications in one direction only.
Left-associative operators use the higher precedence for their right argument, while right-associative operators use the higher precedence for their left argument.

# Defining New Syntax

## Syntax Model

:::TODO
 * {deftech}[atom]
:::

## Syntax Categories and Extensions
%%%
tag := "syntax-categories"
%%%

:::TODO
 * {deftech}_Atoms_ and other kinds of syntax
:::

# Macros
%%%
tag := "macros"
%%%

:::planned 71
 * Definition of {deftech}_macro_
 * `macro_rules`
   * Syntax patterns
   * Backtracking on expansion failure
 * {deftech}[Hygiene] and quotation
 * The `macro` command
:::


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
