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

#doc (Manual) "Custom Operators" =>
%%%
tag := "operators"
%%%

Lean supports custom infix, prefix, and postfix operators.
New operators can be added by any Lean library, and the new operators have equal status to those that are part of the language.
Each new operator is assigned an interpretation as a function, after which uses of the operator are translated into uses of the function.
The operator's translation into a function call is referred to as its {deftech}_expansion_.
If this function is a {tech}[type class] {tech}[method], then the resulting operator can be overloaded by defining instances of the class.

All operators have a {deftech}_precedence_.
Operator precedence determines the order of operations for unparenthesized expressions: because multiplication has a higher precedence than addition, {lean}`2 + 3 * 4` is equivalent to {lean}`2 + (3 * 4)`, and {lean}`2 * 3 + 4` is equivalent to {lean}`(2 * 3) + 4`.
Infix operators additionally have an {deftech}_associativity_ that determines the meaning of a chain of operators that have the same precedence:

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
  <example>:1:10-1:11: expected end of input
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
:::syntax command (title := "Operator Declarations")
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

Custom operators require a {ref "precedence"}[precedence] specifier, following a colon.
There is no default precedence to fall back to for custom operators.

Operators may be explicitly named.
This name denotes the extension to Lean's syntax, and is primarily used for metaprogramming.
If no name is explicitly provided, then Lean generates one based on the operator.
The specifics of the assignment of this name should not be relied upon, both because the internal name assignment algorithm may change and because the introduction of similar operators in upstream dependencies may lead to a clash, in which case Lean will modify the assigned name until it is unique.

::::keepEnv
:::example "Assigned Operator Names"
Given this infix operator:
```lean
infix:90 " ⤴ " => Option.getD
```
the internal name {name}`«term_⤴_»` is assigned to the resulting parser extension.
:::
::::

::::keepEnv
:::example "Provided Operator Names"
Given this infix operator:
```lean
infix:90 (name := getDOp) " ⤴ " => Option.getD
```
the resulting parser extension is named {name}`getDOp`.
:::
::::

::::keepEnv
:::example "Inheriting Documentation"
Given this infix operator:
```lean
@[inherit_doc]
infix:90 " ⤴ " => Option.getD
```
the resulting parser extension has the same documentation as {name}`Option.getD`.
:::
::::



When multiple operators are defined that share the same syntax, Lean's parser attempts all of them.
If more than one succeed, the one that used the most input is selected—this is called the {deftech}_local longest-match rule_.
In some cases, parsing multiple operators may succeed, all of them covering the same range of the input.
In these cases, the operator's {tech}[priority] is used to select the appropriate result.
Finally, if multiple operators with the same priority tie for the longest match, the parser saves all of the results, and the elaborator attempts each in turn, failing if elaboration does not succeed on exactly one of them.

:::::keepEnv

::::example "Ambiguous Operators and Priorities"

:::keepEnv
Defining an alternative implementation of `+` as {lean}`Or` requires only an infix operator declaration.
```lean
infix:65  " + " => Or
```

With this declaration, Lean attempts to elaborate addition both using the built-in syntax for {name}`HAdd.hAdd` and the new syntax for {lean}`Or`:
```lean (name := trueOrFalse1)
#check True + False
```
```leanOutput trueOrFalse1
True + False : Prop
```
```lean (name := twoPlusTwo1)
#check 2 + 2
```
```leanOutput twoPlusTwo1
2 + 2 : Nat
```

However, because the new operator is not associative, the {tech}[local longest-match rule] means that only {name}`HAdd.hAdd` applies to an unparenthesized three-argument version:
```lean (error := true) (name := trueOrFalseOrTrue1)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue1
failed to synthesize
  HAdd Prop Prop ?m.38

Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::

:::keepEnv
If the infix operator is declared with high priority, then Lean does not try the built-in {name}`HAdd.hAdd` operator in ambiguous cases:
```lean
infix:65 (priority := high)  " + " => Or
```

```lean (name := trueOrFalse2)
#check True + False
```
```leanOutput trueOrFalse2
True + False : Prop
```
```lean (name := twoPlusTwo2) (error := true)
#check 2 + 2
```
```leanOutput twoPlusTwo2
failed to synthesize
  OfNat Prop 2
numerals are polymorphic in Lean, but the numeral `2` cannot be used in a context where the expected type is
  Prop
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

The new operator is not associative, so the {tech}[local longest-match rule] means that only {name}`HAdd.hAdd` applies to the three-argument version:
```lean (error := true) (name := trueOrFalseOrTrue2)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue2
failed to synthesize
  HAdd Prop Prop ?m.20

Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::

::::
:::::


The actual operator is provided as a string literal.
The new operator must satisfy the following requirements:
 * It must contain at least one character.
 * The first character may not be a single or double quote (`'` or `"`), unless the operator is `''`.
 * It may not begin with a backtick (`` ` ``) followed by a character that would be a valid prefix of a quoted name.
 * It may not begin with a digit.
 * It may not include internal whitespace.

The operator string literal may begin or end with a space.
These are not part of the operator's syntax, and their presence does not require spaces around uses of the operator.
However, the presence of spaces cause Lean to insert spaces when showing the operator to the user.
Omitting them causes the operator's arguments to be displayed immediately next to the operator itself.


:::keepEnv
```lean (show := false)
-- Test claim about internal whitespace in preceding paragraph
/--
error: invalid atom
---
error: invalid syntax node kind '«term_<<<<_>>>>_»'
-/
#check_msgs in
infix:99 " <<<< >>>> " => Nat.add


--- Test further claims about allowed atoms
/--
error: invalid atom
---
error: invalid syntax node kind 'bogus'
-/
#check_msgs in
infix:9 (name := bogus) "" => Nat.mul


/--
error: invalid atom
---
error: invalid syntax node kind 'alsobogus'
-/
#check_msgs in
infix:9 (name := alsobogus) " ` " => Nat.mul

-- this one's OK
#check_msgs in
infix:9 (name := nonbogus) " `` " => Nat.mul

/--
error: invalid atom
---
error: invalid syntax node kind 'bogus'
-/
#check_msgs in
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
