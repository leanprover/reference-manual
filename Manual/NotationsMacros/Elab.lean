/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
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

#doc (Manual) "Elaborators" =>

%%%
tag := "elaborators"
%%%

While macros allow Lean to be extended by translating new syntax into existing syntax, {deftech}_elaborators_ allow the new syntax to be processed directly.
Elaborators have access to everything that Lean itself uses to implement each feature of the language.
Defining a new elaborator allows a language extension to be just as powerful as any built-in feature of Lean.

:::paragraph
Elaborators come in two varieties:

 * {deftech}_Command elaborators_ are used to add new commands to Lean.
   Commands are implemented as side effects: they may add new constants to the global environment, extend compile-time tables such as the one that tracks {tech}[instances], they can provide feedback in the form of information, warnings, or errors, and they have full access to the {name}`IO` monad.
   Command elaborators are associated with the {tech (key := "kind")}[syntax kinds] that they can handle.

 * {deftech}_Term elaborators_ are used to implement new terms by translating the syntax into Lean's core type theory.
   They can do everything that command elaborators can do, and they additionally have access to the local context in which the term is being elaborated.
   Term elaborators can look up bound variables, bind new variables, unify two terms, and much more.
   A term elaborator must return a value of type {name}`Lean.Expr`, which is the AST of the core type theory.
:::

This section provides an overview and a few examples of elaborators.
Because Lean's own elaborator uses the same tools, the source code of the elaborator is a good source of further examples.
Just like macros, multiple elaborators may be associated with a syntax kind; they are tried in order, and elaborators may delegate to the next elaborator in the table by throwing the {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` exception.

:::syntax command (title := "Elaboration Rules")

The {keywordOf Lean.Parser.Command.elab_rules}`elab_rules` command takes a sequence of elaboration rules, specified as syntax pattern matches, and adds each as an elaborator.
The rules are attempted in order, before previously-defined elaborators, and later elaborators may add further options.

```grammar
$[$d:docComment]?
$[@[$attrs,*]]?
$_:attrKind elab_rules $[(kind := $k)]? $[: $_]? $[<= $_]?
  $[| `(free{(p:ident"|")?/-- Suitable syntax for {p} -/}) => $e]*
```

:::

Commands, terms, and tactics each maintain a table that maps syntax kinds to elaborators.
The syntax category for which the elaborator should be used is specified after the colon, and must be `term`, `command`, or `tactic`.
The {keywordOf Lean.Parser.Command.elab_rules}`<=` binds the provided identifier to the current expected type in the context in which a term is being elaborated; it may only be used for term elaborators, and if present, then `term` is implied as the syntax category.


:::syntax attr (title := "Elaborator Attribute")
Elaborators can be directly associated with syntax kinds by applying the appropriate attributes.
Each takes the name of a syntax kind and associates the definition with the kind.

```grammar
term_elab $_
```
```grammar
command_elab $_
```
```grammar
tactic $_
```
:::

# Command Elaborators

:::::leanSection
```lean -show
open Lean Elab Command
```
A command elaborator has type {name}`CommandElab`, which is an abbreviation for {lean}`Syntax → CommandElabM Unit`.
Command elaborators may be implicitly defined using {keywordOf Lean.Parser.Command.elab_rules}`elab_rules`, or explicitly by defining a function and applying the {attr}`command_elab` attribute.

:::example "Querying the Environment"
```imports
import Lean.Elab
```
```lean -show
open Lean
```

A command elaborator can be used to query the environment to discover how many constants have a given name.
This example uses {name}`getEnv` from the {name}`MonadEnv` class to get the current environment.
{name}`Environment.constants` yields a mapping from names to information about them (e.g. their type and whether they are a definition, {tech}[inductive type] declaration, etc).
{name}`logInfoAt` allows informational output to be associated with syntax from the original program, and a {tech}[token antiquotation] is used to implement the Lean convention that output from interactive commands is associated with their keyword.

```lean
syntax "#count_constants " ident : command

elab_rules : command
  | `(#count_constants%$tok $x) => do
    let pattern := x.getId
    let env ← getEnv
    let mut count := 0
    for (y, _) in env.constants do
      if pattern.isSuffixOf y then
        count := count + 1
    logInfoAt tok m!"Found {count} instances of '{pattern}'"
```

```lean (name := run)
def interestingName := 55
def NS.interestingName := "Another one"

#count_constants interestingName
```

```leanOutput run
Found 2 instances of 'interestingName'
```

:::

:::::

# Term Elaborators

:::::leanSection
```lean -show
open Lean Elab Term
```
A term elaborator has type {name}`TermElab`, which is an abbreviation for {lean}`Syntax → Option Expr → TermElabM Expr`.
The optional {lean}`Expr` parameter is the type expected for the term being elaborated, which is `none` if no type is yet known.
Like command elaborators, term elaborators may be implicitly defined using {keywordOf Lean.Parser.Command.elab_rules}`elab_rules`, or explicitly by defining a function and applying the {attr}`term_elab` attribute.

:::example "Avoiding a Type"
```imports
import Lean.Elab
```
```lean -show
open Lean Elab Term
```

This examples demonstrates an elaborator for syntax that is the opposite of a type ascription.
The provided term may have any type _other_ than the one indicated, and metavariables are solved pessimistically.
In this example, {name}`elabType` invokes the term elaborator and then ensures that the resulting term is a type.
{name}`Meta.inferType` infers a type for a term, and {name}`Meta.isDefEq` attempts to make two terms {tech (key := "definitional equality")}[definitionally equal] by unification, returning {lean}`true` if it succeeds.

```lean
syntax (name := notType) "(" term  " !: " term ")" : term

@[term_elab notType]
def elabNotType : TermElab := fun stx _ => do
  let `(($tm:term !: $ty:term)) := stx
    | throwUnsupportedSyntax
  let unexpected ← elabType ty
  let e ← elabTerm tm none
  let eTy ← Meta.inferType e
  if (← Meta.isDefEq eTy unexpected) then
    throwErrorAt tm m!"Got unwanted type {eTy}"
  else pure e
```

If the type position does not contain a type, then `elabType` throws an error:
```lean (name := notType) +error
#eval ([1, 2, 3] !: "not a type")
```
```leanOutput notType
type expected, got
  ("not a type" : String)
```

If the term's type is definitely not equal to the provided type, then elaboration succeeds:
```lean (name := ok)
#eval ([1, 2, 3] !: String)
```
```leanOutput ok
[1, 2, 3]
```

If the types match, an error is thrown:
```lean (name := nope) +error
#eval (5 !: Nat)
```
```leanOutput nope
Got unwanted type Nat
```

The type equality check may fill in missing information, so {lean  (type := "String")}`sorry` (which may have any type) is also rejected:
```lean (name := unif) +error
#eval (sorry !: String)
```
```leanOutput unif
Got unwanted type String
```
:::

:::example "Using Any Local Variable"
```imports
import Lean.Elab
```
```lean -show
open Lean
```

Term elaborators have access to the expected type and to the local context.
This can be used to create a term analogue of the {tactic}`assumption` tactic.

The first step is to access the local context using {name}`getLocalHyps`.
It returns the context with the outermost bindings on the left, so it is traversed in reverse order.
For each local assumption, a type is inferred with {name}`Meta.inferType`.
If it can be equal to the expected type, then the assumption is returned; if no assumption is suitable, then an error is produced.

```lean
syntax "anything!" : term

elab_rules <= expected
  | `(anything!) => do
    let hyps ← getLocalHyps
    for h in hyps.reverse do
      let t ← Meta.inferType h
      if (← Meta.isDefEq t expected) then return h

    throwError m!"No assumption in {hyps} has type {expected}"
```

The new syntax finds the function's bound variable:
```lean (name := app)
#eval (fun (n : Nat) => 2 + anything!) 5
```
```leanOutput app
7
```

It chooses the most recent suitable variable, as desired:
```lean (name := lets)
#eval
  let x := "x"
  let y := "y"
  "It was " ++ y
```
```leanOutput lets
"It was y"
```

When no assumption is suitable, it returns an error that describes the attempt:
```lean (name := noFun) +error
#eval
  let x := Nat.zero
  let y := "hello"
  fun (f : Nat → Nat) =>
    (anything! : Int → Int)
```
```leanOutput noFun
No assumption in [x, y, f] has type Int → Int
```

Because it uses unification, the natural number literal is chosen here, because numeric literals may have any type with an {name}`OfNat` instance.
Unfortunately, there is no {name}`OfNat` instance for functions, so instance synthesis later fails.
```lean (name := poly) +error
#eval
  let x := 5
  let y := "hello"
  (anything! : Int → Int)
```
```leanOutput poly
failed to synthesize
  OfNat (Int → Int) 5
numerals are polymorphic in Lean, but the numeral `5` cannot be used in a context where the expected type is
  Int → Int
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

:::

:::::

# Custom Tactics

Custom tactics are described in the {ref "custom-tactics"}[section on tactics].
