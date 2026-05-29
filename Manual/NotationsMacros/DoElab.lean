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
open Verso.Genre.Manual hiding seeAlso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Illuminate in
/--
Illustrates how the continuation captures the remainder of a `do`-block: each statement becomes
a box, and elaborating the first statement is handed a continuation that binds its result to a
name and runs the rest of the block.
-/
def continuationDiagram : Diagram SVG :=
  let stmt1 := code "stmt₁"
  let stmt2 := code "stmt₂"
  let line1 :=
    Diagram.hsep 8 [keyword "do", box first stmt1, code ";", box rest stmt2] (align := .center)
  let xName := code "x" |>.namedWithAnchors `x
  let cont :=
    Diagram.hsep 8 [code ">>=", keyword "fun", xName, code "=>", box rest stmt2.ghost] (align := .center)
  let contBraced := Diagram.braceBelow cont (label "the continuation")
  let line2 :=
    Diagram.hsep 8 [box first stmt1.ghost, contBraced] (align := .top)
  Diagram.vsep 44 [line1, line2]
    |>.connect
      { point := `x.north, shift := ⟨44, 28⟩ }
      { point := `x.north, shift := ⟨0, 3⟩ }
      (arrowhead := some { type := .stealth })
      (label := some { label := label "the result name", upright := true })
where
  code (s : String) : Diagram SVG :=
    Diagram.text s { fontFamily := "monospace", fontSize := 16 }
  keyword (s : String) : Diagram SVG :=
    Diagram.text s { fontFamily := "monospace", fontSize := 16, color := Color.rgb 137 89 168 }
  label (s : String) : Diagram SVG :=
    Diagram.text s { fontFamily := "sans-serif", fontSize := 12 }
  first : Color := Color.rgb 207 226 255
  rest : Color := Color.rgb 255 233 191
  box (fill : Color) (d : Diagram SVG) : Diagram SVG :=
    d.filledFrame (fill := fill) (stroke := { color := Color.black, width := 1 })
      (padding := 6) (cornerRadius := 5)

#doc (Manual) "Extending `do`-Notation" =>

%%%
tag := "do-elab"
%%%

Macros and elaborators can be used to extend Lean with new commands and terms.
In addition, `do`-notation can be extended.
Extensions to `do`-notation define new kinds of `do`-elements.
Macros translate the new `do`-elements into previously-existing `do`-elements, while elaborators have access to more information and can produce arbitrary terms in Lean's type theory.


This chapter describes how to extend `do`-notation.
These features are controlled by the option {option}`backward.do.legacy`:

{optionDocs backward.do.legacy}


TODO xref description of do and desugaring

# Elaboration Overview

The elaborator processes the syntax one element at a time.

doElem vs doSeq

Concepts: effect lifting, mutables, continuation

# Macros in `do`-Notation

Macro expansion occurs during the elaboration of `do`-elements.
There is no fundamental difference between `do`-element macros and term or command macros; they are distinguished by being defined for syntax that's part of the `doElem` syntax category.

::::example "Multi-Way `if`"
```lean -show
open Lean
```
:::paragraph
As an alternative to a nested sequence of `if`-terms, this “multi-way `if`” places each condition at the same syntactic level:

```lean
syntax (name := multiIfTerm)
  "if " withPosition(
    (colGe atomic("|" (atomic(ident " : "))? term) " => " term)+
    (colGe "|" " else " " => " term)?
  ) : term
```
```lean
macro_rules
  | `(if
      $[| $[$hs?:ident :]? $gs:term => $bs:term]*
      | else => $e:term) => do
      let mut out := e
      for h? in hs?.reverse, g in gs.reverse, b in bs.reverse do
        out ← match h? with
          | some h => `(if $h:ident : $g then $b else $out)
          | none   => `(if $g then $b else $out)
      return out
  | `(if $[| $[$_:ident :]? $_:term => $_:term]*) =>
      Macro.throwError "a multi-way `if` needs a final `_` fallback"
```
:::

This macro can be adapted to be a `do`-element by placing it in the `doElem` syntax category and replacing each arm of the do with a `doSeq` instead of a `term`:

TODO def and demo

::::

## Limitations

When an extension can be implemented as a macro, it's usually best to do so.
Macros are much simpler to maintain, and they inherit bug fixes from the implementation of the syntax that they expand to.
However, macros cannot implement all possible extensions:
 * They cannot access information about the set of mutable variables, nor can they override it.
 * They cannot control the scope of mutable variables without leaving the current `do`-block.
 * TODO after writing, fill this out

::::example "Freezing Mutable Variables with a Macro"
Within a `do` block, new `let` bindings may not shadow existing `let mut` bindings.
However, many mutable variables are not modified after they are initialized.
It might be convenient to indicate this fact by removing their mutability.


There is no existing way to replace a mutable variable with an immutable one, so a macro cannot be a simple `do`-element.
However, it can introduce a scope in which the mutable variable is immutable by expanding to a function call:
```lean
macro "freeze " x:ident " in " body:doSeq : doElem =>
  `(doElem| (fun $x => do $body) $x)
```


While it may seem promising, this macro-based solution has severe drawbacks.
First off, the body of the resulting function constitutes a new `do`-block.
This means that mutable variables in the surrounding block cannot be modified:
```lean +error (name := noMutFreeze)
#eval Id.run do
  let mut x : Nat := 0
  x := x + 1
  let mut y := 0
  freeze x in
    y := 2 * x
  return y
```
```leanOutput noMutFreeze
`y` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intend to mutate but define `y`, consider using `let y` instead
```
Additionally, early return returns from the inner `do`, rather than the surrounding one, as indicated by the fact that it's expected to return a {lean}`Unit`:
```lean +error (name := noInnerReturn)
#eval Id.run do
  let mut x : Nat := 0
  x := x + 1
  let mut y := 0
  freeze x in
    return x
  return y
```
```leanOutput noInnerReturn
Application type mismatch: The argument
  x
has type
  Nat
but is expected to have type
  PUnit
in the application
  pure x
```
::::

# Elaboration


Elaboration of `do`-elements occurs in the {name Lean.Elab.Do.DoElabM}`DoElabM` monad.
This monad is a wrapper around {name Lean.Elab.Term.TermElabM}`TermElabM` that provides one extra {ref "reader"}[reader] value: a `do`-elaboration context.
The elaborators also received an additional argument: a description of the elaboration {deftech}_continuation_.
The continuation represents the remainder of the `do`-block, after the current element; it includes both a {name Lean.Elab.Do.DoElabM}`DoElabM` action that will elaborate the remainder of the block and the name by which that term will refer to the result of the current elaboration step.
When elaborating the first statement in `do stmt₁; stmt₂`, the continuation captures both the bind operator that sequences it with the rest of the block and the name `x` that stands for its result, as shown in {ref "do-continuation-fig"}[the following figure].

:::figure "The Continuation in `do`-Elaboration" (tag := "do-continuation-fig")
```diagram
continuationDiagram
```
:::



{docstring Lean.Elab.Do.Context +allowMissing}

Elaborators are associated with syntax kinds using the {attr}`doElem_elab` attribute.

:::syntax attr (title := "Do Element Elaborators")
```grammar
doElem_elab
```
{includeDocstring Lean.Elab.Do.doElemElabAttribute}
:::

{docstring Lean.Elab.Do.DoElemCont}

{docstring Lean.Elab.Do.DoElemContKind +allowMissing}

:::syntax attr (title := "Do Element Elaborators")
```grammar
doElem_control_info
```
{includeDocstring Lean.Elab.Do.controlInfoElemAttribute}
:::


## The Context

The context provides access to information about the `do`-block in which the new element is being elaborated.
In addition to the types involved, such as the the block's monad and return type, it provides information about the block's mutable variables as well as instructions for returning early and implementing `break` and `continue` when in a loop.



::::example "Tracing Mutable Variables"
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
The new syntax `dbg_mut` traces the current values of all mutable variables.

```lean
syntax (name := dbgMut) "dbg_mut" : doElem

@[doElem_elab dbgMut] def elabDbgMut : DoElab := fun _stx cont => do
  let ctx ← readThe Do.Context
  let parts : Array Term ← ctx.mutVars.mapM fun (x : Ident) => do
    let nameLit := x.getId.simpMacroScopes.toString
    `(term| s!"{$(quote nameLit)} = {repr $x}")
  let msg ← `(term| String.intercalate ", " [$parts,*])
  elabDoElem (← `(doElem| dbg_trace $msg)) cont

@[doElem_control_info dbgMut]
def x : ControlInfoHandler := fun _ => do return .pure
```

```lean (name := mutDbg)
#eval show IO Unit from do
  let mut x := 1
  let mut y := 1
  for _ in [0...5] do
    let z := x
    dbg_mut
    y := x + y
    x := z
```
```leanOutput mutDbg
x = 1, y = 1
```
::::

## Continuations

## Lifting Effects

## API Reference
