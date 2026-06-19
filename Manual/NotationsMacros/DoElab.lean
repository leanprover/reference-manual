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

open Lean.Parser.Term (doSeq)

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean

#doc (Manual) "Extending `do`-Notation" =>

%%%
tag := "do-elab"
%%%

Macros and elaborators can be used to extend Lean with new commands and terms.
In addition, {keywordOf Lean.Parser.Term.do}`do`-notation can be extended.
Extensions to {keywordOf Lean.Parser.Term.do}`do`-notation define new kinds of {keywordOf Lean.Parser.Term.do}`do`-elements.
Macros translate the new {keywordOf Lean.Parser.Term.do}`do`-elements into previously existing {keywordOf Lean.Parser.Term.do}`do`-elements, while elaborators have access to more information and can produce arbitrary terms in Lean's type theory.

:::paragraph
This chapter describes the extension mechanisms that are available for {keywordOf Lean.Parser.Term.do}`do`-notation.
Extensible {keywordOf Lean.Parser.Term.do}`do`-notation was introduced in Lean version 4.29.0; prior to this release, it was not extensible.
The extensible {keywordOf Lean.Parser.Term.do}`do` elaborator is controlled by the option {option}`backward.do.legacy`:

{optionDocs backward.do.legacy}

When {option}`backward.do.legacy` is `false`, the extensible elaborator is enabled.
Custom {keywordOf Lean.Parser.Term.do}`do`-element elaborators extend the desugaring described in {ref "do-notation"}[the section on syntax for monads].
:::

# Elaboration Overview

The {tech}[syntax kind] `doElem` represents individual {tech}[`do`-elements].
A sequence of these elements is represented by the syntax kind {name}`doSeq`, which makes up the body of a {keywordOf Lean.Parser.Term.do}`do`-block.
The elaborator for {keywordOf Lean.Parser.Term.do}`do` invokes a specialized elaboration framework on the {name}`doSeq` in its body, elaborating each `doElem` in turn.
This specialized framework allows each element in the sequence to modify the elaboration of subsequent elements, as well as to track information such as enclosing loops (for {keywordOf Lean.Parser.Term.doBreak}`break` and {keywordOf Lean.Parser.Term.doContinue}`continue`), the way to escape via {keywordOf Lean.Parser.Term.doReturn}`return`, and the set of mutable variables.

Elaboration of {keywordOf Lean.Parser.Term.do}`do`-elements is very similar to that of terms.
First, if the syntax in question is a {tech}[macro], then it is expanded.
This is repeated until the result of macro expansion is no longer a macro.
Next, an internal table is consulted to find the elaboration procedure associated with the {keywordOf Lean.Parser.Term.do}`do`-element's syntax kind.
This table is separate from the table of term elaborators, because {keywordOf Lean.Parser.Term.do}`do`-element elaborators have a different type.
If a {keywordOf Lean.Parser.Term.do}`do`-element consists only of a term, then the Lean parser wraps it in the syntax kind {name Lean.Parser.Term.doExpr}`doExpr`; its elaborator invokes the term elaborator, ensuring that the term has the correct type for the {keywordOf Lean.Parser.Term.do}`do`-block.

# Macros in `do`-Notation

Macro expansion occurs during the elaboration of {keywordOf Lean.Parser.Term.do}`do`-elements.
There is no fundamental difference between {keywordOf Lean.Parser.Term.do}`do`-element macros and term or command macros; they are distinguished by being defined for syntax that is part of the `doElem` syntax category.

::::example "Multi-Way `if`"
```imports -show
import Lean.Elab
```
```lean -show
open Lean
open Lean.Parser.Term (doSeq)
```
As an alternative to a nested sequence of {keywordOf Lean.Parser.Term.doIf}`if`-terms, this “multi-way {keywordOf Lean.Parser.Term.doIf}`if`” places each condition at the same syntactic level:
```lean
syntax (name := multiIfTerm)
  "if " withPosition(
    (colGe atomic("|" (atomic(ident " : "))? term) " => " term)+
    colGe "|" " else " " => " term
  ) : term
```
It is {ref "syntax-indentation"}[indentation-sensitive].
It can be implemented as a recursive macro that emits the expected nested {keywordOf Lean.Parser.Term.if}`if`:
```lean
def mkTermIf (h? : Option Ident) (g b e : Term) : MacroM Term :=
  match h? with
  | some h => `(if $h:ident : $g then $b else $e)
  | none => `(if $g then $b else $e)

macro_rules
  | `(if | $[$h?:ident :]? $g:term => $b:term | else => $e:term) =>
      mkTermIf h? g b e
  | `(if | $[$h?:ident :]? $g:term => $b:term
         | $[$h2?:ident :]? $g2:term => $b2:term
         $[| $[$hs?:ident :]? $gs:term => $bs:term]*
         | else => $e:term) => do
      mkTermIf h? g b
        (← `(if | $[$h2?:ident :]? $g2 => $b2
                $[| $[$hs?:ident :]? $gs => $bs]*
                | else => $e))
```

It can be used like any other term:
```lean (name := multiDemo)
#eval
  let sign : Int → String := fun n =>
    if
      | n < 0 => "neg"
      | n = 0 => "zero"
      | else => "pos"
  (sign (-2), sign 0, sign 5)
```
```leanOutput multiDemo
("neg", "zero", "pos")
```

This macro can be adapted to be a {keywordOf Lean.Parser.Term.do}`do`-element by placing it in the `doElem` syntax category and replacing each arm of the multi-way {keywordOf Lean.Parser.Term.doIf}`if` with a {name}`doSeq` instead of a {name}`Term`.
The syntax definition is almost the same; however, the {keywordOf Lean.Parser.Term.doIf}`else` branch is optional:
```lean
syntax (name := multiIf)
  "if " withPosition(
    (colGe atomic("|" (atomic(ident " : "))? term) " => " doSeq)+
    (colGe "|" " else " " => " doSeq)?
  ) : doElem
```
Likewise, a helper function to attach the optional condition hypothesis name to {keywordOf Lean.Parser.Term.doIf}`if` is useful:
```lean
def mkDoIf (h? : Option Ident) (g : Term) (b : TSyntax ``doSeq)
    (els? : Option (TSyntax ``doSeq)) : MacroM (TSyntax `doElem) :=
  match h? with
  | some h =>
    `(doElem| if $h : $g then $b $[else $els?]?)
  | none =>
    `(doElem| if $g then $b $[else $els?]?)
```
The implementation as a recursive macro is also nearly the same:
```lean
macro_rules
  | `(doElem| if | $[$h?:ident :]? $g:term => $b:doSeq
                   $[| else => $e:doSeq]?) =>
      mkDoIf h? g b e
  | `(doElem| if | $[$h?:ident :]? $g:term => $b:doSeq
                 | $[$h2?:ident :]? $g2:term => $b2:doSeq
                 $[| $[$hs?:ident :]? $gs:term => $bs:doSeq]*
                 $[| else => $e:doSeq]?) => do
      mkDoIf h? g b <| some
        (← `(doSeq| if | $[$h2?:ident :]? $g2 => $b2
                       $[| $[$hs?:ident :]? $gs => $bs]*
                       $[| else => $e]?))
```

It can be used in {keywordOf Lean.Parser.Term.do}`do`:
```lean
def getEven : IO { n : Nat // n % 2 = 0 ∨ n % 3 = 0} := do
  let n ← (← IO.getStdin).getLine
  let some n := n.toNat?
    | throw <| IO.userError s!"Not a Nat: {n}"
  if
    | h : n % 2 = 0 =>
      IO.println s!"{n} is even."
      return ⟨n, .inl h⟩
    | h : n % 3 = 0 =>
      IO.println s!"{n} is divisible by 3."
      return ⟨n, .inr h⟩
    | else =>
      throw <| IO.userError s!"Invalid input {n}"
```
::::

## Limitations

:::paragraph
When an extension can be implemented as a macro, it is usually best to do so.
Macros are much simpler to maintain, and they inherit bug fixes from the implementation of the syntax that they expand to.
However, macros cannot implement all possible extensions:
 * They cannot access information about the set of mutable variables, nor can they override it.
 * They cannot implement novel control structures that are not expressible in terms of built-in control structures.
 * They cannot place a {keywordOf Lean.Parser.Term.do}`do`-sequence into some new context (such as underneath a binder) while keeping it as part of the enclosing {keywordOf Lean.Parser.Term.do}`do`-block for the purposes of early return and mutable variables.

In these cases, it may be necessary to define an elaborator.
:::

::::example "Freezing Mutable Variables with a Macro"
Within a {keywordOf Lean.Parser.Term.do}`do` block, new {keywordOf Lean.Parser.Term.doLet}`let` bindings may not shadow existing {keywordOf Lean.Parser.Term.doLet}`let mut` bindings.
However, many mutable variables are not modified after they are initialized.
It might be convenient to indicate this fact by removing their mutability.

There is no existing way to replace a mutable variable with an immutable one, so this feature can't be implemented with a macro that expands to an existing {keywordOf Lean.Parser.Term.do}`do`-element which makes the variable immutable for the remainder of the block.
However, the operator can be structured so that it introduces a scope in which the mutable variable is immutable by expanding to a function call:
```lean
macro "freeze " x:ident " in " body:doSeq : doElem =>
  `(doElem| (fun $x => do $body) $x)
```


While it may seem promising, this macro-based solution has severe drawbacks.
First, the body of the resulting function constitutes a new {keywordOf Lean.Parser.Term.do}`do`-block.
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
Variable `y` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `y`, consider using `let y` instead
```
Additionally, an early {keywordOf Lean.Parser.Term.doReturn}`return` exits the inner {keywordOf Lean.Parser.Term.do}`do`, rather than the surrounding one, as indicated by the fact that it is expected to return a {lean}`Unit` (in this case, the universe-polymorphic {name}`PUnit`):
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
Type mismatch
  x
has type
  Nat
but is expected to have type
  PUnit
```
::::

# Elaboration


Elaboration of {keywordOf Lean.Parser.Term.do}`do`-elements occurs in the {name Lean.Elab.Do.DoElabM}`DoElabM` monad.
This monad is a wrapper around {name Lean.Elab.Term.TermElabM}`TermElabM` that provides one extra {ref "reader-monad"}[reader] value: a {keywordOf Lean.Parser.Term.do}`do`-elaboration context.
The elaborators also receive an additional argument: a description of the elaboration {deftech}_continuation_.
The continuation represents the remainder of the {keywordOf Lean.Parser.Term.do}`do`-block, after the current element; it includes both a {name Lean.Elab.Do.DoElabM}`DoElabM` action that will elaborate the remainder of the block and the name by which that term will refer to the result of the current elaboration step.
Unlike term elaborators, which return the elaborated term to a surrounding elaboration context, {keywordOf Lean.Parser.Term.do}`do`-element elaborators invoke the provided continuation to arrange for the elaboration of the rest of the {keywordOf Lean.Parser.Term.do}`do`-block.


{docstring Lean.Elab.Do.Context +allowMissing}

{docstring Lean.Elab.Do.MonadInfo +allowMissing}

{docstring Lean.Elab.Do.CodeLiveness}

To avoid circularity in the implementation, the {name Lean.Elab.Do.Context.contInfo}`Context.contInfo` and {name Lean.Elab.Do.Context.ops}`Context.ops` fields are references that are filled in after construction.
Use {name Lean.Elab.Do.ContInfoRef.toContInfo}`ContInfoRef.toContInfo` and {name Lean.Elab.Do.DoOpsRef.toDoOps}`DoOpsRef.toDoOps` to recover the underlying data:

{docstring Lean.Elab.Do.ContInfoRef.toContInfo +allowMissing}

{docstring Lean.Elab.Do.ContInfo +allowMissing}

{docstring Lean.Elab.Do.DoOpsRef.toDoOps +allowMissing}

{docstring Lean.Elab.Do.DoOps +allowMissing}

Elaborators are associated with syntax kinds using the {attr}`doElem_elab` attribute.
They should have type {name Lean.Elab.Do.DoElab}`DoElab`.
In addition to an elaborator, each custom {keywordOf Lean.Parser.Term.do}`do`-element that's implemented via an elaborator must be provided with {ref "do-elab-control-info"}[control information].

{docstring Lean.Elab.Do.DoElab}

:::syntax attr (title := "Do Element Elaborators")
```grammar
doElem_elab
```
{includeDocstring Lean.Elab.Do.doElemElabAttribute}
:::

Additionally, {keywordOf Lean.Parser.Command.«elab_rules»}`elab_rules` can be used to simultaneously define an elaborator and associate it with syntax.
Just as `elab_rules : term <= ty` binds the expected type to `ty`, `elab_rules : doElem <= dec` binds the continuation to `dec`.

Just as term elaborators may recursively invoke elaboration on their sub-terms by calling functions such as {name Lean.Elab.Term.elabTerm}`elabTerm`, {keywordOf Lean.Parser.Term.do}`do`-element elaborators may elaborate nested {keywordOf Lean.Parser.Term.do}`do`-elements or sequences of {keywordOf Lean.Parser.Term.do}`do`-elements.
To elaborate a single {keywordOf Lean.Parser.Term.do}`do`-element, call {name Lean.Elab.Do.elabDoElem}`elabDoElem`.
To elaborate a non-empty array of {keywordOf Lean.Parser.Term.do}`do`-elements, call {name Lean.Elab.Do.elabDoElems1}`elabDoElems1`.
To elaborate a sequence of {keywordOf Lean.Parser.Term.do}`do`-elements, call {name Lean.Elab.Do.elabDoSeq}`elabDoSeq`.

{docstring Lean.Elab.Do.elabDoElem +allowMissing}

{docstring Lean.Elab.Do.elabDoSeq +allowMissing}

{docstring Lean.Elab.Do.elabDoElems1 +allowMissing}

## Monad Operations

The elaboration framework provides several helpers that make it more convenient and efficient to construct applications of the current monad and its operations.

{docstring Lean.Elab.Do.mkMonadApp}

{docstring Lean.Elab.Do.mkPureApp}

{docstring Lean.Elab.Do.mkBindApp}

{docstring Lean.Elab.Do.mkPUnitUnit}

## Continuations

A {keywordOf Lean.Parser.Term.do}`do`-elaboration continuation consists of an elaborator that is waiting for the result of the present element together with metadata such as the type that this result is expected to have.

{docstring Lean.Elab.Do.DoElemCont}

{docstring Lean.Elab.Do.DoElemContKind +allowMissing}

Many elaborators require that the continuation is expecting a particular type for its result.
It is very common, for example, for an elaborator to result in {name}`Unit` if it returns no result.
Checking the type at an earlier stage can result in better error messages:

{docstring Lean.Elab.Do.DoElemCont.ensureUnit}

{docstring Lean.Elab.Do.DoElemCont.ensureUnitAt}

{docstring Lean.Elab.Do.DoElemCont.ensureHasTypeAt}

Invoking a continuation consists of providing it with the result of the current {keywordOf Lean.Parser.Term.do}`do`-element.
There are three primary ways of doing this.
{name Lean.Elab.Do.DoElemCont.continueWithUnit}`DoElemCont.continueWithUnit` ensures that the continuation is expecting {name}`Unit` and then invokes it.
{name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode` invokes the continuation in a context that asserts that the code is unreachable, generally causing the continuation to generate no code and also warning users if there is code present.
{name Lean.Elab.Do.DoElemCont.mkBindUnlessPure}`DoElemCont.mkBindUnlessPure` is responsible for the standard desugaring of {keywordOf Lean.Parser.Term.do}`do`-notation into applications of {name}`bind`; it is used to invoke a continuation after elaborating a {keywordOf Lean.Parser.Term.do}`do`-element that consists of a term with a monadic type, and it contains an optimization that replaces a {name}`bind` around a {name}`pure` with a {keywordOf Lean.Parser.Term.«let»}`let`-binding.

{docstring Lean.Elab.Do.DoElemCont.continueWithUnit}

{docstring Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}

{docstring Lean.Elab.Do.DoElemCont.mkBindUnlessPure}

:::example "Invoking Continuations"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
A version of the built-in syntax {keywordOf Lean.Parser.Term.InternalSyntax.doSkip}`skip`, which is equivalent to {lean (type := "Option Unit")}`pure ()`, can be implemented using an elaborator that immediately invokes its continuation with {name}`Unit`.
For better error messages, it also asserts that the continuation is expecting {name}`Unit`.
```lean
syntax (name := doNothing) "nothing" : doElem

@[doElem_elab doNothing]
def elabDoNothing : DoElab := fun stx dec => do
  let dec ← dec.ensureUnitAt stx
  dec.continueWithUnit
```
In order to generate code for control structures, the {keywordOf Lean.Parser.Term.do}`do`-element elaboration framework requires information about side effects that might be performed by each element.
This {ref "do-elab-control-info"}[control info] is registered via the {attr}`doElem_control_info` attribute.
Because {keywordOf doNothing}`nothing` does not modify mutable variables, throw exceptions, terminate loops early, or perform any other action, its control info is {name}`ControlInfo.pure`.
```lean
@[doElem_control_info doNothing]
def doNothing.control : ControlInfoHandler := fun _ => do return .pure
```

It is indeed equivalent to {lean (type := "Option Unit")}`pure ()`:
```lean (name := doNothing)
#eval show Option Unit from do nothing
```
```leanOutput doNothing
some ()
```
:::

:::example "Elaborating `do`-elements with `elab_rules`"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
An alternative version of {keywordOf doNothing}`nothing`, which is equivalent to the built-in syntax {keywordOf Lean.Parser.Term.InternalSyntax.doSkip}`skip`, can be implemented using {keywordOf Lean.Parser.Command.«elab_rules»}`elab_rules` as an alternative to an elaborator with the {attr}`doElem_elab` attribute.
```lean
syntax (name := doNothing) "nothing" : doElem

elab_rules : doElem <= dec
  | `(doElem|nothing%$tk) => do
    let dec ← dec.ensureUnitAt tk
    dec.continueWithUnit

@[doElem_control_info doNothing]
def doNothing.control : ControlInfoHandler := fun _ => do return .pure
```

It is equivalent to {lean (type := "Option Unit")}`pure ()`:
```lean (name := doNothing')
#eval show Option Unit from do nothing
```
```leanOutput doNothing'
some ()
```
:::

Because the elaborator invokes its continuation explicitly, rather than simply returning a value, it can control the context of elaboration.
In particular, it can use {name}`withReader` to modify the context, and it can invoke the continuation multiple times in order to support control structures with branching.
To prevent code size explosions, continuations track whether they may be elaborated multiple times in {name Lean.Elab.Do.DoElemCont.kind}`DoElemCont.kind`.
A continuation is {deftech}_duplicable_ if it may be invoked multiple times, and {deftech}_nonduplicable_ if not.
Nonduplicable continuations can be transformed into duplicable continuations using {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont`.

{docstring Lean.Elab.Do.DoElemCont.withDuplicableCont}

Unreachable code does not need to be elaborated.
When a {keywordOf Lean.Parser.Term.do}`do`-element's elaborator has detected that the result of the continuation's elaboration is unreachable, it can return its resulting term directly instead of passing it to the elaboration continuation.
It should produce a term that justifies abandoning the program, such as a call to {name}`False.elim`.
Before returning this term, it should invoke {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode` on the continuation, which warns users that the code that the continuation would elaborate is unreachable.

:::example "Unreachable Code"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Term Do
set_option backward.do.legacy false
```

The operator {keywordOf doAbsurd}`absurd` marks code as unreachable when provided with a proof of {name}`False`, which indicates that the current local context is logically inconsistent.
If passed a proof, it uses it; otherwise, it attempts some automation.
```lean
syntax (name := doAbsurd) "absurd" (" by " tacticSeq)? : doElem
```

Because {keywordOf doAbsurd}`absurd` can never return, and control can never proceed past it, its control information sets {name Lean.Elab.Do.ControlInfo.numRegularExits}`numRegularExits` to {lean}`0` and {name Lean.Elab.Do.ControlInfo.noFallthrough}`noFallthrough` to {lean}`true`:
```lean
@[doElem_control_info doAbsurd]
def inferAbsurd : ControlInfoHandler := fun _ =>
  return { numRegularExits := 0, noFallthrough := true }
```

The elaborator first extracts the proof syntax, falling back to a default if none is provided.
It then elaborates the proof as a proof of false.
If this succeeds, it marks the rest of the {keywordOf Lean.Parser.Term.do}`do`-sequence as dead code using {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode` and uses {name}`False.elim` as the resulting term, which it returns directly rather than to the continuation.
{name}`False.elim` is provided with the type that the term is expected to have, which is determined using {name}`Lean.Elab.Do.mkMonadApp` together with the result type.
It is important to use {name Lean.Elab.Do.Context.doBlockResultType}`Do.Context.doBlockResultType` rather than the continuation's result type because {ref "do-elab-effect-lift"}[effect lifting] may have locally modified the type.
```lean
@[doElem_elab doAbsurd]
def elabAbsurd : DoElab := fun stx dec => do
  let `(doElem| absurd $[by $tac?]?) := stx
    | throwUnsupportedSyntax
  let proofStx : Term ←
    if let some tac := tac? then
      `(by $tac)
    else
      `(by first | contradiction | grind)
  let proof ← elabTermEnsuringType proofStx (mkConst ``False)
  dec.elabAsSyntacticallyDeadCode
  let ty ← mkMonadApp (← read).doBlockResultType
  return (← Meta.mkAppOptM ``False.elim #[some ty, some proof])
```

{keywordOf doAbsurd}`absurd` allows the accumulated information from the nested conditionals to rule out the {keywordOf Lean.Parser.Term.doIf}`else` clause as unreachable:
```lean
#eval show Id (String × String × String) from do
  let classify : Nat → String := fun n => Id.run do
    if n < 3 then return "small"
    else if h1 : n < 10 then return "medium"
    else if h2 : n ≥ 10 then return "large"
    else absurd
  return (classify 1, classify 5, classify 99)
```

Due to the call to {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode`, steps after {keywordOf doAbsurd}`absurd` receive a dead code warning:
```lean (name := absurdOut)
def xs := #[1, 3, 5]
theorem xs_all_odd : ∀ x, x ∈ xs → x % 2 = 1 := by
  simp [xs]

#eval show Id Nat from do
  for h : n in 0...5 do
    let k := n * 2
    if h' : k ∈ xs then
      absurd by grind [xs_all_odd]
      return k
  pure 100
```
```leanOutput absurdOut
This `do` element and its control-flow region are dead code. Consider removing it.
```
However, it does run successfully:
```leanOutput absurdOut
100
```
:::

## Control Flow: `return`, `break`, and `continue`
%%%
tag := "do-elab-return-continue-break"
%%%

Three non-local jump instructions are supported in {keywordOf Lean.Parser.Term.do}`do`-notation: {keywordOf Lean.Parser.Term.doReturn}`return`, which terminates the entire {keywordOf Lean.Parser.Term.do}`do`-block early; {keywordOf Lean.Parser.Term.doBreak}`break`, which terminates a loop early; and {keywordOf Lean.Parser.Term.doContinue}`continue`, which terminates a single iteration of a loop early.
A {keywordOf Lean.Parser.Term.doReturn}`return` is always allowed, while {keywordOf Lean.Parser.Term.doBreak}`break` and {keywordOf Lean.Parser.Term.doContinue}`continue` are only valid inside the body of a loop.
During elaboration, each of these three jumps is represented by a continuation.

{docstring Lean.Elab.Do.getReturnCont +allowMissing}

{docstring Lean.Elab.Do.getBreakCont +allowMissing}

{docstring Lean.Elab.Do.getContinueCont +allowMissing}

The three continuations are installed in the context using the helper {name Lean.Elab.Do.enterLoopBody}`enterLoopBody`.

{docstring Lean.Elab.Do.enterLoopBody}

:::example "Single-Iteration Loop"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Term Do
set_option backward.do.legacy false
```
The single-iteration loop {keywordOf doOnce}`once` executes its body a single time, skipping to the end of the loop on {keywordOf Lean.Parser.Term.doBreak}`break` or {keywordOf Lean.Parser.Term.doContinue}`continue`:
```lean
syntax (name := doOnce) "once " doSeq : doElem
```
Its control info is based on that of the body.
A {keywordOf doOnce}`once` never breaks or continues itself, because it handles {keywordOf Lean.Parser.Term.doBreak}`break` and {keywordOf Lean.Parser.Term.doContinue}`continue` in its body; thus, it sets {name ControlInfo.breaks}`breaks` and {name ControlInfo.continues}`continues` to {lean}`false`.
{name ControlInfo.numRegularExits}`numRegularExits` is the number of times that control can reach the code following the {keywordOf doOnce}`once`.
The body's normal fallthrough, {keywordOf Lean.Parser.Term.doBreak}`break`, and {keywordOf Lean.Parser.Term.doContinue}`continue` all transfer control to the end of the loop, so control leaves a {keywordOf doOnce}`once` at most once.
{name ControlInfo.numRegularExits}`numRegularExits` is therefore {lean}`1` when the body can exit in any of these ways and {lean}`0` otherwise, in which case {name ControlInfo.noFallthrough}`noFallthrough` is set.
```lean
@[doElem_control_info doOnce]
def inferOnce : ControlInfoHandler := fun stx => do
  let `(doElem| once $body) := stx | throwUnsupportedSyntax
  let bodyInfo ← InferControlInfo.ofSeq body
  let exits :=
    bodyInfo.numRegularExits > 0 ||
    bodyInfo.breaks ||
    bodyInfo.continues
  return { bodyInfo with
    breaks := false
    continues := false
    numRegularExits := if exits then 1 else 0
    noFallthrough := !exits
  }
```
The actual elaborator for {keywordOf doOnce}`once` uses {name Lean.Elab.Do.enterLoopBody}`enterLoopBody` to associate the elaborator's overall continuation with the {keywordOf Lean.Parser.Term.doBreak}`break` and {keywordOf Lean.Parser.Term.doContinue}`continue` continuations inside the body.
Because the elaborated body can reach that continuation from several places, the elaborator counts these uses.
The body's control info does not indicate how many times {keywordOf Lean.Parser.Term.doBreak}`break` and {keywordOf Lean.Parser.Term.doContinue}`continue` may be invoked, so they are approximated as two exits each, safely ensuring that the continuation will be duplicated if either is used.
The total approximated use count is passed to {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont`, which shares the continuation rather than duplicating it at each use when the use count is greater than one, and so avoids code explosion.
It computes this count from the body directly, since the value reported by the control info handler is at most {lean}`1` and does not reflect the number of internal uses.
```lean
@[doElem_elab doOnce]
def elabOnce : DoElab := fun stx dec => do
  let `(doElem| once $body) := stx | throwUnsupportedSyntax
  let dec ← dec.ensureUnit
  let bodyInfo ← InferControlInfo.ofSeq body
  let numRegularExits :=
    bodyInfo.numRegularExits +
    (if bodyInfo.breaks then 2 else 0) +
    (if bodyInfo.continues then 2 else 0)
  dec.withDuplicableCont { bodyInfo with numRegularExits } fun dec => do
    let returnCont ← getReturnCont
    let exitCont := dec.continueWithUnit
    enterLoopBody exitCont exitCont returnCont do
      elabDoSeq body dec
```

{keywordOf doOnce}`once` can be used to terminate some part of a computation without terminating the entire {keywordOf Lean.Parser.Term.do}`do`-block with {keywordOf Lean.Parser.Term.doReturn}`return`:
```lean (name := once)
#eval show Id Nat from do
  let mut x := 0
  once
    x := x + 2
    if x % 2 = 0 then break
    x := 0
  return x
```
```leanOutput once
2
```
:::

## Control Information
%%%
tag := "do-elab-control-info"
%%%

In addition to an elaborator, custom {keywordOf Lean.Parser.Term.do}`do`-elements must provide {deftech}_control information_.
This describes how the custom element interacts with surrounding control structures and mutable variables.
The control information allows Lean to generate appropriate code; in particular, it allows {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont` to analyze the code to be elaborated by the continuation, which enables better code generation.
Control information is separate from elaborators because an elaborator needs to be able to analyze the _syntax_ of sub-elements before elaborating them in order to know how to structure its continuations.
*Custom {keywordOf Lean.Parser.Term.do}`do`-elements must provide accurate control information. Incorrect control information can result in incorrect code generation.*

:::syntax attr (title := "Do Element Control Information")
```grammar
doElem_control_info
```
{includeDocstring Lean.Elab.Do.controlInfoElemAttribute}
:::

{docstring Lean.Elab.Do.ControlInfoHandler}

If a {keywordOf Lean.Parser.Term.do}`do`-element neither reassigns variables nor causes early return or termination, the handler can return {name Lean.Elab.Do.ControlInfo.pure}`ControlInfo.pure`.
If it represents code with no regular exits and no other control effects, then the handler can return {name Lean.Elab.Do.ControlInfo.empty}`ControlInfo.empty`; otherwise, set {name Lean.Elab.Do.ControlInfo.numRegularExits}`ControlInfo.numRegularExits` to {lean}`0` and {name Lean.Elab.Do.ControlInfo.noFallthrough}`ControlInfo.noFallthrough` to {lean}`true` while also recording any early returns, reassignments, or loop terminations.


{docstring Lean.Elab.Do.ControlInfo}

{docstring Lean.Elab.Do.ControlInfo.pure +allowMissing}

{docstring Lean.Elab.Do.ControlInfo.empty}

If a {keywordOf Lean.Parser.Term.do}`do`-element itself contains other {keywordOf Lean.Parser.Term.do}`do`-elements, then it can use the combinators {name Lean.Elab.Do.ControlInfo.sequence}`ControlInfo.sequence` and {name Lean.Elab.Do.ControlInfo.alternative}`ControlInfo.alternative` to combine the control information from their sub-elements.
{name Lean.Elab.Do.ControlInfo.sequence}`ControlInfo.sequence` is used for sequential steps, and {name Lean.Elab.Do.ControlInfo.alternative}`ControlInfo.alternative` is used to merge control-flow branches.

{docstring Lean.Elab.Do.ControlInfo.sequence +allowMissing}

{docstring Lean.Elab.Do.ControlInfo.alternative +allowMissing}

Generally speaking, control information should be computed using {name Lean.Elab.Do.inferControlInfoElem}`inferControlInfoElem` or {name Lean.Elab.Do.inferControlInfoSeq}`inferControlInfoSeq`.

{docstring Lean.Elab.Do.inferControlInfoElem +allowMissing}

{docstring Lean.Elab.Do.inferControlInfoSeq +allowMissing}

In some advanced cases, one of the functions in {namespace}`Lean.Elab.Do.InferControlInfo` may be necessary:

{docstring Lean.Elab.Do.InferControlInfo.ofElem +allowMissing}

{docstring Lean.Elab.Do.InferControlInfo.ofSeq +allowMissing}

{docstring Lean.Elab.Do.InferControlInfo.ofOptionSeq +allowMissing}

{docstring Lean.Elab.Do.InferControlInfo.ofLetOrReassign +allowMissing}

{docstring Lean.Elab.Do.InferControlInfo.ofLetOrReassignArrow +allowMissing}

## Mutable Variables

One important part of the context is the set of mutable variables available for the {keywordOf Lean.Parser.Term.do}`do`-element being elaborated.
This is available in two fields: {name Lean.Elab.Do.Context.mutVars}`mutVars` provides the identifiers that initially bound the variables, while {name Lean.Elab.Do.Context.mutVarDefs}`mutVarDefs` maps their names to the local variables that represent them.
Due to {tech}[hygiene], the identifiers in {name Lean.Elab.Do.Context.mutVars}`mutVars` contain {tech}[macro scopes]; these should be removed using {name}`Name.simpMacroScopes` prior to constructing a user-facing error message.

Each mutable variable corresponds to at least one elaborated variable ({name}`Expr.fvar`).
These elaborated variables exist in a local context that tracks their user-visible names.
Mutation is implemented via a shadowing {keywordOf Lean.Parser.Term.«let»}`let`-binding, and subsequent steps in the {keywordOf Lean.Parser.Term.do}`do`-block are elaborated in a context in which this shadowing {keywordOf Lean.Parser.Term.«let»}`let` is the binding for the variable's user-visible name.
Use the standard elaboration helpers {name}`Lean.Meta.getFVarFromUserName` and {name}`Lean.Meta.getLocalDeclFromUserName` to retrieve the local variable associated with a user name, and {name}`TSyntax.getId` to convert an {name}`Ident` to a user name that can be looked up.

When a mutable variable is established with {keywordOf Lean.Parser.Term.doLet}`let mut`, a {keywordOf Lean.Parser.Term.«let»}`let`-binding is created to represent it, and the initial variable's binding identifier and {name}`Expr.fvar` are added to the context that is used around the continuation, which is invoked under {name}`withReader` to add the new variable.
After establishing the {keywordOf Lean.Parser.Term.«let»}`let`-binding, use {name Lean.Elab.Do.declareMutVar}`declareMutVar` to register one mutable variable or an array of them.

{docstring Lean.Elab.Do.declareMutVar}

{docstring Lean.Elab.Do.declareMutVars}

To ensure that an identifier refers to a mutable variable, use {name Lean.Elab.Do.throwUnlessMutVarDeclared}`throwUnlessMutVarDeclared`:

{docstring Lean.Elab.Do.throwUnlessMutVarDeclared}

{docstring Lean.Elab.Do.throwUnlessMutVarsDeclared}

::::example "Tracing Mutable Variables"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
The new syntax {keywordOf dbgMut}`dbg_mut` traces the current values of all mutable variables.

```lean
syntax (name := dbgMut) "dbg_mut" : doElem

@[doElem_elab dbgMut] def elabDbgMut : DoElab := fun _stx cont => do
  let ctx ← readThe Do.Context
  let parts : Array Term ← ctx.mutVars.mapM fun (x : Ident) => do
    let nameLit := x.getId.simpMacroScopes.toString
    `(term| s!"{$(quote nameLit)} = {repr $x}")
  let msg ← `(term| String.intercalate ", " [$parts,*])
  elabDoElem (← `(doElem| dbg_trace $msg)) cont
```

There is no interesting control information for {keywordOf dbgMut}`dbg_mut`.
```lean
@[doElem_control_info dbgMut]
def dbgMut.control : ControlInfoHandler := fun _ => do return .pure
```

Tracing a loop that computes Fibonacci numbers shows all the intermediate states:
```lean (name := mutDbg)
#eval show IO Unit from do
  let mut x := 1
  let mut y := 1
  for _ in 0...5 do
    let z := y
    dbg_mut
    y := x + y
    x := z
```
```leanOutput mutDbg
x = 1, y = 1
x = 1, y = 2
x = 2, y = 3
x = 3, y = 5
x = 5, y = 8
```
::::

The built-in elaborators for mutable variables take care of many subtle details, such as registering each resulting {keywordOf Lean.Parser.Term.«let»}`let`-binding of the mutable variable as aliases so that IDEs can give appropriate feedback.
If at all possible, it is best to reuse these built-in elaborators, either via a macro or by invoking {name Lean.Elab.Do.elabDoElem}`elabDoElem` on the appropriate syntax.

:::example "Mutating Variables"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
The operator {keywordOf doCensor}`censor` replaces all mutable variables with the default value defined in their type's {name}`Inhabited` instance.

```lean
syntax (name := doCensor) "censor" : doElem

@[doElem_elab doCensor]
def elabCensor : DoElab := fun stx dec => do
  let vars := (← readThe Do.Context).mutVars
  let dec ← dec.ensureUnitAt stx
  if h : vars.size = 0 then
    logErrorAt stx "There are no mutable variables to censor."
    dec.continueWithUnit
  else
    let assigns ← vars.mapM fun v =>
      `(doElem| $v:ident := Inhabited.default)
    elabDoElems1 assigns dec
```

The {keywordOf Lean.Parser.Term.do}`do`-elaboration context is not available in the control info handler, so there is no way to precisely return the set of all mutable variables as being modified.
However, the user names of all local variables are a suitable overapproximation:
```lean
@[doElem_control_info doCensor]
def doCensor.control : ControlInfoHandler := fun _ => do
  return { ControlInfo.pure with
      reassigns := (← getLCtx).decls.map (·.map (·.userName))
        |>.foldl (init := .empty) fun
          | names, some n => names.insert n
          | names, none => names
    }
```

After using {keywordOf doCensor}`censor`, all mutable variables have been reset to their types' default values:
```lean (name := censor)
#eval show IO Unit from do
  let mut x := 0
  let mut c := 'm'
  x := x + 1
  IO.println s!"x: {x}, c: {c}"
  c := 'f'
  IO.println s!"x: {x}, c: {c}"
  censor
  IO.println s!"x: {x}, c: {c}"
```
```leanOutput censor
x: 1, c: m
x: 1, c: f
x: 0, c: A
```

:::

## Lifting Effects
%%%
tag := "do-elab-effect-lift"
%%%

Many useful monadic operators take a function whose return type is within the monad, running this function in some modified way.
Examples include {name}`withReader`, {name}`tryCatch`, and {name}`IO.FS.withFile`.
Functions like {name}`tryCatch` have dedicated syntax that allows both the code that might throw an exception and the code that handles it to be part of the surrounding {keywordOf Lean.Parser.Term.do}`do`-block, and thus be able to, for example, reassign mutable variables or return early.
These other operators have no such syntax.

A {keywordOf Lean.Parser.Term.do}`do`-element elaborator can arrange for the body of the function that is passed to one of these operators in the elaborated expression to be part of the source {keywordOf Lean.Parser.Term.do}`do`-block, just as the exception-handling syntax does.
This is done using a {name Lean.Elab.Do.ControlLifter}`ControlLifter`, which generates suitable wrapper code around both the inner sequence of {keywordOf Lean.Parser.Term.do}`do`-elements and the function itself.
There are three steps:
1. A {name Lean.Elab.Do.ControlLifter}`ControlLifter` for the inner sequence is created based on its control info and the current element's continuation, using {name Lean.Elab.Do.ControlLifter.ofCont}`ControlLifter.ofCont`.
2. The inner sequence is elaborated using {name Lean.Elab.Do.ControlLifter.lift}`ControlLifter.lift`, which supplies the inner elaborator with a suitable continuation that generates the wrapping code.
3. Instead of invoking the original continuation, the elaborator invokes a continuation generated by {name Lean.Elab.Do.ControlLifter.restoreCont}`ControlLifter.restoreCont`, which adds suitable unwrapping code to the result.

The lifting code resembles the implementation of Lean's built-in {ref "monad-transformers"}[monad transformers].
For example, if the inner {keywordOf Lean.Parser.Term.do}`do`-sequence mutates a variable, then the wrapping and unwrapping code arranges for the variable to be passed to the lifted code and returned in a tuple, just like {name}`StateT`.
If the inner {keywordOf Lean.Parser.Term.do}`do`-sequence could throw an exception, then the lifted version resembles a use of {name}`ExceptT`.

{docstring Lean.Elab.Do.ControlLifter +allowMissing}

{docstring Lean.Elab.Do.ControlLifter.ofCont +allowMissing}

{docstring Lean.Elab.Do.ControlLifter.lift +allowMissing}

{docstring Lean.Elab.Do.ControlLifter.restoreCont +allowMissing}

:::example "Syntax for {name}`withReader`"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do Term
set_option backward.do.legacy false
```

In a {keywordOf Lean.Parser.Term.do}`do`-block, {keywordOf doLocally}`locally` allows a sequence of {keywordOf Lean.Parser.Term.do}`do`-elements to be run with a modified {name}`MonadReader` context:

```lean
syntax (name := doLocally)
  "locally " ident " => " termBeforeDo " do " doSeq : doElem
```

The {name Lean.Parser.Term.termBeforeDo}`termBeforeDo` parser matches Lean terms that do not themselves contain {keywordOf Lean.Parser.Term.do}`do` outside of parentheses or brackets.
Because this new syntax contains a sequence of {keywordOf Lean.Parser.Term.do}`do`-elements, its control info must be computed from these elements:
```lean
@[doElem_control_info doLocally]
def inferLocally : ControlInfoHandler := fun stx => do
  let `(doElem| locally $_:ident => $_ do $seq) := stx
    | throwUnsupportedSyntax
  InferControlInfo.ofSeq seq
```

The actual elaborator starts by computing the control information for the body, and then derives a control lifter from the control information and the original continuation.
This control lifter can elaborate the body; it provides its own continuation to the elaborator.
Ordinary term elaboration techniques are used to construct the application of {name}`withReader`, with special attention paid to ensuring that the function argument is elaborated with a non-dependent function type in the correct universe for the monad (which is available in {name}`Context.monadInfo` as {name}`MonadInfo.u`).
Finally, the control lifter is used once again to reconstruct a suitable continuation for the full elaboration result:
```lean
@[doElem_elab doLocally] def elabDoLocally : DoElab := fun stx dec => do
  let `(doElem| locally $x:ident => $e do $seq) := stx
    | throwUnsupportedSyntax
  let lifter ← ControlLifter.ofCont (← inferControlInfoElem stx) dec
  let body ← lifter.lift (elabDoSeq seq)
  let ρ ← Meta.mkFreshExprMVar (mkSort (.succ (← read).monadInfo.u))
  let f ← Term.elabTermEnsuringType (← `(fun $x => $e)) (← mkArrow ρ ρ)
  Term.synthesizeSyntheticMVarsNoPostponing
  let wrapped ← Meta.mkAppM ``MonadWithReaderOf.withReader #[f, body]
  (← lifter.restoreCont).mkBindUnlessPure wrapped
```

With this elaborator in place, the value provided by a {name}`ReaderT` can be locally overridden while still permitting effects that are tied to the surrounding {keywordOf Lean.Parser.Term.do}`do`-block:
```lean (name := locallyDemo)
abbrev App := ReaderT Nat Id

#eval show Id Nat from do
  Id.run <| (·.run 5) <| show App Nat from do
    let mut total := 0
    total := total + (← read)
    locally r => r + 100 do
      -- Mutates an outer variable
      total := total + (← read)
      if (← read) > 1000 then
        -- Early return from the outer block
        return 999
    return total
```
```leanOutput locallyDemo
110
```
:::

:::example "Locally Violating Invariants"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do Term Meta
open Lean.Parser.Term (doSeq)
set_option backward.do.legacy false
```
When some invariant of a mutable variable needs to be maintained, it is typically most convenient to use a subtype.
However, subtypes have the drawback that the invariant must _always_ be maintained; it cannot be broken locally and re-established.
While it is possible to use a second mutable variable for this purpose, this clutters the code and is error-prone.
With a suitable extension to {keywordOf Lean.Parser.Term.do}`do`-notation, local breaking and re-establishment of invariants can be made convenient.

The first step is to establish syntax for this operation.
An {keywordOf openMutPure}`open mut` will “open” the subtype, freeing the contained data from the restrictions of the predicate in the nested block.
After the block is complete, the user must either prove or check that the invariant holds; placing a {keywordOf Lean.Parser.Term.do}`do` block in the {keywordOf openMutPure}`invariant` section indicates that a dynamic check is to be performed.
The second syntax definition has an explicit high priority to avoid ambiguity, which ensures that it is used whenever a {keywordOf Lean.Parser.Term.do}`do`-block is present.
```lean
syntax (name := openMutPure)
  "open" "mut" ident "do" doSeq "invariant" term : doElem

syntax (name := openMutMon) (priority := high)
  "open" "mut" ident "do" doSeq "invariant" "do" doSeq : doElem
```

The control info handlers for these operations are a function of the embedded {name}`doSeq` syntax:
```lean
@[doElem_control_info openMutPure, doElem_control_info openMutMon]
def openMutInfo : ControlInfoHandler := fun
  | `(doElem|open mut $x do $steps invariant do $steps') => do
    let info ← inferControlInfoSeq steps
    let info' ← inferControlInfoSeq steps'
    return info.sequence info'
  | `(doElem|open mut $x do $steps invariant $tm:term) =>
    inferControlInfoSeq steps
  | _ => throwUnsupportedSyntax
```

The workhorse of the elaborator is a helper that does the following:
1. It ensures that the provided name in fact refers to a variable with a subtype, extracting the base type and predicate.
2. It extracts the inner value from the subtype.
3. It {keywordOf Lean.Parser.Term.«let»}`let`-binds the inner value, establishing the {keywordOf Lean.Parser.Term.«let»}`let`-bound variable as an alias and arranging for it to be mutable.
4. It elaborates the body with a continuation that invokes the provided elaborator that “closes” the subtype, re-establishing the invariant.
```lean
def openMutBody (x : Ident) (seq : TSyntax ``doSeq)
    (mkClose : (p outerTy : Expr) → (base : FVarId) → DoElabM Expr) :
    DoElabM Expr := do
  -- Ensure that it is mutable
  throwUnlessMutVarDeclared x
  -- Ensure that it is a subtype
  let outerDecl ← getLocalDeclFromUserName x.getId
  let ty ← whnf outerDecl.type
  let (``Subtype, #[α, p]) := ty.getAppFnArgs
    | throwError "`open mut`: `{x}` is not a subtype, but is a `{ty}`"

  -- Get the value from the subtype
  let base := outerDecl.fvarId
  let init ← mkAppM ``Subtype.val #[outerDecl.toExpr]

  -- Let-bind and continue
  withLetDecl x.getId α init (nondep := false) fun innerX => do
    addLocalVarInfo x innerX
    pushInfoLeaf <| .ofFVarAliasInfo {
      userName := x.getId, id := innerX.fvarId!, baseId := base
    }
    let bodyCont : DoElemCont := {
      resultName := ← mkFreshUserName `__r, resultType := ← mkPUnit
      k := mkClose p outerDecl.type base
    }
    mkLetFVars #[innerX] (← declareMutVar x do elabDoSeq seq bodyCont)
```

The call to {name}`addLocalVarInfo` informs the language server about the connection between the elaborated {keywordOf Lean.Parser.Term.«let»}`let`-bound variable and the identifier in the source code, enabling features such as type information on hover.
The {name}`pushInfoLeaf` combined with {name}`Info.ofFVarAliasInfo` registers the {keywordOf Lean.Parser.Term.«let»}`let`-bound variable as an alias of existing bindings.

Closing the pure version consists of introducing a new {keywordOf Lean.Parser.Term.«let»}`let`-binding, shadowing and aliasing the mutable variable, with the updated value and proof.
```lean
def rebindMut (x : Ident) (outerTy repacked : Expr) (base : FVarId)
    (dec : DoElemCont) : DoElabM Expr :=
  withLetDecl x.getId outerTy repacked (nondep := false) fun newX => do
    addLocalVarInfo x newX
    pushInfoLeaf <| .ofFVarAliasInfo {
      userName := x.getId, id := newX.fvarId!, baseId := base
    }
    mkLetFVars #[newX] (← dec.continueWithUnit)

```

The elaborator for the pure version connects the two pieces:
```lean
@[doElem_elab openMutPure]
def elabOpenMutPure : DoElab := fun stx dec => do
  let `(doElem| open mut $x:ident do $seq invariant $prf:term) := stx
    | throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt x
  openMutBody x seq fun p outerTy base => do
    let cur ← getFVarFromUserName x.getId
    let proof ← Term.elabTermEnsuringType prf (mkApp p cur)
    rebindMut x outerTy (← mkAppM ``Subtype.mk #[cur, proof]) base dec
```

To demonstrate this feature in action, take the type {name}`Pos` of nonzero natural numbers:
```lean
abbrev Pos := { n : Nat // 0 < n }
```

Within the {keywordOf openMutPure}`open` block, `x` has type {name}`Nat`.
Both it and other mutable variables can be reassigned:
```lean (name := openDemo)
#eval show Id (Pos × Nat) from do
  let mut other := 100
  let mut x : Pos := ⟨10, by grind⟩
  open mut x do
    x := x * 2
    other := other + x
    x := x + 1
  invariant by grind
  return (x, other)
```
```leanOutput openDemo
(21, 120)
```

Likewise, the inner block can {keywordOf Lean.Parser.Term.doReturn}`return` from the outer {keywordOf Lean.Parser.Term.do}`do` block:
```lean (name := openDemo2)
#eval show Id (Nat × Nat) from do
  let mut other := 100
  let mut x : Pos := ⟨10, by grind⟩
  open mut x do
    x := x * 2
    other := other + x
    if other > 0 then return (0, other)
    x := x + 1
  invariant by grind
  return (x.val, other)
```
```leanOutput openDemo2
(0, 120)
```

For cases where it is impossible to prove that the returned value satisfies the predicate, it can still be useful to _check_ that it does.
The elaborator for the monadic variant expects a {name}`PLift`'ed proof to be returned:
```lean
def closeInvariant {α : Type} {P : α → Prop} [Monad m]
    (val : α) (act : m (PLift (P val))) : m (Subtype P) :=
  return ⟨val, (← act).down⟩

@[doElem_elab openMutMon]
def elabOpenMutMon : DoElab := fun stx dec => do
  let `(doElem| open mut $x:ident do $seq invariant do $invSeq) := stx
    | throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt x
  openMutBody x seq fun _p outerTy base => do
    let cur ← getFVarFromUserName x.getId
    let actionStx ←
      ``(closeInvariant $(← Term.exprToSyntax cur) (do $invSeq))
    let action ← elabTermEnsuringType actionStx (← mkMonadApp outerTy)
    let rn ← mkFreshUserName `__repacked
    let closeCont : DoElemCont := {
      resultName := rn, resultType := outerTy
      k := do
        let d ← getLocalDeclFromUserName rn
        rebindMut x outerTy d.toExpr base dec
    }
    closeCont.mkBindUnlessPure action
```

Now, a runtime check can ensure the invariant, or throw an exception if it does not hold:
```lean
def trySub3 (x : Pos) : IO Pos := do
  let mut x := x
  open mut x do
    x := x - 3
  invariant do
    if h : 0 < x then pure ⟨h⟩
    else throw (IO.userError s!"Not positive: x = {x}")
  return x
```
```lean (name := openMutMon1)
#eval trySub3 ⟨10, by grind⟩
```
```leanOutput openMutMon1
7
```
```lean +error  (name := openMutMon2)
#eval trySub3 ⟨3, by grind⟩
```
```leanOutput openMutMon2
Not positive: x = 0
```

:::
