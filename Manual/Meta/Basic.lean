/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Position
public import Lean.Syntax
public import Lean.Environment
public import Lean.Parser.Types
public import Lean.Elab.Command
import Lean.Parser

import Verso.Parser
import Verso.Doc.ArgParse
import SubVerso.Highlighting

open Lean

namespace Manual

public def parserInputString [Monad m] [MonadFileMap m]
    (str : TSyntax `str) :
    m String := do
  let text ← getFileMap
  let preString := String.Pos.Raw.extract text.source 0 (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.startValidPos
  while h : iter ≠ preString.endValidPos do
    let curr := iter.get h
    iter := iter.next h
    if curr == '\n' then code := code.push '\n'
    else
      for _ in [0:curr.utf8Size] do
        code := code.push ' '

  let strOriginal? : Option String := do
    let ⟨start, stop⟩ ← str.raw.getRange?
    start.extract text.source stop
  code := code ++ strOriginal?.getD str.getString
  return code

public structure SyntaxError where
  pos : Position
  endPos : Position
  text : String
deriving ToJson, FromJson, BEq, Repr

open Lean.Syntax in
public instance : Quote Position where
  quote
    | .mk l c => mkCApp ``Position.mk #[quote l, quote c]

open Lean.Syntax in
public instance : Quote SyntaxError where
  quote
    | .mk pos endPos text => mkCApp ``SyntaxError.mk #[quote pos, quote endPos, quote text]

-- Based on mkErrorMessage used in Lean upstream - keep them in synch for best UX
open Lean.Parser in
private partial def mkSyntaxError (c : InputContext) (pos : String.Pos.Raw) (stk : SyntaxStack) (e : Parser.Error) : SyntaxError := Id.run do
  let mut pos := pos
  let mut endPos? := none
  let mut e := e
  unless e.unexpectedTk.isMissing do
    -- calculate error parts too costly to do eagerly
    if let some r := e.unexpectedTk.getRange? then
      pos := r.start
      endPos? := some r.stop
    let unexpected := match e.unexpectedTk with
      | .ident .. => "unexpected identifier"
      | .atom _ v => s!"unexpected token '{v}'"
      | _         => "unexpected token"  -- TODO: categorize (custom?) literals as well?
    e := { e with unexpected }
    -- if there is an unexpected token, include preceding whitespace as well as the expected token could
    -- be inserted at any of these places to fix the error; see tests/lean/1971.lean
    if let some trailing := lastTrailing stk then
      if trailing.stopPos == pos then
        pos := trailing.startPos
  return {
    pos := c.fileMap.toPosition pos
    endPos := (c.fileMap.toPosition <$> endPos?).getD (c.fileMap.toPosition (pos + c.get pos))
    text := toString e
  }
where
  -- Error recovery might lead to there being some "junk" on the stack
  lastTrailing (s : SyntaxStack) : Option Substring.Raw :=
    s.toSubarray.findSomeRevM? (m := Id) fun stx =>
      if let .original (trailing := trailing) .. := stx.getTailInfo then pure (some trailing)
        else none

open Lean.Parser in
public def runParserCategory (env : Environment) (opts : Lean.Options) (catName : Name) (input : String) (fileName : String := "<example>") : Except (List (Position × String)) Syntax :=
    let p := andthenFn whitespace (categoryParserFnImpl catName)
    let ictx := mkInputContext input fileName
    let s := p.run ictx { env, options := opts } (getTokenTable env) (mkParserState input)
    if !s.allErrors.isEmpty then
      Except.error (toErrorMsg ictx s)
    else if ictx.atEnd s.pos then
      Except.ok s.stxStack.back
    else
      Except.error (toErrorMsg ictx (s.mkError "end of input"))
where
  toErrorMsg (ctx : InputContext) (s : ParserState) : List (Position × String) := Id.run do
    let mut errs := []
    for (pos, _stk, err) in s.allErrors do
      let pos := ctx.fileMap.toPosition pos
      errs := (pos, toString err) :: errs
    errs.reverse


open Lean.Parser in
/--
A version of `Manual.runParserCategory` that returns syntax errors located the way Lean does.
-/
public def runParserCategory' (env : Environment) (opts : Lean.Options) (catName : Name) (input : String) (fileName : String := "<example>") : Except (Array SyntaxError) Syntax :=
    let p := andthenFn whitespace (categoryParserFnImpl catName)
    let ictx := mkInputContext input fileName
    let s := p.run ictx { env, options := opts } (getTokenTable env) (mkParserState input)
    if !s.allErrors.isEmpty then
      Except.error <| toSyntaxErrors ictx s
    else if ictx.atEnd s.pos then
      Except.ok s.stxStack.back
    else
      Except.error (toSyntaxErrors ictx (s.mkError "end of input"))
where
  toSyntaxErrors (ictx : InputContext) (s : ParserState) : Array SyntaxError :=
    s.allErrors.map fun (pos, stk, e) => (mkSyntaxError ictx pos stk e)

open Lean.Parser in
public def runParser
    (env : Environment) (opts : Lean.Options)
    (p : Parser) (input : String) (fileName : String := "<example>")
    (currNamespace : Name := .anonymous) (openDecls : List OpenDecl := [])
    (prec : Nat := 0) :
    Except (List (Position × String)) Syntax :=
  let ictx := mkInputContext input fileName
  let p' := adaptCacheableContext ({· with prec}) p
  let s := p'.fn.run ictx { env, currNamespace, openDecls, options := opts } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    Except.error (toErrorMsg ictx s)
  else if ictx.atEnd s.pos then
    Except.ok s.stxStack.back
  else
    Except.error (toErrorMsg ictx (s.mkError "end of input"))
where
  toErrorMsg (ctx : InputContext) (s : ParserState) : List (Position × String) := Id.run do
    let mut errs := []
    for (pos, _stk, err) in s.allErrors do
      let pos := ctx.fileMap.toPosition pos
      errs := (pos, toString err) :: errs
    errs.reverse

open Lean Elab Command in
public def commandWithoutAsync : (act : CommandElabM α) → CommandElabM α :=
  withScope fun sc =>
    {sc with opts := Elab.async.set sc.opts false}

public def withoutAsync [Monad m] [MonadWithOptions m] : (act : m α) → m α :=
  withOptions (Elab.async.set · false)

open scoped Lean.Doc.Syntax in
/--
If the array of inlines contains a single code element, it is returned. Otherwise, an error is
logged and `none` is returned.
-/
public def oneCodeStr? [Monad m] [MonadError m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (inlines : Array (TSyntax `inline)) : m (Option StrLit) := do
  let #[code] := inlines
    | if inlines.size == 0 then
        Lean.logError "Expected a code element"
      else
        logErrorAt (mkNullNode inlines) "Expected one code element"
      return none
  let `(inline|code($code)) := code
    | logErrorAt code "Expected a code element"
      return none
  return some code
