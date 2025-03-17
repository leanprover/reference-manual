/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Position
import Lean.Parser

import Verso.Parser
import Verso.Doc.ArgParse
import SubVerso.Highlighting

open Lean

namespace Verso.ArgParse

open Lean.Elab (MonadInfoTree)
open Lean

variable {m} [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m] [MonadLiftT CoreM m] [MonadFileMap m]

def ValDesc.nat [Monad m] [MonadError m] : ValDesc m Nat where
  description := m!"a name"
  get
    | .num n => pure n.getNat
    | other => throwError "Expected string, got {repr other}"

def ValDesc.inlinesString : ValDesc m (FileMap × TSyntaxArray `inline) where
  description := m!"a string that contains a sequence of inline elements"
  get
    | .str s => open Lean.Parser in do
      let text ← getFileMap
      let input := s.getString
      let ictxt := mkInputContext input s!"string literal on line {s.raw.getPos?.map ((s!" on line {text.toPosition · |>.line}")) |>.getD ""}"
      let env ← getEnv
      let pmctx : ParserModuleContext := {env, options := {}}
      let p := Parser.textLine
      let s' := p.run ictxt pmctx (getTokenTable env) (mkParserState input)
      if s'.allErrors.isEmpty then
        if s'.stxStack.size = 1 then
          match s'.stxStack.back with
          | .node _ _ contents => pure (FileMap.ofString input, contents.map (⟨·⟩))
          | other => throwError "Unexpected syntax from Verso parser. Expected a node, got {other}"
        else throwError "Unexpected internal stack size from Verso parser. Expected 1, got {s'.stxStack.size}"
      else
        let mut msg := "Failed to parse:"
        for (p, _, e) in s'.allErrors do
          let {line, column} := text.toPosition p
          msg := msg ++ s!"  {line}:{column}: {toString e}\n    {repr <| input.extract p input.endPos}\n"
        throwError msg
    | other => throwError "Expected string, got {repr other}"


end Verso.ArgParse

namespace Manual

def parserInputString [Monad m] [MonadFileMap m]
    (str : TSyntax `str) :
    m String := do
  let text ← getFileMap
  let preString := text.source.extract 0 (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.iter
  while !iter.atEnd do
    if iter.curr == '\n' then code := code.push '\n'
    else
      for _ in [0:iter.curr.utf8Size] do
        code := code.push ' '
    iter := iter.next
  let strOriginal? : Option String := do
    let ⟨start, stop⟩ ← str.raw.getRange?
    text.source.extract start stop
  code := code ++ strOriginal?.getD str.getString
  return code

structure SyntaxError where
  pos : Position
  endPos : Position
  text : String
deriving ToJson, FromJson, BEq, Repr

open Lean.Syntax in
instance : Quote Position where
  quote
    | .mk l c => mkCApp ``Position.mk #[quote l, quote c]

open Lean.Syntax in
instance : Quote SyntaxError where
  quote
    | .mk pos endPos text => mkCApp ``SyntaxError.mk #[quote pos, quote endPos, quote text]

-- Based on mkErrorMessage used in Lean upstream - keep them in synch for best UX
open Lean.Parser in
private partial def mkSyntaxError (c : InputContext) (pos : String.Pos) (stk : SyntaxStack) (e : Parser.Error) : SyntaxError := Id.run do
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
    endPos := (c.fileMap.toPosition <$> endPos?).getD (c.fileMap.toPosition (pos + c.input.get pos))
    text := toString e
  }
where
  -- Error recovery might lead to there being some "junk" on the stack
  lastTrailing (s : SyntaxStack) : Option Substring :=
    s.toSubarray.findSomeRevM? (m := Id) fun stx =>
      if let .original (trailing := trailing) .. := stx.getTailInfo then pure (some trailing)
        else none

open Lean.Parser in
def runParserCategory (env : Environment) (opts : Lean.Options) (catName : Name) (input : String) (fileName : String := "<example>") : Except (List (Position × String)) Syntax :=
    let p := andthenFn whitespace (categoryParserFnImpl catName)
    let ictx := mkInputContext input fileName
    let s := p.run ictx { env, options := opts } (getTokenTable env) (mkParserState input)
    if !s.allErrors.isEmpty then
      Except.error (toErrorMsg ictx s)
    else if ictx.input.atEnd s.pos then
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
def runParserCategory' (env : Environment) (opts : Lean.Options) (catName : Name) (input : String) (fileName : String := "<example>") : Except (Array SyntaxError) Syntax :=
    let p := andthenFn whitespace (categoryParserFnImpl catName)
    let ictx := mkInputContext input fileName
    let s := p.run ictx { env, options := opts } (getTokenTable env) (mkParserState input)
    if !s.allErrors.isEmpty then
      Except.error <| toSyntaxErrors ictx s
    else if ictx.input.atEnd s.pos then
      Except.ok s.stxStack.back
    else
      Except.error (toSyntaxErrors ictx (s.mkError "end of input"))
where
  toSyntaxErrors (ictx : InputContext) (s : ParserState) : Array SyntaxError :=
    s.allErrors.map fun (pos, stk, e) => (mkSyntaxError ictx pos stk e)

open Lean.Parser in
def runParser
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
  else if ictx.input.atEnd s.pos then
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
def commandWithoutAsync : (act : CommandElabM α) → CommandElabM α :=
  withScope fun sc =>
    {sc with opts := Elab.async.set sc.opts false}

def withoutAsync [Monad m] [MonadWithOptions m] : (act : m α) → m α :=
  withOptions (Elab.async.set · false)


/--
Consistently rewrite all substrings that look like automatic metavariables (e.g "?m.123") so
that they're ?m.1, ?m.2, etc.
-/
def normalizeMetavars (str : String) : String := Id.run do
  let mut out := ""
  let mut iter := str.iter
  let mut gensymCounter := 1
  let mut nums : Std.HashMap String Nat := {}
  -- States are:
  -- * none - Not looking at a metavar
  -- * 0 - Saw the ?
  -- * 1 - Saw the m
  -- * 2 - Saw the .
  -- * 3 - Saw one or more digits
  let mut state : Option (Fin 4 × String.Iterator) := none
  while h : iter.hasNext do
    let c := iter.curr' h

    match state with
    | none =>
      if c == '?' then
        state := some (0, iter)
      else
        out := out.push c
    | some (0, i) =>
      state := if c == 'm' then some (1, i) else none
    | some (1, i) =>
      state := if c == '.' then some (2, i) else none
    | some (2, i) =>
      state := if c.isDigit then some (3, i) else none
    | some (3, i) =>
      unless c.isDigit do
        state := none
        let mvarStr := i.extract iter
        match nums[mvarStr]? with
        | none =>
          nums := nums.insert mvarStr gensymCounter
          out := out ++ s!"?m.{gensymCounter}"
          gensymCounter := gensymCounter + 1
        | some s => out := out ++ s!"?m.{s}"
        out := out.push c

    iter := iter.next
  match state with
  | some (3, i) =>
    let mvarStr := i.extract iter
    match nums[mvarStr]? with
    | none =>
      nums := nums.insert mvarStr gensymCounter
      out := out ++ s!"?m.{gensymCounter}"
      gensymCounter := gensymCounter + 1
    | some s => out := out ++ s!"?m.{s}"
  | some (_, i) =>
    out := out ++ i.extract iter
  | _ => pure ()

  out

/-- info: "List ?m.1" -/
#guard_msgs in
#eval normalizeMetavars "List ?m.9783"

/-- info: "List ?m.1 " -/
#guard_msgs in
#eval normalizeMetavars "List ?m.9783 "

/-- info: "x : ?m.1\nxs : List ?m.1\nelem : x ∈ xs\n⊢ xs.length > 0\n" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1034
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0
"##

/-- info: "x : ?m.1\nxs : List ?m.1\nelem : x ∈ xs\n⊢ xs.length > 0" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1034
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0"##

/-- info: "x : ?m.1\nxs : List ?m.2\nelem : x ∈ xs\n⊢ xs.length > 0" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1034
xs : List ?m.10345
elem : x ∈ xs
⊢ xs.length > 0"##

/-- info: "x : ?m.1\nxs : List ?m.2\nelem : x ∈ xs\n⊢ xs.length > 0" -/
#guard_msgs in
#eval normalizeMetavars
  r##"x : ?m.1035
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0"##

#eval normalizeMetavars
  r##"x : ?m.1035
α : Type ?u.1234
xs : List ?m.1034
elem : x ∈ xs
⊢ xs.length > 0"##
