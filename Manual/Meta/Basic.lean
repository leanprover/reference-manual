/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Position
import Lean.Parser

import Verso.Doc.ArgParse
import SubVerso.Highlighting

open Lean

open Verso.ArgParse in
def Verso.ArgParse.ValDesc.nat [Monad m] [MonadError m] : ValDesc m Nat where
  description := m!"a name"
  get
    | .num n => pure n.getNat
    | other => throwError "Expected string, got {repr other}"


namespace SubVerso.Highlighting
/--
Remove n levels of indentation from highlighted code.
-/
partial def Highlighted.deIndent (n : Nat) (hl : Highlighted) : Highlighted :=
  (remove hl).run' (some n)
where
  remove (hl : Highlighted) : StateM (Option Nat) Highlighted := do
    match hl with
    | .token t =>
      set (none : Option Nat)
      return .token t
    | .span i x => .span i <$> remove x
    | .seq xs => .seq <$> xs.mapM remove
    | .text s =>
      let mut s' := ""
      let mut iter := s.iter
      while h : iter.hasNext do
        let c := iter.curr' h
        iter := iter.next
        match c with
        | '\n' =>
          set (some n)
        | ' ' =>
          if let some (i + 1) ← get then
            set (some i)
            continue
        | _ => set (none : Option Nat)
        s' := s'.push c
      return .text s'
    | .point p s => return .point p s
    | .tactics gs x y hl => .tactics gs x y <$> remove hl

end SubVerso.Highlighting

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
def runParser (env : Environment) (opts : Lean.Options) (p : Parser) (input : String) (fileName : String := "<example>") (prec : Nat := 0) : Except (List (Position × String)) Syntax :=
    let ictx := mkInputContext input fileName
    let p' := adaptCacheableContext ({· with prec}) p
    let s := p'.fn.run ictx { env, options := opts } (getTokenTable env) (mkParserState input)
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
