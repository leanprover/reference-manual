/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Verso.Output.Html
import Verso.Parser

public section

-- TODO generalize upstream - this is based on the one in the blog genre.
namespace Manual
open Verso
open Lean.Doc.Syntax

abbrev LexedText.Highlighted := Array (Option String × String)

structure LexedText where
  name : String
  content : LexedText.Highlighted
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

open Lean in
meta instance : Quote LexedText where
  quote
    | LexedText.mk n c => Syntax.mkCApp ``LexedText.mk #[quote n, quote c]

namespace LexedText

open Lean Parser

open Verso.Parser (ignoreFn)

-- In the absence of a proper regexp engine, abuse ParserFn here
structure Highlighter where
  name : String
  lexer : ParserFn
  tokenClass : Syntax → Option String

def highlight (hl : Highlighter) (str : String) : IO LexedText := do
  let mut out : Highlighted := #[]
  let mut unHl : Option String := none
  let env ← mkEmptyEnvironment
  let ictx := mkInputContext str "<input>"
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let mut s := mkParserState str
  repeat
    if s.pos.atEnd str then
      if let some txt := unHl then
        out := out.push (none, txt)
      break
    let s' := hl.lexer.run ictx pmctx {} s
    if s'.hasError then
      let c := s.pos.get! str
      unHl := unHl.getD "" |>.push c
      s := {s with pos := s.pos + c}
    else
      let stk := s'.stxStack.extract 0 s'.stxStack.size
      if stk.size ≠ 1 then
        unHl := unHl.getD "" ++ s.pos.extract str s'.pos
        s := s'.restore 0 s'.pos
      else
        let stx := stk[0]!
        match hl.tokenClass stx with
        | none => unHl := unHl.getD "" ++ s.pos.extract str s'.pos
        | some tok =>
          if let some ws := unHl then
            out := out.push (none, ws)
            unHl := none
          out := out.push (some tok, s.pos.extract str s'.pos)
        s := s'.restore 0 s'.pos
  pure ⟨hl.name, out⟩

def token (kind : Name) (p : ParserFn) : ParserFn :=
  nodeFn kind <| ignoreFn p

open Verso.Output Html

def toHtml (text : LexedText) : Html :=
  text.content.map fun
    | (none, txt) => (txt : Html)
    | (some cls, txt) => {{ <span class={{cls}}>{{txt}}</span>}}

end LexedText
