/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Lean.Elab.InfoTree.Types
import SubVerso.Highlighting.Code
import Manual.Meta.Basic

open scoped Lean.Doc.Syntax

open Verso Doc Elab
open Lean Elab
open Verso.Genre.Manual InlineLean Scopes
open Verso.SyntaxUtils
open SubVerso.Highlighting
open ArgParse

namespace Manual

structure ImportsParams where
  «show» : Bool := true

instance : FromArgs ImportsParams m where
  fromArgs := ImportsParams.mk <$> .flag `show true (some "Whether to show the import header")

@[code_block]
def imports : CodeBlockExpanderOf ImportsParams
  | { «show» }, str => do
    let altStr ← parserInputString str
    let p := Parser.whitespace >> Parser.Module.header.fn
    let headerStx ← p.parseString altStr
    let hl ← highlight headerStx #[] {}
    if «show» then
      ``(Block.other (Block.lean $(quote hl) {}) #[Block.code $(quote str.getString)])
    else
      ``(Block.empty)

@[role]
def «import» : RoleExpanderOf Unit
  | (), contents => do
    let some str ← oneCodeStr? contents
      | ``(Verso.Doc.Inline.empty)

    let p := Lean.Parser.Module.import.fn
    let stx ← withoutModifyingEnv do
      modifyEnv fun env =>
        Parser.parserExtension.modifyState env fun st =>
          { st with tokens := Parser.Module.updateTokens st.tokens }
      Lean.Doc.parseStrLit p str
    let hl ← highlight stx #[] {}
    ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote str.getString)])
