/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Lean.Elab.InfoTree.Types
import SubVerso.Highlighting.Code

open scoped Lean.Doc.Syntax

open Verso Doc Elab
open Lean Elab
open Verso.Genre.Manual InlineLean Scopes
open Verso.SyntaxUtils
open SubVerso.Highlighting

@[code_block]
def imports : CodeBlockExpanderOf Unit
  | (), str => do
    let altStr ← parserInputString str
    let p := Parser.whitespace >> Parser.Module.header.fn
    let headerStx ← p.parseString altStr
    let hl ← highlight headerStx #[] {}
    ``(Block.other (Block.lean $(quote hl) {}) #[Block.code $(quote str.getString)])
