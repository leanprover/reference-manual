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

@[role]
def «namespace» : RoleExpanderOf Unit
  | (), #[arg] => do
    let `(inline|code($s)) := arg
      | throwErrorAt arg "Expected code"
    -- TODO validate that namespace exists? Or is that too strict?
    -- TODO namespace domain for documentation
    ``(Inline.code $(quote s.getString))
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Expected code literal with the namespace"
    else
      throwError "Expected code literal with the namespace"
