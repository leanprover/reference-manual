/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public meta import Verso.Doc.Elab.Monad
import Verso.Doc.Elab.Monad

public section

open scoped Lean.Doc.Syntax

open Verso Doc Elab
open Lean Elab
open Verso.SyntaxUtils
open SubVerso.Highlighting

@[role]
meta def «namespace» : RoleExpanderOf Unit
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
