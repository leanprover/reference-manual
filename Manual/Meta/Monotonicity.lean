/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import Verso

import Manual.Meta.Attribute
import Manual.Meta.Basic
import Manual.Meta.Lean
import Manual.Meta.Table

open Lean Meta Elab
open Verso Doc Elab Manual
open SubVerso.Highlighting Highlighted


namespace Manual

def mkTable (rows : Array (Array Syntax)) (header : String) (name : String) : TermElabM Term := do
  if h : rows.size = 0 then
    throwError "Expected at least one row"
  else
    let columns := rows[0].size
    if columns = 0 then
      throwError "Expected at least one column"
    if rows.any (·.size != columns) then
      throwError s!"Expected all rows to have same number of columns, but got {rows.map (·.size)}"

    let blocks : Array (Syntax.TSepArray `term ",") := rows.map (Syntax.TSepArray.mk)
    ``(Block.other (Block.table $(quote columns) $(quote header) $(quote name)) #[Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])

@[block_role_expander monotonicityLemmas]
def monotonicityLemmas : BlockRoleExpander
  | #[], #[] => do
    let names := (Meta.Monotonicity.monotoneExt.getState (← getEnv)).values
    let names := names.qsort (toString · < toString ·)

    let rows : Array (Array Syntax) ← names.mapM fun name => do
      -- Extract the target pattern
      let ci ← getConstInfo name
      let targetStx : TSyntax `term ←
        forallTelescope ci.type fun _ concl => do
          unless concl.isAppOfArity ``Lean.Order.monotone 5 do
            throwError "Unexpecte conclusion of {name}"
          let f := concl.appArg!
          unless f.isLambda do
            throwError "Unexpecte conclusion of {name}"
          lambdaBoundedTelescope f 1 fun _ call => do
            let stx ← Lean.PrettyPrinter.delab call
            let format := Syntax.prettyPrint stx
            let str := format.pretty'
            `(Inline.code $(quote str))

      let hl : Highlighted ← constTok name name.toString
      let nameStx ← `(Inline.other {Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote name.getString!)])
      pure #[nameStx, targetStx]

    let tableStx ← mkTable rows "foo" "bar"
    return #[tableStx]
  | _, _ => throwError "Unexpected arguments"

-- #eval do
--   let (ss, _) ← (monotonicityLemmas #[] #[]).run {} (.init .missing)
--   logInfo (ss[0]!.raw.prettyPrint)
