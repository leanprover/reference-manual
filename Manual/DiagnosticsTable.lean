/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import VersoManual

import Verso.Doc
import Verso.Syntax
import MD4Lean
import Manual.Meta
import Std.Internal.Parsec.String

import Manual.ErrorExplanation
import Manual.ErrorExplanationDummyData

open Verso.Genre.Manual.InlineLean

open Verso.Genre Manual

open Std.Internal Lean Elab Term Verso Doc Elab Genre Manual Markdown MD4Lean

set_option pp.rawOnError true
set_option guard_msgs.diff true

/-
Table format:
def foo : Array (Array (Doc.Block Manual)) :=
  #[#[ Block.para  #[  Inline.text  "A1"  ] ],
    #[ Block.para  #[  Inline.text  "A2"  ] ],
    #[ Block.para  #[  Inline.text  "B1"  ] ],
    #[ Block.para  #[  Inline.text  "B2"  ] ]]
{{ Block.para  #[  Inline.text  \"A1\"  ] }*
 { Block.para  #[  Inline.text  \"A2\"  ] }*
 { Block.para  #[  Inline.text  \"B1\"  ] }*
 { Block.para  #[  Inline.text  \"B2\"  ] }}
corresponds to
A1 A2
-----
B1 B2
-/

private partial def nameOrd (name name' : Name) : Ordering:=
  match reverse name, reverse name' with
  | .num _ _, .str _ _ => .lt
  | .str _ _, .num _ _  => .gt
  | .str p s, .str p' s' => compare s s' |>.then (nameOrd p p')
  | .num p n, .num p' n' => compare n n' |>.then (nameOrd p p')
  | .anonymous, .anonymous => .eq
  | .anonymous, .str .. | .anonymous, .num .. => .lt
  | .num .., .anonymous .. | .str .., .anonymous .. => .gt
where
  reverse : Name → (xs : Name := .anonymous) → Name
  | .anonymous, acc => acc
  | .str p s, acc => reverse p (.str acc s)
  | .num p n, acc => reverse p (.num acc n)

open Verso Doc Elab
@[block_role_expander errorExplanationTable]
def errorExplanationTable : BlockRoleExpander
  | #[], #[] => do
    let entries := errorExplanationExt.getState (← getEnv) |>.toArray
    let entries := entries.qsort fun e e' => nameOrd e.1 e'.1 |>.isLT
    let columns := 4
    let header := true
    let name := "diagnostic-table"
    let alignment : Option TableConfig.Alignment := none
    -- let block ← ``(Verso.Doc.Block.ul (genre := Manual) #[
    --   Verso.Doc.ListItem.mk #[Verso.Doc.Block.para #[Doc.Inline.text "hello"]]])
    let headers ← #["", "Name", "Summary", "Since"]
      |>.mapM fun s => ``(Verso.Doc.Block.para #[Doc.Inline.text $(quote s)])
    let vals ← entries.flatMapM fun (name, explan) =>
      let icon :=
        (if explan.metadata.removedVersion.isSome then "⌛️" else "")
        ++
        (if explan.metadata.severity == .warning then "⚠️" else "❌")
      let name := toString name
      let summary := explan.metadata.summary
      let since := explan.metadata.sinceVersion
      #[icon, name, summary, since]
        |>.mapM fun s => ``(Verso.Doc.Block.para #[Doc.Inline.text $(quote s)])
    let blocks := (headers ++ vals).map fun c => Syntax.TSepArray.mk #[c]
    pure #[← ``(Block.other (Block.table $(quote columns) $(quote header) $(quote name) $(quote alignment)) #[Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])]
  | _, _ => throwError "unexpected syntax"

syntax (name:=syntaxFoo) "foo(" num ")" : block

open PartElabM in
@[part_command syntaxFoo]
def allExplanations : PartCommand
  | _ => do
    logInfo m!"elaborating foo"
    let titleString := "Explanations"
    let titleBits := #[← ``(Verso.Doc.Inline.text $(quote titleString))]
    let explans := errorExplanationExt.getState (← getEnv)
    let blocks ← liftDocElabM <| explans.toArray.flatMapM fun (name, _) =>
      return #[← ``(Block.para #[Inline.text $(quote name.toString)])]
    push {
      titleSyntax := quote (k := `str) titleString,
      expandedTitle := some (titleString, titleBits),
      metadata := none,
      blocks,
      priorParts := #[]
    }

#doc (Manual) "Diagnostic Explanations" =>

Below is the error explanation table:

{errorExplanationTable}

foo(31)

Above is the error explanation table ^

Test table:

:::table align:=left (header := true)
* row
  * A1
  * A2
* row
  * B1
  * B2
:::
