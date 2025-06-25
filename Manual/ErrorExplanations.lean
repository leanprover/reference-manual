/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import Manual.Meta.ErrorExplanation

open Lean
open Verso Doc Elab Genre Manual

namespace Manual

set_option pp.rawOnError true
set_option guard_msgs.diff true


inline_extension Inline.errorExplanationLink (errorName : Name) where
  data := toJson errorName
  traverse := fun _ _ _ => pure none
  toTeX  := none
  toHtml := some fun go _ data content =>
    open Verso.Output.Html Verso.Doc.Html.HtmlT in do
    let xref ← state
    let .ok name := FromJson.fromJson? (α := String) data
      | logError s!"Failed to parse error explanation link JSON: expected string, but found:\n{data}"
        content.mapM go
    let some obj := (← read).traverseState.getDomainObject? errorExplanationDomain name
      | logError s!"Could not find explanation domain entry for name '{name}'"
        content.mapM go
    let some id := obj.getId
      | logError s!"Could not find retrieve ID from explanation domain entry for name '{name}'"
        content.mapM go
    if let some { path, htmlId } := xref.externalTags.get? id then
      let addr := path.link (some htmlId.toString)
      pure {{<a class="technical-term" href={{addr}}>{{← content.mapM go}}</a>}}
    else
      logError s!"Could not find external tag for error explanation '{name}' corresponding to ID '{id}'"
      content.mapM go

@[block_role_expander error_explanation_table]
def error_explanation_table : BlockRoleExpander
  | #[], #[] => do
    let entries ← getErrorExplanationsSorted
    let columns := 4
    let header := true
    let name := "diagnostic-table"
    let alignment : Option TableConfig.Alignment := none
    let headers ← #["Name", "Summary", "Severity", "Since"]
      |>.mapM fun s => ``(Verso.Doc.Block.para #[Doc.Inline.text $(quote s)])
    let vals ← entries.flatMapM fun (name, explan) => do
      let sev := quote <|
        if explan.metadata.severity == .warning then "Warning" else "Error"
      let sev ← ``(Doc.Inline.text $sev)
      let nameStr := toString name
      let nameLink ← ``(Doc.Inline.other (Inline.errorExplanationLink $(quote name)) #[Doc.Inline.text $(quote nameStr)])
      let summary ← ``(Doc.Inline.text $(quote explan.metadata.summary))
      let since ← ``(Doc.Inline.text $(quote explan.metadata.sinceVersion))
      #[nameLink, summary, sev, since]
        |>.mapM fun s => ``(Verso.Doc.Block.para #[$s])
    let blocks := (headers ++ vals).map fun c => Syntax.TSepArray.mk #[c]
    pure #[← ``(Block.other (Block.table $(quote columns) $(quote header) $(quote name) $(quote alignment)) #[Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])]
  | _, _ => throwError "unexpected syntax"

-- Elaborating explanations can exceed the default heartbeat maximum:
set_option maxHeartbeats 1000000

#doc (Manual) "Error Explanations" =>
%%%
number := false
htmlToc := false
%%%

This section provides explanations of errors and warnings that may be generated
by Lean when processing a source file.

{error_explanation_table}

{make_explanations}
