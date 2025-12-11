/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import Manual.Meta.ErrorExplanation
import Lean

open Verso Doc Elab Genre Manual
open Lean




namespace Manual

set_option pp.rawOnError true
set_option guard_msgs.diff true

set_option manual.requireErrorExplanations false

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
    let some { path, htmlId } := xref.externalTags.get? id
      | logError s!"Could not find external tag for error explanation '{name}' corresponding to ID '{id}'"
        content.mapM go
    let addr := path.link (some htmlId.toString)
    pure {{<a class="technical-term" href={{addr}}>{{← content.mapM go}}</a>}}


/- Renders the suffix of an error explanation, allowing line breaks before capital letters. -/
inline_extension Inline.errorExplanationShortName (errorName : Name) where
  data := toJson (getBreakableSuffix errorName)
  traverse := fun _ _ _ => pure none
  extraCss := [".error-explanation-short-name { hyphenate-character: ''; }"]
  toTeX := none
  toHtml := some fun _go _id info _content =>
    open Verso.Output Html in do
    let .ok (some errorName) := fromJson? (α := Option String) info
      | HtmlT.logError "Invalid data for explanation name element"
        pure .empty
    let html := {{ <code class="error-explanation-short-name">{{errorName}}</code> }}
    return html

@[block_command]
def error_explanation_table : BlockCommandOf Unit
  | () => do
    let entries ← getErrorExplanationsSorted
    let columns := 4
    let header := true
    let name := "error-explanation-table"
    let alignment : Option TableConfig.Alignment := none
    let headers ← #["Name", "Summary", "Severity", "Since"]
      |>.mapM fun s => ``(Verso.Doc.Block.para #[Inline.text $(quote s)])
    let vals ← entries.flatMapM fun (name, explan) => do
      let sev := quote <| if explan.metadata.severity == .warning then "Warning" else "Error"
      let sev ← ``(Inline.text $sev)
      let nameLink ← ``(Inline.other (Inline.errorExplanationLink $(quote name))
        #[Inline.other (Inline.errorExplanationShortName $(quote name)) #[]])
      let summary ← ``(Inline.text $(quote explan.metadata.summary))
      let since ← ``(Inline.text $(quote explan.metadata.sinceVersion))
      #[nameLink, summary, sev, since]
        |>.mapM fun s => ``(Verso.Doc.Block.para #[$s])
    let blocks := (headers ++ vals).map fun c => Syntax.TSepArray.mk #[c]
    ``(Block.other (Block.table $(quote columns) $(quote header) $(quote name) $(quote alignment)) #[Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])

-- Elaborating explanations can exceed the default heartbeat maximum:
set_option maxHeartbeats 1000000

#doc (Manual) "Error Explanations" =>
%%%
number := false
htmlToc := false
%%%

This section provides explanations of errors and warnings that may be generated
by Lean when processing a source file. All error names listed below have the
`lean` package prefix.

{error_explanation_table}

{make_explanations}
