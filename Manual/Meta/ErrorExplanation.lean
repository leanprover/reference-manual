/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import VersoManual
import Manual.Meta
import Manual.Meta.ErrorExplanation.Example
import Manual.Meta.ErrorExplanation.Header

open Lean
open Verso.Doc
open Verso.Genre.Manual
open Elab

namespace Manual

/--
Returns the suffix of `name` as a string containing soft-hyphen characters at reasonable split points.
-/
def getBreakableSuffix (name : Name) : Option String := do
  let suffix ← match name with
    | .str _ s => s
    | .num _ n => toString n
    | .anonymous => none
  let breakableHtml := softHyphenateText false suffix
  htmlText breakableHtml
where
  htmlText : Verso.Output.Html → String
    | .text _ txt => txt
    | .seq elts => elts.foldl (· ++ htmlText ·) ""
    | .tag _nm _attrs children => htmlText children


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

/--
Renders a table-of-contents like summary of the error explanations defined by the current Lean
implementation.
-/
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
      let nameLink ←
        ``(Inline.other (Inline.ref $(quote name.toString) $(quote errorExplanationDomain) Option.none)
          #[Inline.other (Inline.errorExplanationShortName $(quote name)) #[]])
      let summary ← ``(Inline.text $(quote explan.metadata.summary))
      let since ← ``(Inline.text $(quote explan.metadata.sinceVersion))
      #[nameLink, summary, sev, since]
        |>.mapM fun s => ``(Verso.Doc.Block.para #[$s])
    let blocks := (headers ++ vals).map fun c => Syntax.TSepArray.mk #[c]
    ``(Block.other (Block.table $(quote columns) $(quote header) $(quote name) $(quote alignment)) #[Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])
