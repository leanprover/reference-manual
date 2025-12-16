/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import Manual.Meta.ErrorExplanation
import Manual.ErrorExplanations.CtorResultingTypeMismatch
import Manual.ErrorExplanations.DependsOnNoncomputable
import Manual.ErrorExplanations.InductionWithNoAlts
import Manual.ErrorExplanations.InductiveParamMismatch
import Manual.ErrorExplanations.InductiveParamMissing
import Manual.ErrorExplanations.InferBinderTypeFailed
import Manual.ErrorExplanations.InferDefTypeFailed
import Manual.ErrorExplanations.InvalidDottedIdent
import Manual.ErrorExplanations.InvalidField
import Manual.ErrorExplanations.ProjNonPropFromProp
import Manual.ErrorExplanations.PropRecLargeElim
import Manual.ErrorExplanations.RedundantMatchAlt
import Manual.ErrorExplanations.SynthInstanceFailed
import Manual.ErrorExplanations.UnknownIdentifier

open Lean
open Verso.Doc Elab
open Verso.Genre Manual


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

#doc (Manual) "Error Explanations" =>
%%%
number := false
htmlToc := false
%%%

This section provides explanations of errors and warnings that may be generated
by Lean when processing a source file. All error names listed below have the
`lean` package prefix.

{error_explanation_table}

{include 0 Manual.ErrorExplanations.CtorResultingTypeMismatch}

{include 0 Manual.ErrorExplanations.DependsOnNoncomputable}

{include 0 Manual.ErrorExplanations.InductionWithNoAlts}

{include 0 Manual.ErrorExplanations.InductiveParamMismatch}

{include 0 Manual.ErrorExplanations.InductiveParamMissing}

{include 0 Manual.ErrorExplanations.InferBinderTypeFailed}

{include 0 Manual.ErrorExplanations.InferDefTypeFailed}

{include 0 Manual.ErrorExplanations.InvalidDottedIdent}

{include 0 Manual.ErrorExplanations.InvalidField}

{include 0 Manual.ErrorExplanations.ProjNonPropFromProp}

{include 0 Manual.ErrorExplanations.PropRecLargeElim}

{include 0 Manual.ErrorExplanations.RedundantMatchAlt}

{include 0 Manual.ErrorExplanations.SynthInstanceFailed}

{include 0 Manual.ErrorExplanations.UnknownIdentifier}
