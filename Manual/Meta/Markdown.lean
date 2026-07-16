/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual
import Manual.Meta.Figure
import Lean.Elab.InfoTree

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab

namespace Manual

def Block.noVale : Block where
  name := `Manual.Block.noVale

@[block_extension Block.noVale]
def Block.noVale.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="no-vale">{{← content.mapM goB}}</div>}}

/-- Closes the last-opened section, throwing an error on failure. -/
def closeEnclosingSection : PartElabM Unit := do
  -- Markdown headers carry no source extent of their own, so end the section at the end of the
  -- current reference. This keeps each part's range valid (the selection stays within
  -- `[rangeStart, endPos]`) for the TOC range conversion.
  let endPos := (← getRef).getTailPos?.getD default
  if let some ctxt' := (← getThe PartElabM.State).partContext.close endPos then
    modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
  else
    throwError m!"Failed to close the last-opened explanation part"

/-- Closes as many sections as were created by markdown processing. -/
def closeEnclosingSections (headerMapping : Markdown.HeaderMapping) : PartElabM Unit := do
  for _ in headerMapping do
    closeEnclosingSection

@[part_command Lean.Doc.Syntax.codeblock]
def markdown : PartCommand
  | `(Lean.Doc.Syntax.codeblock| ``` $markdown:ident $args*| $txt ``` ) => do
     let x ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo markdown
     if x != by exact decl_name% then Elab.throwUnsupportedSyntax
     for arg in args do
       let h ← MessageData.hint m!"Remove it" #[""] (ref? := arg)
       logErrorAt arg m!"No arguments expected{h}"
     let some ast := MD4Lean.parse txt.getString
       | throwError "Failed to parse body of markdown code block"
     let mut currentHeaderLevels : Markdown.HeaderMapping := {}
     for block in ast.blocks do
       currentHeaderLevels ← Markdown.addPartFromMarkdown block currentHeaderLevels
     closeEnclosingSections currentHeaderLevels
  | _ => Elab.throwUnsupportedSyntax
