/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual
import Manual.Meta.Figure
import Lean.Elab.InfoTree.Types

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

open Lean.Doc.Syntax in
@[part_command Lean.Doc.Syntax.codeblock]
def markdown : PartCommand
  | `(block| ``` markdown | $txt ``` ) => do
     let some ast := MD4Lean.parse txt.getString
       | throwError "Failed to parse body of markdown code block"
     _ ← ast.blocks.mapM Markdown.addPartFromMarkdown
  | _ => Elab.throwUnsupportedSyntax
