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

@[code_block_expander markdown]
def markdown : CodeBlockExpander
  | _args, str => do
    let str ← parserInputString str
    let some ast := MD4Lean.parse str
      | throwError "Failed to parse docstring as Markdown"
    let content ← ast.blocks.mapM <|
      Markdown.blockFromMarkdown (handleHeaders := Markdown.strongEmphHeaders)
    pure #[← ``(Block.other Block.noVale #[$content,*])]
