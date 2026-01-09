/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual
import Lean.Elab.InfoTree.Types

import Manual.Meta.Basic

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab



namespace Manual

def Block.shieldList : Block where
  name := `Manual.shieldList
  data := .null

@[directive_expander shieldList]
def shieldList : DirectiveExpander
  | _args, contents => do
    let blocks ← contents.mapM elabBlock
    -- Figures are represented using the first block to hold the caption. Storing it in the JSON
    -- entails repeated (de)serialization.
    pure #[← ``(Block.other Block.shieldList #[$blocks,*])]

@[block_extension shieldList]
def shieldList.descr : BlockDescr where
  traverse _id _data _contents := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← goB b, .raw "\n"]
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun _goI goB _id _data blocks => do
      pure {{
        <div class="shieldList">
          {{← blocks.mapM goB}}
        </div>
      }}
  extraCss := [r##".shieldList li::marker { content: "🛡️ "; font-size: 1.2em; }"##]
