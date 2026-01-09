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

def Block.listBullet (bullet : String) : Block where
  name := `Manual.listBullet
  data := .str bullet

@[directive_expander listBullet]
def listBullet : DirectiveExpander
  | args, contents => do
    let bullet ← ArgParse.run (.positional `bullet .string) args
    let blocks ← contents.mapM elabBlock
    pure #[← ``(Block.other (Block.listBullet $(quote bullet)) #[$blocks,*])]

@[block_extension listBullet]
def listBullet.descr : BlockDescr where
  traverse _id _data _contents := pure none
  toTeX := none
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun _goI goB _id data blocks => do
      let bullet ←
        match data with
        | .str bullet => pure bullet
        | _ =>
          HtmlT.logError "Invalid data for listBullet block"
          pure ""
      pure {{
        <div class="listBullet" style=s!"--bullet: '{bullet} ';">
          {{← blocks.mapM goB}}
        </div>
      }}
  extraCss := [r##".listBullet li::marker { content: var(--bullet); font-size: 1.2em; }"##]
