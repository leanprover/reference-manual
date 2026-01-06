/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Lean.Data.Json

open Verso Doc Elab Output Html Code
open Verso.Genre Manual
open Verso.ArgParse
open Lean

namespace Manual

block_extension Block.customCSS (css : String) where
  data := toJson css
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize CSS while rendering HTML: " ++ err
        pure .empty
      | .ok (css : String) =>
        pure {{
          <style>{{css}}</style>
        }}

@[code_block]
def customCSS : CodeBlockExpanderOf Unit
  | (), str =>
    `(Block.other (Block.customCSS $(quote str.getString)) #[])
