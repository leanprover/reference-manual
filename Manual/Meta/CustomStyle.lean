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


def Block.CSS : Block where
  name := `Manual.CSS

@[code_block_expander CSS]
def CSS : CodeBlockExpander
  | args, str => do
    let () ← ArgParse.done.run args
    pure #[← `(Doc.Block.other {Block.CSS with data := ToJson.toJson (α := String) $(quote str.getString)} #[])]

@[block_extension Manual.CSS]
def CSS.descr : BlockDescr where
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
