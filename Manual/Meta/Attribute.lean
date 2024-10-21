/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Verso.Code.Highlighted

import Manual.Meta.Basic
import Manual.Meta.PPrint

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Verso.Code (highlightingJs)
open Verso.Code.Highlighted.WebAssets


open Lean Elab Parser
open Lean.Widget (TaggedText)
open SubVerso.Highlighting
open Verso.Code

namespace Manual

def Inline.attr : Inline where
  name := `Manual.attr

@[role_expander attr]
def attr : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $a:str }) := arg
      | throwErrorAt arg "Expected code literal with the attribute"
    let altStr ← parserInputString a

    match Parser.runParserCategory (← getEnv) `attr altStr (← getFileName) with
    | .error e => throwErrorAt a e
    | .ok stx =>
      match stx.getKind with
      | `Lean.Parser.Attr.simple =>
        let attrName := stx[0].getId
        throwErrorAt a "Simple: {attrName} {isAttribute (← getEnv) attrName}"
      | .str (.str (.str (.str .anonymous "Lean") "Parser") "Attr") k =>
        match getAttributeImpl (← getEnv) k.toName with
        | .error e => throwErrorAt a e
        | .ok {descr, name, ref, ..} =>
          let attrTok := a.getString
          let hl : Highlighted := attrToken ref descr attrTok
          discard <| realizeGlobalConstNoOverloadWithInfo (mkIdentFrom a ref)
          pure #[← `(Verso.Doc.Inline.other {Inline.attr with data := ToJson.toJson $(quote hl)} #[Verso.Doc.Inline.code $(quote attrTok)])]
      | other =>
      throwErrorAt a "Kind is {stx.getKind} {isAttribute (← getEnv) stx.getKind} {attributeExtension.getState (← getEnv) |>.map |>.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString) |> repr}"

where
  -- TODO: This will eventually generate the right cross-reference, but VersoManual needs to have a
  -- domain for syntax categories/kinds upstreamed to it first (and then the appropriate link target
  -- code added)
  attrToken (ref : Name) (descr : String) (tok : String) : Highlighted :=
    .token ⟨.keyword ref none (some descr), tok⟩

@[inline_extension attr]
def attr.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]
  toHtml :=
    open Verso.Output.Html Verso.Doc.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean attribute code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"
