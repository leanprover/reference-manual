/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Verso.Code.Highlighted

import Manual.Meta.Basic
import Manual.Meta.PPrint
import Manual.Meta.Syntax

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Verso.Code (highlightingJs)
open Verso.Code.Highlighted.WebAssets

open scoped Lean.Doc.Syntax


open Lean Elab Parser
open Lean.Widget (TaggedText)
open SubVerso.Highlighting
open Verso.Code

namespace Manual

def Inline.attr : Inline where
  name := `Manual.attr

open Lean Parser in
/--
The syntax kind of the unique production in the `attr` category whose leading token is `tok`.

Attributes such as `export` require arguments, so their bare names don't parse as complete attribute
syntax. When the leading token identifies a single production, this returns that production's kind,
which is enough to refer to the attribute and link to its documented syntax.
-/
def attrSyntaxKind? (env : Environment) (tok : String) : Option Name := Id.run do
  let some cat := getCategory (parserExtension.getState env).categories `attr
    | return none
  let tok := tok.trimAscii
  let mut kinds : Array Name := #[]
  for (tk, prods) in cat.tables.leadingTable do
    let tkStr :=
      match tk with
      | .str .anonymous s => s.trimAscii
      | _ => tk.toString
    if tkStr == tok then
      for (p, _) in prods do
        for (k, _) in (p.info.collectKinds {}).toList do
          if cat.kinds.contains k && !kinds.contains k then
            kinds := kinds.push k
  match kinds with
  | #[k] => some k
  | _ => none

@[role_expander attr]
def attr : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $a:str )) := arg
      | throwErrorAt arg "Expected code literal with the attribute"
    let altStr ← parserInputString a

    match Parser.runParserCategory (← getEnv) `attr altStr (← getFileName) with
    | .error e =>
      -- Attributes whose syntax requires arguments (e.g. `export`) don't parse from their bare name.
      -- When the name is a leading token, refer to that syntax and link to its docs.
      match attrSyntaxKind? (← getEnv) a.getString with
      | some kind =>
        let kindDoc ← findDocString? (← getEnv) kind
        pure #[← `(Verso.Doc.Inline.other { Inline.keywordOf with
          data :=
            ToJson.toJson (α := String × Option Name × Name × Option String)
              ($(quote a.getString), $(quote (some `attr)), $(quote kind), $(quote kindDoc))
        } #[Verso.Doc.Inline.code $(quote a.getString)])]
      | none => throwErrorAt a e
    | .ok stx =>
      let attrName ←
        match stx.getKind with
        | `Lean.Parser.Attr.simple => pure stx[0].getId
        | .str (.str (.str (.str .anonymous "Lean") "Parser") "Attr") k => pure k.toName
        | .str (.str (.str .anonymous "Lean") "Attr") k => pure k.toName
        | other =>
          let allAttrs := attributeExtension.getState (← getEnv) |>.map |>.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString)
          throwErrorAt a "Failed to process attribute kind: {stx.getKind} {isAttribute (← getEnv) stx.getKind} {allAttrs |> repr}"
      match getAttributeImpl (← getEnv) attrName with
      | .error e => throwErrorAt a e
      | .ok {descr, name, ref, ..} => do
        let attrTok := a.getString
        let hl : Highlighted := attrToken ref descr attrTok
        try
          -- Attempt to add info to the document source for go-to-def and the like, but this doesn't
          -- work for all attributes (e.g. `csimp`)
          discard <| realizeGlobalConstNoOverloadWithInfo (mkIdentFrom a ref)
        catch _ =>
          pure ()
        pure #[← `(Verso.Doc.Inline.other {Inline.attr with data := ToJson.toJson $(quote hl)} #[Verso.Doc.Inline.code $(quote attrTok)])]

where
  -- TODO: This will eventually generate the right cross-reference, but VersoManual needs to have a
  -- domain for syntax categories/kinds upstreamed to it first (and then the appropriate link target
  -- code added)
  attrToken (ref : Name) (descr : String) (tok : String) : Highlighted :=
    .token ⟨.keyword ref none (some descr), tok⟩

def Inline.attrs : Inline where
  name := `Manual.attrs

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
        reportError <| "Couldn't deserialize Lean attribute code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Manual) "examples"

/--
Shows a collection of applied attributes
-/
@[role_expander attrs]
def attrs : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $a:str )) := arg
      | throwErrorAt arg "Expected code literal with the attribute application syntax"
    let altStr ← parserInputString a

    let p := andthenFn whitespace Lean.Parser.Term.attributes.fn
    let `(Term.attributes|@[%$s$insts,*]%$e) ← withRef a <| p.parseString altStr
      | throwErrorAt a "Didn't match syntax"

    let mut hl : Highlighted := .empty
    let text ← getFileMap
    for stx in (insts : Array Syntax) do
      let `(Lean.Parser.Term.attrInstance | $[$scopedOrLocal]? $stx:attr) := stx
        | throwErrorAt stx "Didn't parse attribute instance"
      let stx := stx.raw
      let attrName ←
        match stx.getKind with
        | `Lean.Parser.Attr.simple => pure stx[0].getId
        | .str (.str (.str (.str .anonymous "Lean") "Parser") "Attr") k => pure k.toName
        | .str (.str (.str .anonymous "Lean") "Attr") k => pure k.toName
        | other =>
          let allAttrs := attributeExtension.getState (← getEnv) |>.map |>.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString)
          throwErrorAt a "Failed to process attribute kind: {stx.getKind} {isAttribute (← getEnv) stx.getKind} {allAttrs |> repr}"
      match getAttributeImpl (← getEnv) attrName with
      | .error e => throwErrorAt a e
      | .ok {descr, name, ref, ..} =>
        let mod : Highlighted :=
          if let some tok := scopedOrLocal then
            let ⟨s, e⟩ := tok.raw.getRange?.get!
            let str := s.extract text.source e
            .token ⟨.keyword none none none, str⟩ ++ .text " "
          else .empty

        let ⟨s, e⟩ := stx.getRange?.get!
        let attrTok := s.extract text.source e

        unless hl.isEmpty do hl := hl ++ mod ++ .token ⟨.keyword ``Term.attributes none none, ", "⟩
        hl := hl ++ attrToken ref descr attrTok
        try
          -- Attempt to add info to the document source for go-to-def and the like, but this doesn't
          -- work for all attributes (e.g. `csimp`)
          discard <| realizeGlobalConstNoOverloadWithInfo (mkIdentFrom a ref)
        catch _ =>
          pure ()
    hl := .token ⟨.keyword ``Term.attributes none none, "@["⟩ ++ hl ++ .token ⟨.keyword ``Term.attributes none none, "]"⟩
    pure #[← `(Verso.Doc.Inline.other {Inline.attrs with data := ToJson.toJson $(quote hl)} #[Verso.Doc.Inline.code $(quote a.getString)])]

where
  -- TODO: This will eventually generate the right cross-reference, but VersoManual needs to have a
  -- domain for syntax categories/kinds upstreamed to it first (and then the appropriate link target
  -- code added)
  attrToken (ref : Name) (descr : String) (tok : String) : Highlighted :=
    .token ⟨.keyword ref none (some descr), tok⟩

@[inline_extension attrs]
def attrs.descr : InlineDescr where
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
        reportError <| "Couldn't deserialize Lean attribute code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Manual) "examples"
