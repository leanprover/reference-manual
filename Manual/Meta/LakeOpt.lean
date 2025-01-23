/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Verso.Code

import Manual.Meta.Basic


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets

namespace Manual

inductive LakeOptKind where
  | flag
  | option
deriving ToJson, FromJson, DecidableEq, Ord, Repr

def LakeOptKind.ns : LakeOptKind → String
  | .flag => "lake-flag"
  | .option => "lake-option"

open LakeOptKind in
instance : Quote LakeOptKind where
  quote
    | .flag => Syntax.mkCApp ``flag #[]
    | .option => Syntax.mkCApp ``option #[]

def Inline.lakeOptDef (name : String) (kind : LakeOptKind) : Inline where
  name := `Manual.lakeOptDef
  data := .arr #[.str name, toJson kind]

def Inline.lakeOpt (name : String) : Inline where
  name := `Manual.lakeOpt
  data := .str name

def lakeOptDomain := `Manual.lakeOpt

structure LakeOptDefOpts where
  kind : LakeOptKind

def LakeOptDefOpts.parse [Monad m] [MonadError m] : ArgParse m LakeOptDefOpts :=
  LakeOptDefOpts.mk <$> .positional `kind optKind
where
  optKind : ValDesc m LakeOptKind := {
    description := "'flag' or 'option'",
    get
      | .name x =>
        match x.getId with
        | `flag => pure .flag
        | `option => pure .option
        | _ => throwErrorAt x "Expected 'flag' or 'option'"
      | .num x | .str x => throwErrorAt x "Expected 'flag' or 'option'"
  }

def lakeOptCss : String :=
r#"
.lake-opt a {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
.lake-opt a:hover {
  text-decoration: currentcolor underline solid;
}
"#

@[role_expander lakeOptDef]
def lakeOptDef : RoleExpander
  | args, inlines => do
    let {kind} ← LakeOptDefOpts.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the option or flag"
    let name := name.getString.takeWhile fun c => c == '-' || c.isAlphanum

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other (Manual.Inline.lakeOptDef $(quote name) $(quote kind)) #[Inline.code $(quote name)])]

@[inline_extension lakeOptDef]
def lakeOptDef.descr : InlineDescr where
  traverse id data _ := do
    let .arr #[.str name, jsonKind] := data
      | logError s!"Failed to deserialize metadata for Lake option def: {data}"; return none
    let .ok kind := fromJson? (α := LakeOptKind) jsonKind
      | logError s!"Failed to deserialize metadata for Lake option def '{name}' kind: {jsonKind}"; return none
    modify fun s =>
      s |>.saveDomainObject lakeOptDomain name id |>.saveDomainObjectData lakeOptDomain name jsonKind

    discard <| externalTag id (← read).path (kind.ns ++ name)

    pure none

  toTeX := none

  toHtml :=
    open Verso.Output.Html in
    some <| fun goB id data content => do
      let .arr #[.str name, _jsonKind] := data
        | HtmlT.logError s!"Failed to deserialize metadata for Lake option def: {data}"; content.mapM goB

      let idAttr := (← read).traverseState.htmlId id

      pure {{<code {{idAttr}} class="lake-opt">{{name}}</code>}}


@[role_expander lakeOpt]
def lakeOpt : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the option or flag"
    let name := name.getString

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other (Manual.Inline.lakeOpt $(quote name)) #[Inline.code $(quote name)])]

@[inline_extension lakeOpt]
def lakeOpt.descr : InlineDescr where
  traverse _ _ _ := do
    pure none

  toTeX := none

  extraCss := [lakeOptCss]

  toHtml :=
    open Verso.Output.Html in
    some <| fun goB id data content => do
      let .str name := data
        | HtmlT.logError s!"Failed to deserialize metadata for Lake option ref: {data}"; content.mapM goB

      if let some obj := (← read).traverseState.getDomainObject? lakeOptDomain name then
        for id in obj.ids do
          if let some (path, slug) := (← read).traverseState.externalTags[id]? then
            let url := path.link (some slug.toString)
            return {{<code class="lake-opt"><a href={{url}} class="lake-command">{{name}}</a></code>}}

      pure {{<code class="lake-opt">{{name}}</code>}}
