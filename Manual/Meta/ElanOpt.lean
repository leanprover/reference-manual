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


-- TODO: this is copied from LakeOpt for reasons of expediency. Factor out the common parts to a library!

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets

namespace Manual

inductive ElanOptKind where
  | flag
  | option
deriving ToJson, FromJson, DecidableEq, Ord, Repr

def ElanOptKind.ns : ElanOptKind → String
  | .flag => "elan-flag"
  | .option => "elan-option"

open ElanOptKind in
instance : Quote ElanOptKind where
  quote
    | .flag => Syntax.mkCApp ``flag #[]
    | .option => Syntax.mkCApp ``option #[]

def Inline.elanOptDef (name : String) (kind : ElanOptKind) (argMeta : Option String) : Inline where
  name := `Manual.elanOptDef
  data := .arr #[.str name, toJson kind, toJson argMeta]

def Inline.elanOpt (name : String) (original : String) : Inline where
  name := `Manual.elanOpt
  data := .arr #[.str name, .str original]

def elanOptDomain := `Manual.elanOpt

structure ElanOptDefOpts where
  kind : ElanOptKind

def ElanOptDefOpts.parse [Monad m] [MonadError m] : ArgParse m ElanOptDefOpts :=
  ElanOptDefOpts.mk <$> .positional `kind optKind
where
  optKind : ValDesc m ElanOptKind := {
    description := "'flag' or 'option'",
    signature := .Ident
    get
      | .name x =>
        match x.getId with
        | `flag => pure .flag
        | `option => pure .option
        | _ => throwErrorAt x "Expected 'flag' or 'option'"
      | .num x | .str x => throwErrorAt x "Expected 'flag' or 'option'"
  }

def elanOptCss : String :=
r#"
.elan-opt a {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
.elan-opt a:hover {
  text-decoration: currentcolor underline solid;
}
"#

@[role_expander elanOptDef]
def elanOptDef : RoleExpander
  | args, inlines => do
    let {kind} ← ElanOptDefOpts.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the option or flag"
    let origName := name.getString
    let name := origName.takeWhile fun c => c == '-' || c.isAlphanum
    let valMeta := origName.drop name.length |>.dropWhile fun c => !c.isAlphanum

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other (Manual.Inline.elanOptDef $(quote name) $(quote kind) $(quote (if valMeta.isEmpty then none else some valMeta : Option String))) #[Inline.code $(quote name)])]

open Verso.Search in
def elanOptDomainMapper : DomainMapper :=
  DomainMapper.withDefaultJs elanOptDomain "Elan Command-Line Option" "elan-option-domain" |>.setFont { family := .code }

@[inline_extension elanOptDef]
def elanOptDef.descr : InlineDescr where
  init s := s.addQuickJumpMapper elanOptDomain elanOptDomainMapper

  traverse id data _ := do
    let .arr #[.str name, jsonKind, _] := data
      | logError s!"Failed to deserialize metadata for Elan option def: {data}"; return none
    let .ok kind := fromJson? (α := ElanOptKind) jsonKind
      | logError s!"Failed to deserialize metadata for Elan option def '{name}' kind: {jsonKind}"; return none
    modify fun s =>
      s |>.saveDomainObject elanOptDomain name id |>.saveDomainObjectData elanOptDomain name jsonKind

    discard <| externalTag id (← read).path (kind.ns ++ name)

    pure none

  toTeX := none

  toHtml :=
    open Verso.Output.Html in
    some <| fun goB id data content => do
      let .arr #[.str name, _jsonKind, metadata] := data
        | HtmlT.logError s!"Failed to deserialize metadata for Elan option def: {data}"; content.mapM goB

      let idAttr := (← read).traverseState.htmlId id

      let .ok metadata := FromJson.fromJson? (α := Option String) metadata
        | HtmlT.logError s!"Failed to deserialize argument metadata for Elan option def: {metadata}"; content.mapM goB

      if let some mv := metadata then
        pure {{<code {{idAttr}} class="elan-opt">{{name}}" "{{mv}}</code>}}
      else
        pure {{<code {{idAttr}} class="elan-opt">{{name}}</code>}}

  localContentItem _ info _ := open Verso.Output.Html in do
    if let .arr #[.str name, _jsonKind, _meta] := info then
      pure #[(name, {{<code>{{name}}</code>}})]
    else throw s!"Expected three-element array with string first, got {info}"


@[role_expander elanOpt]
def elanOpt : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the option or flag"
    let optName := name.getString.takeWhile fun c => c == '-' || c.isAlphanum

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other (Manual.Inline.elanOpt $(quote optName) $(quote name.getString)) #[Inline.code $(quote name.getString)])]

@[inline_extension elanOpt]
def elanOpt.descr : InlineDescr where
  traverse _ _ _ := do
    pure none

  toTeX := none

  extraCss := [elanOptCss]

  toHtml :=
    open Verso.Output.Html in
    some <| fun goB _id data content => do
      let .arr #[.str name, .str original] := data
        | HtmlT.logError s!"Failed to deserialize metadata for Elan option ref: {data}"; content.mapM goB

      if let some obj := (← read).traverseState.getDomainObject? elanOptDomain name then
        for id in obj.ids do
          if let some dest := (← read).traverseState.externalTags[id]? then
            return {{<code class="elan-opt"><a href={{dest.link}} class="elan-command">{{name}}</a>{{original.drop name.length}}</code>}}

      pure {{<code class="elan-opt">{{original}}</code>}}
