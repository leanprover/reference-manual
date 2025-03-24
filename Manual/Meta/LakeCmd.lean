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

import SubVerso.Highlighting
import SubVerso.Examples

import Manual.Meta.Basic
import Manual.Meta.Lean.Scopes
import Manual.Meta.Lean.Block


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

namespace CommandSpec
mutual
  inductive Item where
    | metavar (name : String)
    | literalSyntax (string : String)
    | ellipses
    | optional (contents : List DecoratedItem)
    | or
  deriving ToJson, FromJson, Repr
  structure DecoratedItem where
    leading : String
    item : Item
    trailing : String
  deriving ToJson, FromJson, Repr
end

mutual
  partial def Item.toHighlighted : Item → Highlighted
    | .metavar x => .token ⟨.var ⟨x.toName⟩ x, x⟩ -- Hack: abusing FVarId here
    | .literalSyntax s => .token ⟨.keyword none none none, s⟩
    | .ellipses => .token ⟨.unknown, "..."⟩
    | .or => .token ⟨.keyword none none none, "|"⟩
    | .optional xs =>
      .token ⟨.keyword none none none, "["⟩ ++
      .seq (xs.toArray.map DecoratedItem.toHighlighted) ++
      .token ⟨.keyword none none none, "]"⟩

  partial def DecoratedItem.toHighlighted : DecoratedItem → Highlighted
    | ⟨l, x, r⟩ => .text l ++ x.toHighlighted ++ .text r
end

open Syntax (mkCApp)

private def quoteList [Quote α `term] : List α → Term
  | []      => mkCIdent ``List.nil
  | (x::xs) => Syntax.mkCApp ``List.cons #[quote x, quoteList xs]

mutual
  partial def Item.quote : Item → Term
    | .metavar x => mkCApp ``Item.metavar #[Quote.quote x]
    | .literalSyntax s => mkCApp ``Item.literalSyntax #[Quote.quote s]
    | .ellipses => mkCApp ``Item.ellipses #[]
    | .or => mkCApp ``Item.or #[]
    | .optional xs =>
      have : Quote DecoratedItem := ⟨DecoratedItem.quote⟩
      mkCApp ``Item.optional #[quoteList xs]

  partial def DecoratedItem.quote : DecoratedItem → Term
    | ⟨l, i, t⟩ => mkCApp ``DecoratedItem.mk #[quote l, i.quote, quote t]
end

instance : Quote Item := ⟨Item.quote⟩
instance : Quote DecoratedItem := ⟨DecoratedItem.quote⟩

end CommandSpec


abbrev CommandSpec : Type := List CommandSpec.DecoratedItem

def CommandSpec.toHighlighted (spec : CommandSpec) : Highlighted := .seq (spec.map (·.toHighlighted)).toArray

declare_syntax_cat lake_cmd_spec_item
syntax ident : lake_cmd_spec_item
syntax str : lake_cmd_spec_item
syntax "..." : lake_cmd_spec_item
syntax "|" : lake_cmd_spec_item
syntax "[" lake_cmd_spec_item+ "]" : lake_cmd_spec_item

declare_syntax_cat lake_cmd_spec
syntax lake_cmd_spec_item* : lake_cmd_spec

mutual
  partial def CommandSpec.Item.ofSyntax (stx : TSyntax `lake_cmd_spec_item) : Except String CommandSpec.Item :=
    match stx with
    | `(lake_cmd_spec_item|$i:ident) => pure <| .metavar <| i.getId.toString (escape := false)
    | `(lake_cmd_spec_item|$s:str) => pure <| .literalSyntax s.getString
    | `(lake_cmd_spec_item|...) => pure <| .ellipses
    | `(lake_cmd_spec_item||) => pure <| .or
    | `(lake_cmd_spec_item|[ $items* ]) => .optional <$> items.toList.mapM DecoratedItem.ofSyntax
    | _ => .error s!"Not a command spec item: {stx}"

  partial def CommandSpec.DecoratedItem.ofSyntax
      (stx : TSyntax `lake_cmd_spec_item) : Except String CommandSpec.DecoratedItem := do
    return ⟨lead stx.raw.getHeadInfo, ← Item.ofSyntax stx, trail stx.raw.getTailInfo⟩
  where
    lead : SourceInfo → String
      | .original l .. => l.toString
      | _ => ""

    trail : SourceInfo → String
      | .original _ _ t _ => t.toString
      | _ => ""
end

def CommandSpec.ofSyntax (stx : Syntax) : Except String CommandSpec :=
  match stx with
  | `(lake_cmd_spec|$items:lake_cmd_spec_item*) => do
      items.toList.mapM DecoratedItem.ofSyntax
  | _ => .error s!"Not a command spec: {stx}"

structure LakeCommandOptions where
  name : List Name
  spec : StrLit
  -- This only allows one level of subcommand, but it's sufficient for Lake as it is today
  aliases : List Name

partial def LakeCommandOptions.parse [Monad m] [MonadError m] : ArgParse m LakeCommandOptions :=
  LakeCommandOptions.mk <$>
    many1 (.positional `name .name) <*>
    (.positional `spec strLit <|>
     (pure (Syntax.mkStrLit ""))) <*>
    many (.named `alias .name false)

where
  many {α} (p : ArgParse m α) : ArgParse m (List α) :=
    ((· :: ·) <$> p <*> many p) <|> pure []

  many1 {α} (p : ArgParse m α) : ArgParse m (List α) :=
    (· :: ·) <$> p <*> many p

  strLit : ValDesc m StrLit := {
    description := "string literal containing a Lake command spec",
    get
      | .str s => pure s
      | other => throwError "Expected string, got {repr other}"
  }

def Block.lakeCommand (name : String) (aliases : List String) (spec : CommandSpec) : Block where
  name := `Manual.Block.lakeCommand
  data := Json.arr #[Json.str name, toJson aliases, toJson spec]

def Inline.lakeMeta : Inline where
  name := `Manual.lakeMeta
  data := .arr #[.null, .null]

def Inline.lakeArgs (hl : Highlighted) : Inline where
  name := `Manual.lakeArgs
  data := .arr #[toJson hl, .null]

def Inline.lake : Inline where
  name := `Manual.lake
  data := .null


private partial def addLakeMetaInline (name : String) : Doc.Inline Verso.Genre.Manual → Doc.Inline Verso.Genre.Manual
  | .other i xs =>
    if i.name == Inline.lakeMeta.name || i.name == `Manual.lakeArgs then
      if let Json.arr #[mn, _] := i.data then
        .other {i with data := .arr #[mn, .str name]} <| xs.map (addLakeMetaInline name)
      else
        .other i <| xs.map (addLakeMetaInline name)
    else
      .other i <| xs.map (addLakeMetaInline name)
  | .concat xs => .concat <| xs.map (addLakeMetaInline name)
  | .emph xs => .emph <| xs.map (addLakeMetaInline name)
  | .bold xs => .bold <| xs.map (addLakeMetaInline name)
  | .image alt url => .image alt url
  | .math t txt => .math t txt
  | .footnote x xs => .footnote x (xs.map (addLakeMetaInline name))
  | .link xs url => .link (xs.map (addLakeMetaInline name)) url
  | .code s => .code s
  | .linebreak str => .linebreak str
  | .text str => .text str

private partial def addLakeMetaBlock (name : String) : Doc.Block Verso.Genre.Manual → Doc.Block Verso.Genre.Manual
  | .para xs => .para (xs.map (addLakeMetaInline name))
  | .other b xs => .other b (xs.map (addLakeMetaBlock name))
  | .concat xs => .concat (xs.map (addLakeMetaBlock name))
  | .blockquote xs => .blockquote (xs.map (addLakeMetaBlock name))
  | .code s => .code s
  | .dl items => .dl (items.map fun ⟨xs, ys⟩ => ⟨xs.map (addLakeMetaInline name), ys.map (addLakeMetaBlock name)⟩)
  | .ul items => .ul (items.map fun ⟨ys⟩ => ⟨ys.map (addLakeMetaBlock name)⟩)
  | .ol n items => .ol n (items.map fun ⟨ys⟩ => ⟨ys.map (addLakeMetaBlock name)⟩)


@[directive_expander lake]
def lake : DirectiveExpander
  | args, contents => do
    let {name, spec, aliases} ← LakeCommandOptions.parse.run args
    let spec ←
      if spec.getString.trim.isEmpty then
        pure []
      else
        match Parser.runParserCategory (← getEnv) `lake_cmd_spec spec.getString (← getFileName) with
        | .error e => throwErrorAt spec e
        | .ok stx =>
          match CommandSpec.ofSyntax stx with
          | .error e => throwErrorAt spec e
          | .ok spec => pure spec
    let contents ← contents.mapM fun b => do
      ``(addLakeMetaBlock $(quote <| String.intercalate "~~" (name.map (·.toString (escape := false)))) $(← elabBlock b))
    pure #[← ``(Verso.Doc.Block.other (Block.lakeCommand $(quote <| String.intercalate " " <| name.map (·.toString (escape := false))) $(quote <| aliases.map (·.toString (escape := false))) $(quote spec)) #[$contents,*])]

def lakeCommandDomain : Name := `Manual.lakeCommand

open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension Block.lakeCommand]
def lakeCommand.descr : BlockDescr where
  init st := st
    |>.setDomainTitle lakeCommandDomain "Lake commands"
    |>.setDomainDescription lakeCommandDomain "Detailed descriptions of Lake commands"

  traverse id info _ := do
    let Json.arr #[Json.str name, aliases, _] := info
      | do logError s!"Failed to deserialize data while traversing a Lake command, expected 3-element array startign with string but got {info}"; pure none
    let aliases : List String ←
      match fromJson? (α := List String) aliases with
      | .ok v => pure v
      | .error e =>
        logError s!"Failed to deserialize aliases while traversing a Lake command: {e}"; pure []
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name
    Index.addEntry id {term := Doc.Inline.concat #[.code name, .text " (Lake command)"]}
    modify fun st => st.saveDomainObject lakeCommandDomain name id
    for a in aliases do
      modify fun st => st.saveDomainObject lakeCommandDomain a id
    pure none

  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let Json.arr #[ Json.str name, aliases, spec] := info
        | do Verso.Doc.Html.HtmlT.logError s!"Failed to deserialize data while making HTML for Lake command, got {info}"; pure .empty
      let .ok (aliases : List String) := FromJson.fromJson? aliases
        | do Verso.Doc.Html.HtmlT.logError s!"Failed to deserialize aliases while making HTML for Lake command, got {spec}"; pure .empty
      let .ok (spec : CommandSpec) := FromJson.fromJson? spec
        | do Verso.Doc.Html.HtmlT.logError s!"Failed to deserialize spec while making HTML for Lake command, got {spec}"; pure .empty

      let lakeTok : Highlighted := .token ⟨.keyword none none none, "lake"⟩
      let nameTok : Highlighted := .token ⟨.keyword none none none, name⟩
      let spec : Highlighted := spec.toHighlighted

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      let aliasHtml : Html :=
        match aliases with
        | [] => .empty
        | _::more => {{
            <p>
              <strong>{{if more.isEmpty then "Alias:" else "Aliases:"}}</strong>
              " "
              {{aliases.map (fun (a : String) => {{<code>s!"lake {a}"</code>}}) |>.intersperse {{", "}}}}
            </p>
          }}

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"Lake command"</span>
          <pre class="signature hl lean block" data-lean-context={{name}}>
            {{← (Highlighted.seq #[lakeTok, .text " ", nameTok, .text " ", spec]).toHtml}}
          </pre>
          <div class="text">
            {{aliasHtml}}
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := none
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]
  localContentItem _ info _ := open Verso.Output.Html in do
    if let Json.arr #[ Json.str name, _, _] := info then
      let str := s!"lake {name}"
      pure #[(str, {{<code>{{str}}</code>}})]
    else throw s!"Expected a three-element array with a string first, got {info}"

@[role_expander lakeMeta]
def lakeMeta : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $mName:str )) := arg
      | throwErrorAt arg "Expected code literal with the metavariable"
    let mName := mName.getString

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other {Manual.Inline.lakeMeta with data := Json.arr #[$(quote mName), .null]} #[Inline.code $(quote mName)])]

@[inline_extension lakeMeta]
def lakeMeta.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let (mName, ctx) :=
        match data with
        | .arr #[.str mName, .str cmdName] =>
          (mName, some cmdName)
        | .arr #[.str mName, _] =>
          (mName, none)
        | _ => ("", none)
      let hl : Highlighted := .token ⟨.var ⟨mName.toName⟩ mName, mName⟩
      hl.inlineHtml ctx


@[role_expander lake]
def lakeInline : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $cmdName:str )) := arg
      | throwErrorAt arg "Expected code literal with the Lake command name"
    let name := cmdName.getString

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other {Manual.Inline.lake with data := $(quote name)} #[Inline.code $(quote name)])]

@[inline_extension lake]
def lake.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [
r#"
a.lake-command {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
a.lake-command:hover {
  text-decoration: currentcolor underline solid;
}

"#
]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ data is => do
      let (name) :=
        match data with
        | .str x => some x
        | _ => none

      if let some n := name then
        if let some dest := (← read).traverseState.getDomainObject? lakeCommandDomain n then
          for id in dest.ids do
            if let some (path, slug) := (← read).traverseState.externalTags[id]? then
              let url := path.link (some slug.toString)
              return {{<a href={{url}} class="lake-command"><code>s!"lake {n}"</code></a>}}

      HtmlT.logError "No name for lake command"
      is.mapM goI

@[role_expander lakeArgs]
def lakeArgs : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $spec:str )) := arg
      | throwErrorAt arg "Expected code literal with the Lake command name"

    match Parser.runParserCategory (← getEnv) `lake_cmd_spec spec.getString (← getFileName) with
    | .error e => throwErrorAt spec e
    | .ok stx =>
      match CommandSpec.ofSyntax stx with
      | .error e => throwErrorAt spec e
      | .ok spec =>
        let hl := spec.toHighlighted
        pure #[← ``(Verso.Doc.Inline.other (Inline.lakeArgs $(quote hl)) #[])]

@[inline_extension lakeArgs]
def lakeArgs.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none

  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      if let .arr #[hl, name] := data then
        match fromJson? (α := Highlighted) hl with
        | .error e => HtmlT.logError s!"Couldn't deserialize Lake args: {e}"; return .empty
        | .ok hl =>
          let name := if let Json.str n := name then some n else none
          hl.inlineHtml name
      else HtmlT.logError s!"Expected two-element JSON array, got {data}"; return .empty
