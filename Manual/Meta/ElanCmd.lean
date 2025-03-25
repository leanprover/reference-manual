/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Manual.Meta.LakeCmd -- TODO: generalize the common parts into a library that can be upstreamed

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

namespace Manual

structure ElanCommandOptions where
  name : List Name
  spec : StrLit
  -- This only allows one level of subcommand, but it's sufficient for Elan as it is today
  aliases : List Name

partial def ElanCommandOptions.parse [Monad m] [MonadError m] : ArgParse m ElanCommandOptions :=
  ElanCommandOptions.mk <$>
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
    description := "string literal containing a Elan command spec",
    get
      | .str s => pure s
      | other => throwError "Expected string, got {repr other}"
  }

def Block.elanCommand (name : String) (aliases : List String) (spec : CommandSpec) : Block where
  name := `Manual.Block.elanCommand
  data := Json.arr #[Json.str name, toJson aliases, toJson spec]

def Inline.elanMeta : Inline where
  name := `Manual.elanMeta
  data := .arr #[.null, .null]

def Inline.elanArgs (hl : Highlighted) : Inline where
  name := `Manual.elanArgs
  data := .arr #[toJson hl, .null]

def Inline.elan : Inline where
  name := `Manual.elan
  data := .null


private partial def addElanMetaInline (name : String) : Doc.Inline Verso.Genre.Manual → Doc.Inline Verso.Genre.Manual
  | .other i xs =>
    if i.name == Inline.elanMeta.name || i.name == `Manual.elanArgs then
      if let Json.arr #[mn, _] := i.data then
        .other {i with data := .arr #[mn, .str name]} <| xs.map (addElanMetaInline name)
      else
        .other i <| xs.map (addElanMetaInline name)
    else
      .other i <| xs.map (addElanMetaInline name)
  | .concat xs => .concat <| xs.map (addElanMetaInline name)
  | .emph xs => .emph <| xs.map (addElanMetaInline name)
  | .bold xs => .bold <| xs.map (addElanMetaInline name)
  | .image alt url => .image alt url
  | .math t txt => .math t txt
  | .footnote x xs => .footnote x (xs.map (addElanMetaInline name))
  | .link xs url => .link (xs.map (addElanMetaInline name)) url
  | .code s => .code s
  | .linebreak str => .linebreak str
  | .text str => .text str

private partial def addElanMetaBlock (name : String) : Doc.Block Verso.Genre.Manual → Doc.Block Verso.Genre.Manual
  | .para xs => .para (xs.map (addElanMetaInline name))
  | .other b xs => .other b (xs.map (addElanMetaBlock name))
  | .concat xs => .concat (xs.map (addElanMetaBlock name))
  | .blockquote xs => .blockquote (xs.map (addElanMetaBlock name))
  | .code s => .code s
  | .dl items => .dl (items.map fun ⟨xs, ys⟩ => ⟨xs.map (addElanMetaInline name), ys.map (addElanMetaBlock name)⟩)
  | .ul items => .ul (items.map fun ⟨ys⟩ => ⟨ys.map (addElanMetaBlock name)⟩)
  | .ol n items => .ol n (items.map fun ⟨ys⟩ => ⟨ys.map (addElanMetaBlock name)⟩)


@[directive_expander elan]
def elan : DirectiveExpander
  | args, contents => do
    let {name, spec, aliases} ← ElanCommandOptions.parse.run args
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
      ``(addElanMetaBlock $(quote <| String.intercalate "~~" (name.map (·.toString (escape := false)))) $(← elabBlock b))
    pure #[← ``(Verso.Doc.Block.other (Block.elanCommand $(quote <| String.intercalate " " <| name.map (·.toString (escape := false))) $(quote <| aliases.map (·.toString (escape := false))) $(quote spec)) #[$contents,*])]

def elanCommandDomain : Name := `Manual.elanCommand

open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension Block.elanCommand]
def elanCommand.descr : BlockDescr where
  init st := st
    |>.setDomainTitle elanCommandDomain "Elan commands"
    |>.setDomainDescription elanCommandDomain "Detailed descriptions of Elan commands"

  traverse id info _ := do
    let Json.arr #[Json.str name, aliases, _] := info
      | logError s!"Failed to deserialize data while traversing a Elan command, expected 3-element array starting with string but got {info}"
        pure none
    let aliases : List String ←
      match fromJson? (α := List String) aliases with
      | .ok v => pure v
      | .error e =>
        logError s!"Failed to deserialize aliases while traversing a Elan command: {e}"; pure []
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name
    Index.addEntry id {term := Doc.Inline.concat #[.code name, .text " (Elan command)"]}
    modify fun st => st.saveDomainObject elanCommandDomain name id
    for a in aliases do
      modify fun st => st.saveDomainObject elanCommandDomain a id
    pure none

  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let Json.arr #[ Json.str name, aliases, spec] := info
        | do Verso.Doc.Html.HtmlT.logError s!"Failed to deserialize data while making HTML for Elan command, got {info}"; pure .empty
      let .ok (aliases : List String) := FromJson.fromJson? aliases
        | do Verso.Doc.Html.HtmlT.logError s!"Failed to deserialize aliases while making HTML for Elan command, got {spec}"; pure .empty
      let .ok (spec : CommandSpec) := FromJson.fromJson? spec
        | do Verso.Doc.Html.HtmlT.logError s!"Failed to deserialize spec while making HTML for Elan command, got {spec}"; pure .empty

      let elanTok : Highlighted := .token ⟨.keyword none none none, "elan"⟩
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
              {{aliases.map (fun (a : String) => {{<code>s!"elan {a}"</code>}}) |>.intersperse {{", "}}}}
            </p>
          }}

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"Elan command"</span>
          <pre class="signature hl lean block" data-lean-context={{name}}>
            {{← (Highlighted.seq #[elanTok, .text " ", nameTok, .text " ", spec]).toHtml}}
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
      let str := s!"elan {name}"
      pure #[(str, {{<code>{{str}}</code>}})]
    else throw s!"Expected a three-element array with a string first, got {info}"

@[role_expander elanMeta]
def elanMeta : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $mName:str )) := arg
      | throwErrorAt arg "Expected code literal with the metavariable"
    let mName := mName.getString

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other {Manual.Inline.elanMeta with data := Json.arr #[$(quote mName), .null]} #[Inline.code $(quote mName)])]

@[inline_extension elanMeta]
def elanMeta.descr : InlineDescr where
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


@[role_expander elan]
def elanInline : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $cmdName:str )) := arg
      | throwErrorAt arg "Expected code literal with the Elan command name"
    let name := cmdName.getString

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other {Manual.Inline.elan with data := $(quote name)} #[Inline.code $(quote name)])]

@[inline_extension elan]
def elan.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [
r#"
a.elan-command {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
a.elan-command:hover {
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
        if let some dest := (← read).traverseState.getDomainObject? elanCommandDomain n then
          for id in dest.ids do
            if let some (path, slug) := (← read).traverseState.externalTags[id]? then
              let url := path.link (some slug.toString)
              return {{<a href={{url}} class="elan-command"><code>s!"elan {n}"</code></a>}}

      HtmlT.logError s!"No name/dest for elan command {name}"
      is.mapM goI

@[role_expander elanArgs]
def elanArgs : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $spec:str )) := arg
      | throwErrorAt arg "Expected code literal with the Elan command name"

    match Parser.runParserCategory (← getEnv) `lake_cmd_spec spec.getString (← getFileName) with
    | .error e => throwErrorAt spec e
    | .ok stx =>
      match CommandSpec.ofSyntax stx with
      | .error e => throwErrorAt spec e
      | .ok spec =>
        let hl := spec.toHighlighted
        pure #[← ``(Verso.Doc.Inline.other (Inline.elanArgs $(quote hl)) #[])]

@[inline_extension elanArgs]
def elanArgs.descr : InlineDescr where
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
        | .error e => HtmlT.logError s!"Couldn't deserialize Elan args: {e}"; return .empty
        | .ok hl =>
          let name := if let Json.str n := name then some n else none
          hl.inlineHtml name
      else HtmlT.logError s!"Expected two-element JSON array, got {data}"; return .empty
