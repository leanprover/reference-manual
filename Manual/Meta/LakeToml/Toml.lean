/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/


module
public meta import Lake.Util.Lift
public import Manual.Meta.LakeToml.Highlight
public meta import Manual.Meta.LakeToml.Highlight
public import VersoManual.Basic
import Lake.Config.Dependency
import Lake.Config.LeanExeConfig
import Lake.Config.LeanLibConfig
import MultiVerso.Method

public section

open Verso ArgParse Doc Elab Genre.Manual Html Code Multi
open SubVerso.Highlighting Highlighted
open Lean Elab


open Lean.Elab.Tactic.GuardMsgs
open Lean.Doc (CodeView)

namespace Manual

def tomlFieldDomain := `Manual.lakeTomlField
def tomlTableDomain := `Manual.lakeTomlTable

namespace Toml

/--
A mapping from paths into the nested tables of the config file to the datatypes at which the field
documentation can be found.
-/
private def configPaths : Std.HashMap (List String) Name := Std.HashMap.ofList [
  (["require"], ``Lake.Dependency),
  (["lean_lib"], ``Lake.LeanLibConfig),
  (["lean_exe"], ``Lake.LeanExeConfig),
]

open Verso Output Html in
partial def Highlighted.toHtml (tableLink : Name → Option String) (keyLink : Name → Name → Option String) (urlLinks : Bool := true) : Highlighted -> Html
  | .token t s =>
    match t with
    | .bool _ => {{<span class="bool">{{s}}</span>}}
    | .string _ => {{<span class="string">{{s}}</span>}}
    | .num _ => {{<span class="num">{{s}}</span>}}
  | .tableHeader hl =>
    {{<span class="table-header">{{hl.toHtml tableLink keyLink urlLinks}}</span>}}
  | .tableName n hl =>
    let tableName := n.map (·.splitOn ".") >>= (configPaths[·]?)
    if let some dest := tableName >>= tableLink then
      {{<a href={{dest}}>{{hl.toHtml tableLink keyLink urlLinks}}</a>}}
    else
      hl.toHtml tableLink keyLink urlLinks
  | .tableDelim hl => {{<span class="table-delimiter">{{hl.toHtml tableLink keyLink urlLinks}}</span>}}
  | .concat hls => .seq (hls.map (toHtml tableLink keyLink urlLinks))
  | .link url hl =>
    if urlLinks then
      {{<a href={{url}}>{{hl.toHtml tableLink keyLink urlLinks}}</a>}}
    else
      hl.toHtml tableLink keyLink urlLinks
  | .text s => s
  | .ws s =>
    let comment := s.find (· == '#')
    let commentStr := s.extract comment s.endPos
    let commentHtml := if commentStr.isEmpty then .empty else {{<span class="comment">{{commentStr}}</span>}}
    {{ {{s.extract s.startPos comment}} {{commentHtml}} }}
  | .key none k => {{
    <span class="key">
      {{k.toHtml tableLink keyLink urlLinks}}
    </span>
  }}
  | .key (some p) k =>
    let path := p.splitOn "."
    let dest :=
      if let (table, [k]) := path.splitAt (path.length - 1) then
        if let some t := configPaths[table]? then
          keyLink t k.toName
        else none
      else none

    {{ <span class="key" data-toml-key={{p}}>
        {{ if let some url := dest then {{
          <a href={{url}}>{{k.toHtml tableLink keyLink urlLinks}}</a>
        }} else k.toHtml tableLink keyLink urlLinks }}
      </span>
    }}



end Toml

def Block.toml (highlighted : Toml.Highlighted) (link : Bool := true) : Block where
  name := `Manual.Block.toml
  data := toJson (highlighted, link)

def Inline.toml (highlighted : Toml.Highlighted) : Inline where
  name := `Manual.Inline.toml
  data := toJson highlighted


open Verso.Output Html in
private def htmlLink (state : TraverseState) (id : InternalId) (html : Html) : Html :=
  if let some dest := state.externalTags[id]? then
    {{<a href={{dest.link}}>{{html}}</a>}}
  else html

open Verso.Output Html in
private def htmlDest (state : TraverseState) (id : InternalId) : Option String :=
  if let some dest := state.externalTags[id]? then
    some <| dest.link
  else none

-- TODO upstream
/--
Return an arbitrary ID assigned to the object (or `none` if there are none).
-/
defmethod Object.getId (obj : Object) : Option InternalId := do
  for i in obj.ids do return i
  failure

def Toml.fieldLink (xref : Genre.Manual.TraverseState) (inTable fieldName : Name) : Option String := do
  let obj ← xref.getDomainObject? tomlFieldDomain s!"{inTable} {fieldName}"
  let dest← xref.externalTags[← obj.getId]?
  return dest.link

def Toml.tableLink (xref : Genre.Manual.TraverseState) (table : Name) : Option String := do
  let obj ← xref.getDomainObject? tomlTableDomain table.toString
  let dest ← xref.externalTags[← obj.getId]?
  return dest.link

def tomlCSS : String := r#"
.toml {
  font-family: var(--verso-code-font-family);
}

pre.toml {
  margin: 0.5rem .75rem;
  padding: 0.1rem 0;
}

.toml .bool, .toml .table-header {
    font-weight: 600;
}

.toml .table-header .key {
    color: #3030c0;
}

.toml .bool {
    color: #107090;
}

.toml .string {
    color: #0a5020;
}

.toml a, .toml a:link {
    color: inherit;
    text-decoration: none;
    border-bottom: 1px dotted #a2a2a2;
}

.toml a:hover {
    border-bottom-style: solid;
}
"#

structure TomlParams where
  link : Bool := true

meta section

instance : FromArgs TomlParams m where
  fromArgs := TomlParams.mk <$> ArgParse.flag `link true

open Lean.Parser in
@[code_block]
def toml : CodeBlockExpanderOf TomlParams
  | { link }, str => do
    let hl ← tomlContent str
    ``(Block.other (Block.toml $(quote hl) $(quote link)) #[Block.code $(quote str.getVersoCodeBlock)])

open Lean.Parser in
@[role_expander toml]
def tomlInline : RoleExpander
  | args, inlines => do
    ArgParse.done.run args

    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let some { content := str, .. } := CodeView.of arg
      | throwErrorAt arg "Expected code literal with TOML code"

    let hl ← tomlContent str

    pure #[← ``(Inline.other (Inline.toml $(quote hl)) #[Inline.code $(quote str.getVersoCode)])]

end


@[block_extension Block.toml]
def Block.toml.descr : BlockDescr where
  traverse _ _ _ := pure none

  toTeX := none

  extraCss := [tomlCSS]

  toHtml := some <| fun _goI _ _ info _ =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (hl, link) := FromJson.fromJson? (α := Toml.Highlighted × Bool) info
        | do reportError "Failed to deserialize highlighted TOML data"; pure .empty

      let xref := (← read).traverseState

      return {{
        <pre class="toml">
          {{hl.toHtml (Toml.tableLink xref) (Toml.fieldLink xref) link}}
        </pre>
      }}

@[inline_extension Inline.toml]
def Inline.toml.descr : InlineDescr where
  traverse _ _ _ := pure none

  toTeX := none

  extraCss := [tomlCSS]

  toHtml := some <| fun _ _ info _ =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok hl := FromJson.fromJson? (α := Toml.Highlighted) info
        | do reportError "Failed to deserialize highlighted TOML data"; pure .empty

      let xref := (← read).traverseState

      return {{
        <code class="toml">
          {{hl.toHtml (Toml.tableLink xref) (Toml.fieldLink xref)}}
        </code>
      }}
