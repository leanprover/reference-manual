/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/


import VersoManual

import Manual.Meta.Basic

import Lake.Toml.Decode
import Lake.Load.Toml

open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets Multi
open SubVerso.Highlighting Highlighted
open Lean Elab

open scoped Lean.Doc.Syntax

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

def tomlFieldDomain := `Manual.lakeTomlField
def tomlTableDomain := `Manual.lakeTomlTable

namespace Toml

namespace Highlighted

inductive Token where
  | string : String → Token
  | bool : Bool → Token
  | num : Nat → Token -- TODO other kinds of number?
deriving DecidableEq, Repr, Ord, ToJson, FromJson

open Lean.Syntax in
open Token in
instance : Quote Token where
  quote
    | .string s => mkCApp ``string #[quote s]
    | .bool b => mkCApp ``Token.bool #[quote b]
    | .num n  => mkCApp ``num #[quote n]

end Highlighted

inductive Highlighted where
  | token : Highlighted.Token → String → Highlighted
  | key (fullPath : Option String) : Highlighted → Highlighted
  | text : String → Highlighted
  | /-- Whitespace from leading/trailing source info -/
    ws : String → Highlighted
  | link (url : String) : Highlighted → Highlighted
  | concat : Array Highlighted → Highlighted
  | tableHeader : Highlighted → Highlighted
  | tableName (name : Option String) : Highlighted → Highlighted
  | tableDelim : Highlighted → Highlighted
deriving Inhabited, Repr, BEq, ToJson, FromJson

open Lean.Syntax in
open Highlighted in
partial instance : Quote Highlighted where
  quote := q
where
  q
    | .token t s => mkCApp ``Highlighted.token #[quote t, quote s]
    | .key p s => mkCApp ``key #[quote p, q s]
    | .text s => mkCApp ``Highlighted.text #[quote s]
    | .ws s => mkCApp ``Highlighted.text #[quote s]
    | .link url s => mkCApp ``Highlighted.link #[quote url, q s]
    | .concat xs =>
      let _ : Quote Highlighted := ⟨q⟩
      mkCApp ``Highlighted.concat #[quote xs]
    | .tableHeader hl => mkCApp ``Highlighted.tableHeader #[q hl]
    | .tableName n hl => mkCApp ``Highlighted.tableName #[quote n, q hl]
    | .tableDelim hl => mkCApp ``Highlighted.tableDelim #[q hl]

instance : Append Highlighted where
  append
    | .concat xs, .concat ys => .concat (xs ++ ys)
    | .concat xs, y => .concat (xs.push y)
    | x, .concat ys => .concat (#[x] ++ ys)
    | x, y => .concat (#[x] ++ [y])

instance : Coe (Array Highlighted) Highlighted where
  coe := .concat

def srcInfoHl : SourceInfo → Highlighted → Highlighted
    | .original leading _ trailing _, hl =>
      mkWs leading.toString ++ #[hl] ++ mkWs trailing.toString
    | _, hl => hl
where
  mkWs : String → Array Highlighted
    | "" => #[]
    | w => #[.ws w]

private def takeDropWhile (xs : Array α) (p : α → Bool) : Array α × Array α := Id.run do
  for h : i in [0:xs.size] do
    if !p xs[i] then
      return (xs.extract 0 i, xs.extract i xs.size)
  (xs, #[])

private def takeDropWhileRev (xs : Array α) (p : α → Bool) : Array α × Array α := Id.run do
  for h : i in [0:xs.size] do
    have : i < xs.size := by get_elem_tactic
    let j := xs.size - (i + 1)
    if !p xs[j] then
      return (xs.extract 0 (j + 1), xs.extract (j + 1) xs.size)
  (#[], xs)


/-- info: (#[], #[1, 2, 3, 4, 5]) -/
#guard_msgs in
#eval takeDropWhile  #[1,2,3,4,5] (· > 3)

/-- info: (#[1, 2], #[3, 4, 5]) -/
#guard_msgs in
#eval takeDropWhile #[1,2,3,4,5] (· < 3)

/-- info: (#[1, 2, 3], #[4, 5]) -/
#guard_msgs in
#eval takeDropWhileRev #[1,2,3,4,5] (· > 3)

/-- info: (#[1, 2, 3, 4, 5], #[]) -/
#guard_msgs in
#eval takeDropWhileRev #[1,2,3,4,5] (· < 3)

/--
Normalizes semantic info such that it doesn't have leading or trailing whitespace.
-/
partial def Highlighted.normalize : Highlighted → Highlighted
    | .concat xs => .concat (normArray (xs.map Highlighted.normalize))
    | .ws x => .ws x
    | .text x => .text x
    | .token t x => .token t x
    | .tableDelim x =>
      let (pre, y, post) := splitWs (normArray #[x.normalize])
      pre ++ .tableDelim y ++ post
    | .tableHeader x =>
      let (pre, y, post) := splitWs (normArray #[x.normalize])
      pre ++ .tableHeader y ++ post
    | .tableName n x =>
      let (pre, y, post) := splitWs (normArray #[x.normalize])
      pre ++ .tableName n y ++ post
    | .key p x =>
      let (pre, y, post) := splitWs (normArray #[x.normalize])
      pre ++ .key p y ++ post
    | .link d x =>
      let (pre, y, post) := splitWs (normArray #[x.normalize])
      pre ++ .link d y ++ post

where
  splitWs (xs : Array Highlighted) : (Array Highlighted × Array Highlighted × Array Highlighted) :=
    let (pre, rest) := takeDropWhile xs (· matches (.ws ..))
    let (mid, post) := takeDropWhileRev rest (· matches (.ws ..))
    (pre, mid, post)
  normArray (xs : Array Highlighted) :=
    xs.flatMap fun
      | .concat ys => normArray ys
      | .ws "" => #[]
      | other => #[other]

-- Inefficient string matching, which is fine because URLs are assumed short here
private def hasSubstring (haystack : String) (needle : String) : Bool := Id.run do
  if needle.isEmpty then return true
  if needle.length > haystack.length then return false
  let mut iter := haystack.startPos
  let fst := String.Pos.Raw.get needle 0
  while h : iter ≠ haystack.endPos do
    if iter.get h  == fst then
      let mut iter' := iter
      let mut iter'' := needle.startPos
      while h : iter'≠ haystack.endPos ∧ iter'' ≠ needle.endPos do
        if iter'.get h.1 == iter''.get h.2 then
          iter' := iter'.next h.1
          iter'' := iter''.next h.2
        else break
      if iter'' ≠ needle.endPos then
        iter := iter.next h
        continue
      else return true
    else
      iter := iter.next h
      continue
  return false

/-- info: true -/
#guard_msgs in
#eval hasSubstring "" ""

/-- info: false -/
#guard_msgs in
#eval hasSubstring "" "a"

/-- info: true -/
#guard_msgs in
#eval hasSubstring "bab" "a"

/-- info: true -/
#guard_msgs in
#eval hasSubstring "bab" "ab"

/-- info: false -/
#guard_msgs in
#eval hasSubstring "bab" "abb"

/-- info: true -/
#guard_msgs in
#eval hasSubstring "abcdef" "ef"

/-- info: true -/
#guard_msgs in
#eval hasSubstring "https://repohost.example.com/example2.git" "example.com"

/-- info: false -/
#guard_msgs in
#eval hasSubstring "https://github.com/example2.git" "example.com"

partial def highlightToml : Syntax → StateM (Option String) Highlighted := fun stx =>
  match stx with
  | .node info `null elts =>
    srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.toml elts =>
    srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.header elts =>
    srcInfoHl info <$> elts.mapM highlightToml
  | stx@(.node info ``Lake.Toml.keyval #[k, eq, v]) => do
    let keypath := (← get).map (· ++ ".") |>.getD ""
    let fullKey :=
      if let `(Lake.Toml.keyval|$k = $_) := stx then
        getKey k |>.map (keypath ++ ·)
      else none
    let hlK ← (.key fullKey) <$> highlightToml k

    return srcInfoHl info #[hlK, (← highlightToml eq), (← highlightToml v)]
  | .node info ``Lake.Toml.keyval elts =>
    srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.key elts =>
    (srcInfoHl info ∘ .key none) <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.simpleKey elts => srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.unquotedKey elts => srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.string elts =>
    srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.basicString #[s@(.atom _ str)] =>
    if let some str' := Lean.Syntax.decodeStrLit str then
      if (str'.startsWith "https://" || str'.startsWith "http://".toSlice ) && !hasSubstring str' "example.com" then
        (srcInfoHl info ∘ .link str') <$> highlightToml s
      else
        srcInfoHl info <$> highlightToml s
    else
      srcInfoHl info <$> highlightToml s
  | .node info ``Lake.Toml.boolean elts => srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.true #[.atom _ b] =>
    pure <| srcInfoHl info <| .token (.bool true) b
  | .node info ``Lake.Toml.false #[.atom _ b] =>
    pure <| srcInfoHl info <| .token (.bool false) b
  | .node info ``Lake.Toml.arrayTable #[open1, open2, contents, close1, close2] => do
    let n := getKey ⟨contents⟩
    set n
    return srcInfoHl info <| .tableHeader <|
      .tableDelim ((← highlightToml open1) ++ (← highlightToml open2)) ++
      (.tableName n (← highlightToml contents)) ++
      .tableDelim ((← highlightToml close1) ++ (← highlightToml close2))
  | .node info ``Lake.Toml.arrayTable elts =>
    srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.decInt #[.atom _ n] => pure <| srcInfoHl info <| .token (.num n.toNat!) n
  | .node info ``Lake.Toml.array elts => srcInfoHl info <$> elts.mapM highlightToml
  | .node info ``Lake.Toml.inlineTable elts => do
    let x ← get
    set (none : Option String)
    let out ← srcInfoHl info <$> elts.mapM highlightToml
    set x
    return out
  | .atom info str => pure <| srcInfoHl info (.text str)
  | other => panic! s!"Failed to highlight TOML (probably highlightToml in Manual.Meta.LakeToml needs another pattern case): {toString other}"

where
  getKey : TSyntax `Lake.Toml.key → Option String
    | `(Lake.Toml.key| $d:unquotedKey) =>
      d.raw.isLit? ``Lake.Toml.unquotedKey
    | `(Lake.Toml.key| $d:literalString) =>
      d.raw.isLit? ``Lake.Toml.literalString
    | `(Lake.Toml.key| $d:basicString) =>
      d.raw.isLit? ``Lake.Toml.basicString
    | _ => none

/--
A mapping from paths into the nested tables of the config file to the datatypes at which the field
documentation can be found.
-/
def configPaths : Std.HashMap (List String) Name := Std.HashMap.ofList [
  (["require"], ``Lake.Dependency),
  (["lean_lib"], ``Lake.LeanLibConfig),
  (["lean_exe"], ``Lake.LeanExeConfig),
]

open Verso Output Html in
partial def Highlighted.toHtml (tableLink : Name → Option String) (keyLink : Name → Name → Option String) : Highlighted -> Html
  | .token t s =>
    match t with
    | .bool _ => {{<span class="bool">{{s}}</span>}}
    | .string _ => {{<span class="string">{{s}}</span>}}
    | .num _ => {{<span class="num">{{s}}</span>}}
  | .tableHeader hl =>
    {{<span class="table-header">{{hl.toHtml tableLink keyLink}}</span>}}
  | .tableName n hl =>
    let tableName := n.map (·.splitOn ".") >>= (configPaths[·]?)
    if let some dest := tableName >>= tableLink then
      {{<a href={{dest}}>{{hl.toHtml tableLink keyLink}}</a>}}
    else
      hl.toHtml tableLink keyLink
  | .tableDelim hl => {{<span class="table-delimiter">{{hl.toHtml tableLink keyLink}}</span>}}
  | .concat hls => .seq (hls.map (toHtml tableLink keyLink))
  | .link url hl => {{<a href={{url}}>{{hl.toHtml tableLink keyLink}}</a>}}
  | .text s => s
  | .ws s =>
    let comment := s.find (· == '#')
    let commentStr := s.extract comment s.endPos
    let commentHtml := if commentStr.isEmpty then .empty else {{<span class="comment">{{commentStr}}</span>}}
    {{ {{s.extract s.startPos comment}} {{commentHtml}} }}
  | .key none k => {{
    <span class="key">
      {{k.toHtml tableLink keyLink}}
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
          <a href={{url}}>{{k.toHtml tableLink keyLink}}</a>
        }} else k.toHtml tableLink keyLink }}
      </span>
    }}



end Toml

def Block.toml (highlighted : Toml.Highlighted) : Block where
  name := `Manual.Block.toml
  data := toJson highlighted

def Inline.toml (highlighted : Toml.Highlighted) : Inline where
  name := `Manual.Inline.toml
  data := toJson highlighted


open Verso.Output Html in
def htmlLink (state : TraverseState) (id : InternalId) (html : Html) : Html :=
  if let some dest := state.externalTags[id]? then
    {{<a href={{dest.link}}>{{html}}</a>}}
  else html

open Verso.Output Html in
def htmlDest (state : TraverseState) (id : InternalId) : Option String :=
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

open Lean.Parser in
def tomlContent (str : StrLit) : DocElabM Toml.Highlighted := do
  let scope : Command.Scope := {header := ""}
  let inputCtx := Parser.mkInputContext (← parserInputString str) (← getFileName)
  let pmctx : Parser.ParserModuleContext :=
    { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let pos := str.raw.getPos? |>.getD 0

  let p := andthenFn whitespace Lake.Toml.toml.fn
  let s := p.run inputCtx pmctx (getTokenTable pmctx.env) { cache := initCacheForInput inputCtx.inputString, pos }
  match s.errorMsg with
  | some err =>
    throwErrorAt str "Couldn't parse TOML: {err}"
  | none =>
    let #[stx] := s.stxStack.toSubarray.toArray
      | throwErrorAt str s!"Internal error parsing TOML - expected one result, got {s.stxStack.toSubarray.toArray}"
    return Toml.highlightToml stx |>.run' none |>.normalize

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

open Lean.Parser in
@[code_block_expander toml]
def toml : CodeBlockExpander
  | args, str => do
    ArgParse.done.run args
    let hl ← tomlContent str
    pure #[← ``(Block.other (Block.toml $(quote hl)) #[Block.code $(quote str.getString)])]

open Lean.Parser in
@[role_expander toml]
def tomlInline : RoleExpander
  | args, inlines => do
    ArgParse.done.run args

    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $str:str )) := arg
      | throwErrorAt arg "Expected code literal with TOML code"

    let hl ← tomlContent str

    pure #[← ``(Inline.other (Inline.toml $(quote hl)) #[Inline.code $(quote str.getString)])]


@[block_extension Block.toml]
def Block.toml.descr : BlockDescr where
  traverse _ _ _ := pure none

  toTeX := none

  extraCss := [tomlCSS]

  toHtml := some <| fun _goI _ _ info _ =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok hl := FromJson.fromJson? (α := Toml.Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize highlighted TOML data"; pure .empty

      let xref := (← read).traverseState

      return {{
        <pre class="toml">
          {{hl.toHtml (Toml.tableLink xref) (Toml.fieldLink xref)}}
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
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize highlighted TOML data"; pure .empty

      let xref := (← read).traverseState

      return {{
        <code class="toml">
          {{hl.toHtml (Toml.tableLink xref) (Toml.fieldLink xref)}}
        </code>
      }}
