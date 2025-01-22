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
import Manual.Meta.ExpectString
import Manual.Meta.Lean.Scopes
import Manual.Meta.Lean.Block

import Lake
import Lake.Toml.Decode
import Lake.Load.Toml

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

namespace Toml

inductive FieldType where
  | string
  | stringOf (what : String)
  | version
  | path
  | array (contents : FieldType)
  | oneOf (choices : List String)
  | option (t : FieldType)
  | bool
  | other (name : Name) (what : String)
deriving Repr, ToJson, FromJson

open Lean Syntax in
instance : Quote FieldType where
  quote := q
where
  q : FieldType → Term
    | .string => mkCApp ``FieldType.string #[]
    | .stringOf x => mkCApp ``FieldType.stringOf #[quote x]
    | .version => mkCApp ``FieldType.version #[]
    | .path => mkCApp ``FieldType.path #[]
    | .array x => mkCApp ``FieldType.array #[q x]
    | .oneOf cs => mkCApp ``FieldType.oneOf #[quote cs]
    | .option x => mkCApp ``FieldType.option #[q x]
    | .bool => mkCApp ``FieldType.bool #[]
    | .other x y => mkCApp ``FieldType.other #[quote x, quote y]


open Output Html in
def FieldType.toHtml (plural : Bool := false) : FieldType → Html
  | .string => if plural then "strings" else "String"
  | .stringOf x => s!"{x} (as string{if plural then "s" else ""}"
  | .version => if plural then "version strings" else "Version string"
  | .path => if plural then "paths" else "Path"
  | .array t => (if plural then "arrays of " else "Array of ") ++ t.toHtml true
  | .other _ y => if plural then y ++ "s" else y
  | .bool => if plural then "Booleans" else "Boolean"
  | .option t => t.toHtml ++ " (optional)"
  | .oneOf xs =>
    let opts := xs
      |>.map ({{<code>{{show Html from .text true s!"\"{·}\""}}</code>}})
      |>.intersperse {{", "}}
    {{"one of " {{opts}} }}

structure Field (α) where
  name : Name
  type : FieldType
  docs? : Option α
deriving Repr, ToJson, FromJson

instance : Functor Field where
  map f | ⟨n, t, d?⟩ => ⟨n, t, d?.map f⟩

def Field.mapM [Monad m] (f : α → m β) : Field α → m (Field β)
  | ⟨n, t, d?⟩ => d?.mapM f <&> (⟨n, t, ·⟩)

def Field.takeDocs (f : Field α) : Field Empty × Option α :=
  ({f with docs? := none}, f.docs?)

open Lean Syntax in
instance [Quote α] : Quote (Field α) where
  quote | ⟨n, t, d?⟩ => mkCApp ``Field.mk #[quote n, quote t, quote d?]

structure Table (α) where
  name : String
  typeName : Name
  fields : Array (Field α)
deriving Repr

open Lean Syntax in
instance [Quote α] : Quote (Table α) where
  quote | ⟨n, tn, fs⟩ => mkCApp ``Table.mk #[quote n, quote tn, quote fs]

end Toml

def Block.tomlFieldCategory (title : String) (fields : List Name) : Block where
  name := `Manual.Block.tomlFieldCategory
  data := .arr #[.str title, toJson fields]

def Block.tomlField (sort : Option Nat) (inTable : Name) (field : Toml.Field Empty) : Block where
  name := `Manual.Block.tomlField
  data := ToJson.toJson (sort, inTable, field)

def Block.tomlTable (name : String) (typeName : Name) : Block where
  name := `Manual.Block.tomlTable
  data := ToJson.toJson (name, typeName)

def tomlFieldDomain := `Manual.lakeTomlField
def tomlTableDomain := `Manual.lakeTomlTable

structure TomlFieldOpts where
  inTable : Name
  field : Name
  typeDesc : String
  type : Name
  sort : Option Nat

instance [Inhabited α] [Applicative f] : Inhabited (f α) where
  default := pure default

@[specialize]
private partial def many [Applicative f] [Alternative f] (p : f α) : f (List α) :=
  ((· :: ·) <$> p <*> many p) <|> pure []


def TomlFieldOpts.parse  [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m TomlFieldOpts :=
  TomlFieldOpts.mk <$> .positional `inTable .name <*> .positional `field .name <*> .positional `typeDesc .string <*> .positional `type .resolvedName <*> .named `sort .nat true

instance : Quote Empty where
  quote := nofun

@[directive_expander tomlField]
def tomlField : DirectiveExpander
  | args, contents => do
    let {inTable, field, typeDesc, type, sort} ← TomlFieldOpts.parse.run args
    let field : Toml.Field Empty := {name := field, type := .other type typeDesc, docs? := none}
    let contents ← contents.mapM elabBlock
    return #[← ``(Block.other (Block.tomlField $(quote sort) $(quote inTable) $(quote field)) #[$contents,*])]


@[block_extension Block.tomlField]
def Block.tomlField.descr : BlockDescr where
  traverse id info _ := do
    let .ok (_, inTable, field) := FromJson.fromJson? (α := Option Nat × Name × Toml.Field Empty) info
      | do logError "Failed to deserialize field doc data"; pure none
    modify fun s =>
      let name := s!"{inTable} {field.name}"
      s |>.saveDomainObject tomlFieldDomain name id
        |>.saveDomainObjectData tomlFieldDomain name inTable.toString
    discard <| externalTag id (← read).path s!"{inTable}-{field.name}"
    pure none
  toTeX := none

  extraCss := [".namedocs .label a { color: inherit; }"]

  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (_, inTable, field) := FromJson.fromJson? (α := Option Nat × Name × Toml.Field Empty) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize field doc data"; pure .empty
      let sig : Html := {{ {{field.name.toString}} }}

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      let name := s!"{inTable} {field.name}"

      let label : Option Html := do
        let .str tableName ← xref.getDomainObject? tomlFieldDomain name <&> (·.data)
          | none
        let table ← xref.getDomainObject? tomlTableDomain tableName
        let #[id] := table.ids.toArray
          | none
        let .str name := table.data
          | none
        let (path, slug) ← xref.externalTags[id]?
        pure {{"field in "<a href={{path.link slug.toString}}>{{name}}</a>}}

      return {{
        <dt {{idAttr}}>
          <code class="field-name">{{sig}}</code>
        </dt>
        <dd>
            <p><strong>"Contains:"</strong>" " {{field.type.toHtml}}</p>
            {{← contents.mapM goB}}
        </dd>
      }}

structure TomlFieldCategoryOpts where
  title : String
  fields : List Name

def TomlFieldCategoryOpts.parse [Monad m] [MonadError m] : ArgParse m TomlFieldCategoryOpts :=
  TomlFieldCategoryOpts.mk <$> .positional `title .string <*> many (.positional `field .name)

@[directive_expander tomlFieldCategory]
def tomlFieldCategory : DirectiveExpander
  | args, contents => do
    let {title, fields} ← TomlFieldCategoryOpts.parse.run args
    let contents ← contents.mapM elabBlock
    return #[← ``(Block.other (Block.tomlFieldCategory $(quote title) $(quote fields)) #[$contents,*])]


@[block_extension Block.tomlFieldCategory]
def Block.tomlFieldCategory.descr : BlockDescr where
  traverse _id _info _ := pure none

  toTeX := none

  extraCss := [r#"
.field-category > :first-child {
}

.field-category > :not(:first-child) {
  margin-left: 1rem;
}
"#

]

  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .arr #[.str title, _fields] := info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize field category doc data"; pure .empty

      return {{
        <div class="field-category">
          <p><strong>{{title}}":"</strong></p>
          {{← contents.mapM goB}}
        </div>
      }}

private partial def flattenBlocks (blocks : Array (Doc.Block genre)) : Array (Doc.Block genre) :=
  blocks.flatMap fun
    | .concat bs =>
      flattenBlocks bs
    | other => #[other]

@[block_extension Block.tomlTable]
def Block.tomlTable.descr : BlockDescr where
  traverse id info _ := do
    let .ok (humanName, typeName) := FromJson.fromJson? (α := String × Name) info
        | do logError "Failed to deserialize FFI doc data"; pure none
    modify fun s =>
      s |>.saveDomainObject tomlTableDomain typeName.toString id
        |>.saveDomainObjectData tomlTableDomain typeName.toString humanName
    discard <| externalTag id (← read).path typeName.toString
    pure none

  toTeX := none

  extraCss := [
r#"
dl.toml-table-field-spec {
}
"#
]

  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (humanName, _typeName) := FromJson.fromJson? (α := String × Name) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize FFI doc data"; pure .empty
      let sig : Html := {{ {{humanName}} }}

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      let (categories, contents) := flattenBlocks contents |>.partition (· matches Block.other {name := `Manual.Block.tomlFieldCategory, ..} _)
      let categories := categories.map fun
        | blk@(Block.other {name := `Manual.Block.tomlFieldCategory, data := .arr #[.str title, fields], ..} _) =>
          if let .ok fields := FromJson.fromJson? fields (α := List Name) then
            (fields, some title, blk)
          else ([], none, blk)
        | blk => ([], none, blk)

      let category? (f : Name) : Option String := Id.run do
        for (fs, title, _) in categories do
          if f ∈ fs then return title
        return none

      -- First partition the inner blocks into unsorted fields, sorted fields, and other blocks
      let mut fields := #[]
      let mut sorted := #[]
      let mut notFields := #[]
      for f in flattenBlocks contents do
        if let Block.other {name:=`Manual.Block.tomlField, data, .. : Genre.Manual.Block} .. := f then
          if let .ok (sort?, _, field) := FromJson.fromJson? (α := Option Nat × Name × Toml.Field Empty) data then
            if let some sort := sort? then
              sorted := sorted.push (sort, f, field.name)
            else
              fields := fields.push (f, field.name)
        else notFields := notFields.push f

      -- Next, find all the categories and the names that they expect
      let mut categorized : Std.HashMap String (Array (Doc.Block Genre.Manual)) := {}
      let mut uncategorized := #[]
      for (f, fieldName) in fields do
        if let some title := category? fieldName then
          categorized := categorized.insert title <| (categorized.getD title #[]).push f
        else
          uncategorized := uncategorized.push f

      -- Finally, distribute fields into categories, respecting the requested sort orders
      for (n, f, fieldName) in sorted.qsort (lt := (·.1 < ·.1)) do
        if let some title := category? fieldName then
          let inCat := categorized.getD title #[]
          if h : n < inCat.size then
            categorized := categorized.insert title <| inCat.insertIdx n f
          else
            categorized := categorized.insert title <| inCat.push f
        else
          if h : n < uncategorized.size then
            uncategorized := uncategorized.insertIdx n f
          else
            uncategorized := uncategorized.push f

      -- Add the contents of each category to its corresponding block
      let categories := categories.map fun
        | (_, some title, Doc.Block.other which contents) =>
          let inCategory := categorized.getD title #[]
          Doc.Block.other which (contents ++ inCategory)
        | (_, _, blk) => blk


      let uncatHtml ← uncategorized.mapM goB
      let catHtml ← categories.mapM goB

      let fieldHtml :=
        if categories.isEmpty then {{
            <p><strong>"Fields:"</strong></p>
            <dl class="toml-table-field-spec">
              {{uncatHtml}}
            </dl>
        }} else {{
          {{catHtml}}
          <p><strong>"Other Fields:"</strong></p>
          <dl class="toml-table-field-spec">
            {{uncatHtml}}
          </dl>
        }}

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">"TOML table"</span>
          <pre class="signature">{{sig}}</pre>
          <div class="text">
            {{← notFields.mapM goB}}

            {{fieldHtml}}
          </div>
        </div>
      }}

namespace Toml

section

open Lean Meta

variable {m : Type → Type}
variable [Monad m]
variable [MonadEnv m] [MonadMCtx m] [MonadWithOptions m] [MonadFileMap m] [MonadError m]
variable [MonadQuotation m]
variable [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadLiftT IO m]

def buildTypes := ["debug", "relWithDebInfo", "minSizeRel", "release"]

-- Fail if more types added
theorem builtTypes_exhaustive : s ∈ buildTypes ↔ (Lake.BuildType.ofString? s).isSome := by
  simp only [buildTypes]
  constructor
  . intro h
    simp [Lake.BuildType.ofString?]
    repeat (cases ‹List.Mem _ _›; simp)
    contradiction
  . intro h
    simp [Lake.BuildType.ofString?] at h
    split at h <;> simp_all


def asTable (humanName : String) (n : Name) (skip : List Name := []) : DocElabM Term  := do
  let env ← getEnv
  if let some (.inductInfo ii) := env.find? n then
    let allFields := getStructureFieldsFlattened env n (includeSubobjectFields := false) |>.filter (!skip.contains ·)
    let directFields := getStructureFields env n
    -- Sort the direct fields first, because that makes the ordering "more intuitive" in the docs
    let allFields := allFields.filter (directFields.contains ·) ++ allFields.filter (!directFields.contains ·)
    let ancestry ← getStructureResolutionOrder n
    let tomlFields : Array (Field (Array Term)) ← forallTelescopeReducing ii.type fun params _ =>
      withLocalDeclD `self (mkAppN (mkConst n (ii.levelParams.map mkLevelParam)) params) fun s =>
        allFields.mapM fun fieldName => do
          let proj ← mkProjection s fieldName
          let type ← inferType proj >>= instantiateMVars
          for struct in ancestry do
            if let some projFn := getProjFnInfoForField? env struct fieldName then
              let docs? ← findDocString? env projFn.1
              let docs? ← docs?.mapM fun mdDocs => do
                let some ast := MD4Lean.parse mdDocs
                  | throwError "Failed to parse docstring as Markdown"
                -- Here most code elements are not Lean code; don't elaborate them
                ast.blocks.mapM Markdown.blockFromMarkdown

              let type' : Option FieldType :=
                if type.isConstOf ``String then some .string
                else if type.isConstOf ``Name then some .string
                else if type.isConstOf ``Bool then some .bool
                else if type.isConstOf ``System.FilePath then some .path
                else if type.isConstOf ``Lake.WorkspaceConfig then some (.other ``Lake.WorkspaceConfig "workspace configuration")
                else if type.isConstOf ``Lake.BuildType then some (.oneOf buildTypes)
                else if type.isConstOf ``Lake.StdVer then some .version
                else if type.isConstOf ``Lake.StrPat then some (.other ``Lake.StrPat "string pattern")
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``Lake.LeanOption then some (.array (.other ``Lake.LeanOption "Lean option"))
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``String then some (.array .string)
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``Name then some (.array .string)
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``System.FilePath then some (.array .path)
                else if type.isAppOfArity ``Option 1 && (type.getArg! 0).isConstOf ``Bool then some (.option .bool)
                else if type.isAppOfArity ``Option 1 && (type.getArg! 0).isConstOf ``String then some (.option .string)
                else if type.isAppOfArity ``Option 1 && (type.getArg! 0).isConstOf ``System.FilePath then some (.option .path)
                else none
              if let some type := type' then
                return { name := fieldName, type, docs?}
              else throwError "Can't convert Lean type '{type}' to a field type for '{fieldName}'"
          throwError "No projection function found for {n}.{fieldName}"
    ``(Table.mk $(quote humanName) $(quote n) $(quote tomlFields))
  else
    throwError "Not an inductive type: {n}"


def Field.toBlock (inTable : Name) (f : Field (Array (Block Genre.Manual))) : Block Genre.Manual :=
  let (f, docs?) := f.takeDocs
  .other (Block.tomlField none inTable f) (docs?.getD #[])

def Table.toBlock (docs : Array (Block Genre.Manual)) (t : Table (Array (Block Genre.Manual))) : Array (Block Genre.Manual) :=
  let (fieldBlocks, notFields) := docs.partition (fun b => b matches Block.other {name:=`Manual.Block.tomlField, .. : Genre.Manual.Block} ..)

  #[.other (Block.tomlTable t.name t.typeName) <| notFields ++ (fieldBlocks ++ t.fields.map (Field.toBlock t.typeName))]

end

end Toml

structure TomlTableOpts where
  description : String
  name : Name
  skip : List Name

def TomlTableOpts.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m TomlTableOpts :=
  TomlTableOpts.mk <$> .positional `description .string <*> .positional `name .resolvedName <*> many (.named `skip .name false)


open Markdown in
/--
Interpret a structure type as a TOML table, and generate docs.
-/
@[directive_expander tomlTableDocs]
def tomlTableDocs : DirectiveExpander
  | args, contents => do
    let {description, name, skip} ← TomlTableOpts.parse.run args
    let docsStx ←
      match ← Lean.findDocString? (← getEnv) name with
      | none => throwError m!"No docs found for '{name}'"; pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwError "Failed to parse docstring as Markdown"

        -- Don't render these as ordinary Lean docstrings, because code samples in them
        -- are usually things like shell commands rather than Lean code.
        -- TODO: detect and add xref to `lake` subcommands or other fields here.
        ast.blocks.mapM (blockFromMarkdown (handleHeaders := strongEmphHeaders))

    let tableStx ← Toml.asTable description name skip

    let userContents ← contents.mapM elabBlock

    return #[← `(Block.concat (Toml.Table.toBlock #[$(docsStx),* , $userContents,*] $tableStx))]


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
  | /-- Whitespace from leading/trailing source info -/ ws : String → Highlighted
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
  let mut iter := haystack.iter
  let fst := needle.get 0
  while h : iter.hasNext do
    if iter.curr' h  == fst then
      let mut iter' := iter
      let mut iter'' := needle.iter
      while iter'.hasNext && iter''.hasNext do
        if iter'.curr == iter''.curr then
          iter' := iter'.next
          iter'' := iter''.next
        else break
      if iter''.hasNext then
        iter := iter.next
        continue
      else return true
    else
      iter := iter.next
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
      if (str'.take 8 == "https://" || str'.take 7 == "http://") && !hasSubstring str' "example.com" then
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
    {{ {{s.extract 0 comment}} {{commentHtml}} }}
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

open Verso.Output Html in
def htmlLink (state : TraverseState) (id : InternalId) (html : Html) : Html :=
  if let some (path, htmlId) := state.externalTags[id]? then
    {{<a href={{path.link htmlId.toString}}>{{html}}</a>}}
  else html

open Verso.Output Html in
def htmlDest (state : TraverseState) (id : InternalId) : Option String :=
  if let some (path, htmlId) := state.externalTags[id]? then
    some <| path.link htmlId.toString
  else none

-- TODO upstream
/--
Return an arbitrary ID assigned to the object (or `none` if there are none).
-/
defmethod Object.getId (obj : Object) : Option InternalId := do
  for i in obj.ids do return i
  failure

def fieldLink (xref : Genre.Manual.TraverseState) (inTable fieldName : Name) : Option String := do
  let obj ← xref.getDomainObject? tomlFieldDomain s!"{inTable} {fieldName}"
  let (path, htmlId) ← xref.externalTags[← obj.getId]?
  return path.link htmlId.toString

def tableLink (xref : Genre.Manual.TraverseState) (table : Name) : Option String := do
  let obj ← xref.getDomainObject? tomlTableDomain table.toString
  let (path, htmlId) ← xref.externalTags[← obj.getId]?
  return path.link htmlId.toString


open Lean.Parser in
@[code_block_expander toml]
def toml : CodeBlockExpander
  | args, str => do
    ArgParse.done.run args
    let scope : Command.Scope := {header := ""}
    let inputCtx := Parser.mkInputContext (← parserInputString str) (← getFileName)
    let pmctx : Parser.ParserModuleContext :=
      { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let pos := str.raw.getPos? |>.getD 0

    let p := andthenFn whitespace Lake.Toml.toml.fn
    let s := p.run inputCtx pmctx (getTokenTable pmctx.env) { cache := initCacheForInput inputCtx.input, pos }
    match s.errorMsg with
    | some err =>
      throwErrorAt str "Couldn't parse TOML: {err}"
    | none =>
      let #[stx] := s.stxStack.toSubarray.toArray
        | throwErrorAt str s!"Internal error parsing TOML - expected one result, got {s.stxStack.toSubarray.toArray}"
      let hl : Toml.Highlighted := Toml.highlightToml stx |>.run' none |>.normalize
      pure #[← ``(Block.other (Block.toml $(quote hl)) #[Block.code $(quote str.getString)])]

@[block_extension Block.toml]
def Block.toml.descr : BlockDescr where
  traverse _ _ _ := pure none

  toTeX := none

  extraCss := [
r#"
pre.toml {
  font-family: var(--verso-code-font-family);
  margin: 0.5em .75em;
  padding: 0 0;
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
]

  toHtml := some <| fun _goI _ _ info _ =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok hl := FromJson.fromJson? (α := Toml.Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize highlighted TOML data"; pure .empty

      let xref := (← read).traverseState

      return {{
        <pre class="toml">
          {{hl.toHtml (tableLink xref) (fieldLink xref)}}
        </pre>
      }}


namespace Toml

/-- Types that can be used in in-manual tests for TOML decoding -/
class Test (α : Type u) where
  toString : α → Format

instance [ToString α] : Test α where
  toString := .text ∘ toString

instance [Repr α] : Test α where
  toString x := repr x

instance [Test α] : Test (Array α) where
  toString arr := "#[" ++ .group (.nest 2 <| Format.joinSep (arr.map Test.toString).toList ("," ++ .line))  ++ "]"

instance [Test α] : Test (NameMap α) where
  toString xs := "{" ++ .group (.nest 2 <| Format.joinSep (xs.toList.map (fun x => s!"'{x.1}' ↦ {Test.toString x.2}")) ("," ++ .line)) ++ "}"

instance [Test α] : Test (Lake.OrdNameMap α) where
  toString xs := Id.run do
    let mut out : Std.Format := Std.Format.nil
    for (k, v) in xs.toRBMap do
      out := out ++ .group (.nest 2 <| Test.toString k ++ " ↦" ++ .line ++ Test.toString v) ++ "," ++ .line
    return .group (.nest 2 <| "{" ++ out) ++ "}"

instance [{n : Name} → Test (f n)] : Test (Lake.DNameMap f) where
  toString xs := Id.run do
    let mut out : Std.Format := Std.Format.nil
    for ⟨k, v⟩ in xs do
      out := out ++ .group (.nest 2 <| Test.toString k ++ " ↦" ++ .line ++ Test.toString v) ++ "," ++ .line
    return .group (.nest 2 <| "{" ++ out) ++ "}"

instance : Test Lake.StrPat where
  toString
    | .satisfies _f n => s!".satisfies #<fun> {n}"
    | .startsWith s => s!".startsWith {s.quote}"
    | .mem ss => s!".mem {Test.toString ss}"

instance : Test (Lake.Script) where
  toString s := s!"#<script {s.name}>"

instance : Test (Lake.ExternLibConfig n n') where
  toString _ := s!"#<extern lib>"

instance : Test (Lake.OpaqueTargetConfig n n') where
  toString _ := s!"#<opaque target>"

instance : Test (Lake.OpaquePostUpdateHook α) where
  toString _ := s!"#<post-update-hook>"

-- HACK: This is easier to write than a deriving handler and there's a deadline
/--
info: {toWorkspaceConfig, toLeanConfig, name, manifestFile, extraDepTargets, precompileModules, moreServerArgs, moreGlobalServerArgs, srcDir, buildDir, leanLibDir, nativeLibDir, binDir, irDir, releaseRepo?, releaseRepo, buildArchive?, buildArchive, preferReleaseBuild, testDriver, testDriverArgs, lintDriver, lintDriverArgs, version, versionTags, description, keywords, homepage, license, licenseFiles, readmeFile, reservoir}
"{" ++ .group (.nest 2 <| "toWorkspaceConfig := " ++ Test.toString toWorkspaceConfig ++ "," ++ .line ++ "toLeanConfig := " ++ Test.toString toLeanConfig ++ "," ++ .line ++ "name := " ++ Test.toString name ++ "," ++ .line ++ "manifestFile := " ++ Test.toString manifestFile ++ "," ++ .line ++ "extraDepTargets := " ++ Test.toString extraDepTargets ++ "," ++ .line ++ "precompileModules := " ++ Test.toString precompileModules ++ "," ++ .line ++ "moreServerArgs := " ++ Test.toString moreServerArgs ++ "," ++ .line ++ "moreGlobalServerArgs := " ++ Test.toString moreGlobalServerArgs ++ "," ++ .line ++ "srcDir := " ++ Test.toString srcDir ++ "," ++ .line ++ "buildDir := " ++ Test.toString buildDir ++ "," ++ .line ++ "leanLibDir := " ++ Test.toString leanLibDir ++ "," ++ .line ++ "nativeLibDir := " ++ Test.toString nativeLibDir ++ "," ++ .line ++ "binDir := " ++ Test.toString binDir ++ "," ++ .line ++ "irDir := " ++ Test.toString irDir ++ "," ++ .line ++ "releaseRepo? := " ++ Test.toString releaseRepo? ++ "," ++ .line ++ "releaseRepo := " ++ Test.toString releaseRepo ++ "," ++ .line ++ "buildArchive? := " ++ Test.toString buildArchive? ++ "," ++ .line ++ "buildArchive := " ++ "ELIDED" ++ "," ++ .line ++ "preferReleaseBuild := " ++ Test.toString preferReleaseBuild ++ "," ++ .line ++ "testDriver := " ++ Test.toString testDriver ++ "," ++ .line ++ "testDriverArgs := " ++ Test.toString testDriverArgs ++ "," ++ .line ++ "lintDriver := " ++ Test.toString lintDriver ++ "," ++ .line ++ "lintDriverArgs := " ++ Test.toString lintDriverArgs ++ "," ++ .line ++ "version := " ++ Test.toString version ++ "," ++ .line ++ "versionTags := " ++ Test.toString versionTags ++ "," ++ .line ++ "description := " ++ Test.toString description ++ "," ++ .line ++ "keywords := " ++ Test.toString keywords ++ "," ++ .line ++ "homepage := " ++ Test.toString homepage ++ "," ++ .line ++ "license := " ++ Test.toString license ++ "," ++ .line ++ "licenseFiles := " ++ Test.toString licenseFiles ++ "," ++ .line ++ "readmeFile := " ++ Test.toString readmeFile ++ "," ++ .line ++ "reservoir := " ++ Test.toString reservoir) ++ "}"
-/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let fs := getStructureFields (← getEnv) ``Lake.PackageConfig |>.toList
  IO.println <| "{" ++ String.intercalate ", " (fs.map (·.toString)) ++ "}"
  IO.println <|
    "\"{\" ++ .group (.nest 2 <| " ++
    String.intercalate " ++ \",\" ++ .line ++ " (fs.map (fun f => s!"\"{f} := \" ++ {if f == `buildArchive then "\"ELIDED\"" else s!"Test.toString {f}"}")) ++
    ") ++ \"}\""


instance : Test Lake.PackageConfig where
  toString
    | {toWorkspaceConfig, toLeanConfig, name, manifestFile, extraDepTargets, precompileModules, moreServerArgs, moreGlobalServerArgs, srcDir, buildDir, leanLibDir, nativeLibDir, binDir, irDir, releaseRepo?, releaseRepo, buildArchive?, buildArchive:=_, preferReleaseBuild, testDriver, testDriverArgs, lintDriver, lintDriverArgs, version, versionTags, description, keywords, homepage, license, licenseFiles, readmeFile, reservoir} =>
      "{" ++ .group (.nest 2 <| "toWorkspaceConfig := " ++ Test.toString toWorkspaceConfig ++ "," ++ .line ++ "toLeanConfig := " ++ Test.toString toLeanConfig ++ "," ++ .line ++ "name := " ++ Test.toString name ++ "," ++ .line ++ "manifestFile := " ++ Test.toString manifestFile ++ "," ++ .line ++ "extraDepTargets := " ++ Test.toString extraDepTargets ++ "," ++ .line ++ "precompileModules := " ++ Test.toString precompileModules ++ "," ++ .line ++ "moreServerArgs := " ++ Test.toString moreServerArgs ++ "," ++ .line ++ "moreGlobalServerArgs := " ++ Test.toString moreGlobalServerArgs ++ "," ++ .line ++ "srcDir := " ++ Test.toString srcDir ++ "," ++ .line ++ "buildDir := " ++ Test.toString buildDir ++ "," ++ .line ++ "leanLibDir := " ++ Test.toString leanLibDir ++ "," ++ .line ++ "nativeLibDir := " ++ Test.toString nativeLibDir ++ "," ++ .line ++ "binDir := " ++ Test.toString binDir ++ "," ++ .line ++ "irDir := " ++ Test.toString irDir ++ "," ++ .line ++ "releaseRepo? := " ++ Test.toString releaseRepo? ++ "," ++ .line ++ "releaseRepo := " ++ Test.toString releaseRepo ++ "," ++ .line ++ "buildArchive? := " ++ Test.toString buildArchive? ++ "," ++ .line ++ "buildArchive := " ++ "ELIDED" ++ "," ++ .line ++ "preferReleaseBuild := " ++ Test.toString preferReleaseBuild ++ "," ++ .line ++ "testDriver := " ++ Test.toString testDriver ++ "," ++ .line ++ "testDriverArgs := " ++ Test.toString testDriverArgs ++ "," ++ .line ++ "lintDriver := " ++ Test.toString lintDriver ++ "," ++ .line ++ "lintDriverArgs := " ++ Test.toString lintDriverArgs ++ "," ++ .line ++ "version := " ++ Test.toString version ++ "," ++ .line ++ "versionTags := " ++ Test.toString versionTags ++ "," ++ .line ++ "description := " ++ Test.toString description ++ "," ++ .line ++ "keywords := " ++ Test.toString keywords ++ "," ++ .line ++ "homepage := " ++ Test.toString homepage ++ "," ++ .line ++ "license := " ++ Test.toString license ++ "," ++ .line ++ "licenseFiles := " ++ Test.toString licenseFiles ++ "," ++ .line ++ "readmeFile := " ++ Test.toString readmeFile ++ "," ++ .line ++ "reservoir := " ++ Test.toString reservoir) ++ "}"
instance : Test Lake.Dependency where
  toString
    | {name, scope, version?, src?, opts} =>
      "{" ++ .group (.nest 2 <| "name := `" ++ name.toString ++ "," ++ .line ++ "scope := " ++ scope.quote ++ "," ++ .line ++ s!"version := {version?}" ++ "," ++ .line ++ "src? := " ++ Test.toString src? ++ "," ++ .line ++ "opts := " ++ Test.toString opts) ++ .line ++ "}"

instance : Test Lake.Toml.DecodeError where
  toString
    | {ref, msg} => s!"{msg} at {ref}"

instance {α : Type u} {β : Type v} : Test (α → β) where
  toString _ := "#<fun>"

/--
info: {toLeanConfig, name, srcDir, roots, globs, libName, extraDepTargets, precompileModules, defaultFacets, nativeFacets}
"{" ++ .group (.nest 2 <| "toLeanConfig := " ++ Test.toString toLeanConfig ++ "," ++ .line ++ "name := " ++ Test.toString name ++ "," ++ .line ++ "srcDir := " ++ Test.toString srcDir ++ "," ++ .line ++ "roots := " ++ Test.toString roots ++ "," ++ .line ++ "globs := " ++ Test.toString globs ++ "," ++ .line ++ "libName := " ++ Test.toString libName ++ "," ++ .line ++ "extraDepTargets := " ++ Test.toString extraDepTargets ++ "," ++ .line ++ "precompileModules := " ++ Test.toString precompileModules ++ "," ++ .line ++ "defaultFacets := " ++ Test.toString defaultFacets ++ "," ++ .line ++ "nativeFacets := " ++ Test.toString nativeFacets) ++ "}"
-/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let fs := getStructureFields (← getEnv) ``Lake.LeanLibConfig |>.toList
  IO.println <| "{" ++ String.intercalate ", " (fs.map (·.toString)) ++ "}"
  IO.println <|
    "\"{\" ++ .group (.nest 2 <| " ++
    String.intercalate " ++ \",\" ++ .line ++ " (fs.map (fun f => s!"\"{f} := \" ++ {if f == `buildArchive then "\"ELIDED\"" else s!"Test.toString {f}"}")) ++
    ") ++ \"}\""
instance : Test (Lake.LeanLibConfig) where
  toString
    | {toLeanConfig, name, srcDir, roots, globs, libName, extraDepTargets, precompileModules, defaultFacets, nativeFacets} =>
      "{" ++ .group (.nest 2 <| "toLeanConfig := " ++ Test.toString toLeanConfig ++ "," ++ .line ++ "name := " ++ Test.toString name ++ "," ++ .line ++ "srcDir := " ++ Test.toString srcDir ++ "," ++ .line ++ "roots := " ++ Test.toString roots ++ "," ++ .line ++ "globs := " ++ Test.toString globs ++ "," ++ .line ++ "libName := " ++ Test.toString libName ++ "," ++ .line ++ "extraDepTargets := " ++ Test.toString extraDepTargets ++ "," ++ .line ++ "precompileModules := " ++ Test.toString precompileModules ++ "," ++ .line ++ "defaultFacets := " ++ Test.toString defaultFacets ++ "," ++ .line ++ "nativeFacets := " ++ Test.toString nativeFacets) ++ "}"

/--
info: {toLeanConfig, name, srcDir, root, exeName, extraDepTargets, supportInterpreter, nativeFacets}
"{" ++ .group (.nest 2 <| "toLeanConfig := " ++ Test.toString toLeanConfig ++ "," ++ .line ++ "name := " ++ Test.toString name ++ "," ++ .line ++ "srcDir := " ++ Test.toString srcDir ++ "," ++ .line ++ "root := " ++ Test.toString root ++ "," ++ .line ++ "exeName := " ++ Test.toString exeName ++ "," ++ .line ++ "extraDepTargets := " ++ Test.toString extraDepTargets ++ "," ++ .line ++ "supportInterpreter := " ++ Test.toString supportInterpreter ++ "," ++ .line ++ "nativeFacets := " ++ Test.toString nativeFacets) ++ "}"
-/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let fs := getStructureFields (← getEnv) ``Lake.LeanExeConfig |>.toList
  IO.println <| "{" ++ String.intercalate ", " (fs.map (·.toString)) ++ "}"
  IO.println <|
    "\"{\" ++ .group (.nest 2 <| " ++
    String.intercalate " ++ \",\" ++ .line ++ " (fs.map (fun f => s!"\"{f} := \" ++ {if f == `buildArchive then "\"ELIDED\"" else s!"Test.toString {f}"}")) ++
    ") ++ \"}\""

instance : Test (Lake.LeanExeConfig) where
  toString
    | {toLeanConfig, name, srcDir, root, exeName, extraDepTargets, supportInterpreter, nativeFacets} =>
      "{" ++ .group (.nest 2 <| "toLeanConfig := " ++ Test.toString toLeanConfig ++ "," ++ .line ++ "name := " ++ Test.toString name ++ "," ++ .line ++ "srcDir := " ++ Test.toString srcDir ++ "," ++ .line ++ "root := " ++ Test.toString root ++ "," ++ .line ++ "exeName := " ++ Test.toString exeName ++ "," ++ .line ++ "extraDepTargets := " ++ Test.toString extraDepTargets ++ "," ++ .line ++ "supportInterpreter := " ++ Test.toString supportInterpreter ++ "," ++ .line ++ "nativeFacets := " ++ Test.toString nativeFacets) ++ "}"



/--
info: {dir, relDir, config, relConfigFile, relManifestFile, scope, remoteUrl, depConfigs, leanLibConfigs, leanExeConfigs, externLibConfigs, opaqueTargetConfigs, defaultTargets, scripts, defaultScripts, postUpdateHooks, testDriver, lintDriver}
"{" ++ .group (.nest 2 <| "dir := " ++ Test.toString dir ++ "," ++ .line ++ "relDir := " ++ Test.toString relDir ++ "," ++ .line ++ "config := " ++ Test.toString config ++ "," ++ .line ++ "relConfigFile := " ++ Test.toString relConfigFile ++ "," ++ .line ++ "relManifestFile := " ++ Test.toString relManifestFile ++ "," ++ .line ++ "scope := " ++ Test.toString scope ++ "," ++ .line ++ "remoteUrl := " ++ Test.toString remoteUrl ++ "," ++ .line ++ "depConfigs := " ++ Test.toString depConfigs ++ "," ++ .line ++ "leanLibConfigs := " ++ Test.toString leanLibConfigs ++ "," ++ .line ++ "leanExeConfigs := " ++ Test.toString leanExeConfigs ++ "," ++ .line ++ "externLibConfigs := " ++ Test.toString externLibConfigs ++ "," ++ .line ++ "opaqueTargetConfigs := " ++ Test.toString opaqueTargetConfigs ++ "," ++ .line ++ "defaultTargets := " ++ Test.toString defaultTargets ++ "," ++ .line ++ "scripts := " ++ Test.toString scripts ++ "," ++ .line ++ "defaultScripts := " ++ Test.toString defaultScripts ++ "," ++ .line ++ "postUpdateHooks := " ++ Test.toString postUpdateHooks ++ "," ++ .line ++ "testDriver := " ++ Test.toString testDriver ++ "," ++ .line ++ "lintDriver := " ++ Test.toString lintDriver) ++ "}"
-/
#guard_msgs in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let fs := getStructureFields (← getEnv) ``Lake.Package |>.toList
  IO.println <| "{" ++ String.intercalate ", " (fs.map (·.toString)) ++ "}"
  IO.println <|
    "\"{\" ++ .group (.nest 2 <| " ++
    String.intercalate " ++ \",\" ++ .line ++ " (fs.map (fun f => s!"\"{f} := \" ++ {if f == `buildArchive then "\"ELIDED\"" else s!"Test.toString {f}"}")) ++
    ") ++ \"}\""

instance : Test Lake.Package where
  toString
    | {dir, relDir, config, relConfigFile, relManifestFile, scope, remoteUrl, depConfigs, leanLibConfigs, leanExeConfigs, externLibConfigs, opaqueTargetConfigs, defaultTargets, scripts, defaultScripts, postUpdateHooks, testDriver, lintDriver} =>
      "{" ++ .group (.nest 2 <| "dir := " ++ Test.toString dir ++ "," ++ .line ++ "relDir := " ++ Test.toString relDir ++ "," ++ .line ++ "config := " ++ Test.toString config ++ "," ++ .line ++ "relConfigFile := " ++ Test.toString relConfigFile ++ "," ++ .line ++ "relManifestFile := " ++ Test.toString relManifestFile ++ "," ++ .line ++ "scope := " ++ Test.toString scope ++ "," ++ .line ++ "remoteUrl := " ++ Test.toString remoteUrl ++ "," ++ .line ++ "depConfigs := " ++ Test.toString depConfigs ++ "," ++ .line ++ "leanLibConfigs := " ++ Test.toString leanLibConfigs ++ "," ++ .line ++ "leanExeConfigs := " ++ Test.toString leanExeConfigs ++ "," ++ .line ++ "externLibConfigs := " ++ Test.toString externLibConfigs ++ "," ++ .line ++ "opaqueTargetConfigs := " ++ Test.toString opaqueTargetConfigs ++ "," ++ .line ++ "defaultTargets := " ++ Test.toString defaultTargets ++ "," ++ .line ++ "scripts := " ++ Test.toString scripts ++ "," ++ .line ++ "defaultScripts := " ++ Test.toString defaultScripts ++ "," ++ .line ++ "postUpdateHooks := " ++ Test.toString postUpdateHooks ++ "," ++ .line ++ "testDriver := " ++ Test.toString testDriver ++ "," ++ .line ++ "lintDriver := " ++ Test.toString lintDriver) ++ "}"

open Lake Toml in
def report [Monad m] [Lean.MonadLog m] [MonadFileMap m] [Test α] (val : α) (errs : Array DecodeError) : m String := do
    let mut result := ""
    unless errs.isEmpty do
      result := result ++ "Errors:\n"
      for e in errs do
        result := result ++ (← posStr e.ref) ++ e.msg ++ "\n"
      result := result ++ "-------------\n"
    result := result ++ (Test.toString val).pretty ++ "\n"
    pure result
where
  posStr (stx : Syntax) : m String := do
    let text ← getFileMap
    let fn ← getFileName <&> (System.FilePath.fileName · |>.getD "")
    let head := (stx.getHeadInfo? >>= SourceInfo.getPos?) <&> text.utf8PosToLspPos
    let tail := (stx.getTailInfo? >>= SourceInfo.getPos?) <&> text.utf8PosToLspPos
    if let some ⟨l, c⟩ := head then
      if let some ⟨l', c'⟩ := tail then
        if l = l' then return s!"{fn}:{l}:{c}-{c'}: "
        else return s!"{fn}:{l}-{l'}:{c}-{c'}: "
      return s!"{fn}:{l}:{c}: "
    return ""

end Toml

open Lean.Parser in
open Lake Toml in
def checkToml (α : Type) [Monad m] [MonadLiftT BaseIO m] [MonadFileMap m] [Lean.MonadLog m] [Inhabited α] [DecodeToml α] [Toml.Test α] (str : String) (what : Name) : m (Except String String) := do
  let ictx := mkInputContext str "<example TOML>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .error err =>
    return .error <| toString (← err.unreported.toArray.mapM (·.toString))
  | .ok table =>
    let ((out : α), errs) := (table.tryDecode what) #[]
    .ok <$> report out errs



open Lean.Parser in
open Lake Toml in
def checkTomlPackage [Monad m] [MonadLiftT BaseIO m] [MonadFileMap m] [Lean.MonadLog m] [Lean.MonadError m] (str : String) : m (Except String String) := do
  let ictx := mkInputContext str "<example TOML>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .error err =>
    return .error <| toString (← err.unreported.toArray.mapM (·.toString))
  | .ok table =>
    let .ok env ←
      EIO.toBaseIO <|
        Lake.Env.compute {home:=""} {sysroot:=""} none none
      | throwError "Failed to make env"
    let cfg : LoadConfig := {lakeEnv := env, wsDir := "."}
    let ((pkg : Lake.Package), errs) := Id.run <| (StateT.run · #[]) <| do
      let config ← tryDecode <| PackageConfig.decodeToml table
      let leanLibConfigs ← mkRBArray (·.name) <$> table.tryDecodeD `lean_lib #[]
      let leanExeConfigs ← mkRBArray (·.name) <$> table.tryDecodeD `lean_exe #[]
      let defaultTargets ← table.tryDecodeD `defaultTargets #[]
      let defaultTargets := defaultTargets.map stringToLegalOrSimpleName
      let depConfigs ← table.tryDecodeD `require #[]
      pure {
        dir := cfg.pkgDir
        relDir := cfg.relPkgDir
        relConfigFile := cfg.relConfigFile
        scope := cfg.scope
        remoteUrl := cfg.remoteUrl
        config, depConfigs, leanLibConfigs, leanExeConfigs
        defaultTargets
      }

    .ok <$> report pkg errs


structure LakeTomlOpts where
  /-- The type to check it against -/
  type : Name
  /-- The field of the table to use -/
  field : Name
  /-- Whether to keep the result -/
  «show» : Bool

def LakeTomlOpts.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LakeTomlOpts :=
  LakeTomlOpts.mk <$> .positional `type .resolvedName <*> .positional `field .name <*> (.named `show .bool true <&> (·.getD true))



@[directive_expander lakeToml]
def lakeToml : DirectiveExpander
  | args, contents => do
    let opts ← LakeTomlOpts.parse.run args
    let (expected, contents) := contents.partition fun
      | `(block| ``` expected | $_ ```) => true
      | _ => false
    let toml := contents.filterMap fun
      | `(block| ``` toml $_* | $tomlStr ```) => some tomlStr
      | _ => none
    if h : expected.size ≠ 1 then
      throwError "Expected exactly 1 'expected' code block, got {expected.size}"
    else
      let `(block| ```expected | $expectedStr ```) := expected[0]
        | throwErrorAt expected[0] "Expected an 'expected' code block with no arguments"
      if h : toml.size ≠ 1 then
        throwError "Expected exactly 1 toml code block, got {toml.size}"
      else
        let tomlStr := toml[0]
        let tomlInput := tomlStr.getString ++ "\n"
        let v ← match opts.field, opts.type with
        | `_root_, ``Lake.PackageConfig =>
          match (← checkTomlPackage ((← parserInputString tomlStr) ++ "\n")) with
          | .error e => throwErrorAt tomlStr e
          | .ok v => pure v
        | `_root_, other =>
          throwError "'_root_' can only be used with 'Lake.PackageConfig'"
        | f, ``Lake.Dependency =>
          match (← checkToml (Array Lake.Dependency) ((← parserInputString tomlStr) ++ "\n") f) with
          | .error e => throwErrorAt tomlStr e
          | .ok v => pure v
        | `lean_lib, ``Lake.LeanLibConfig =>
          match (← checkToml (Array Lake.LeanLibConfig) ((← parserInputString tomlStr) ++ "\n") `lean_lib) with
          | .error e => throwErrorAt tomlStr e
          | .ok v => pure v
        | `lean_exe, ``Lake.LeanExeConfig =>
          match (← checkToml (Array Lake.LeanExeConfig) ((← parserInputString tomlStr) ++ "\n") `lean_exe) with
          | .error e => throwErrorAt tomlStr e
          | .ok v => pure v
        | _, _ => throwError s!"Unsupported type {opts.type}"

        discard <| expectString "elaborated configuration" expectedStr v (useLine := (·.any (!·.isWhitespace)))

        contents.mapM elabBlock
