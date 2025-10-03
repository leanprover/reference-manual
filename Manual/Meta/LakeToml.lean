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
import Manual.Meta.LakeToml.Toml
import Manual.Meta.LakeToml.Test

import Lake.Toml.Decode
import Lake.Load.Toml


open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open Lean Elab
open SubVerso.Highlighting Highlighted
open scoped Lean.Doc.Syntax
open Lean.Elab.Tactic.GuardMsgs

set_option guard_msgs.diff true

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
  | target
  | other (name : Name) (what : String) (whatPlural : Option String)
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
    | .target => mkCApp ``FieldType.target #[]
    | .other x y z => mkCApp ``FieldType.other #[quote x, quote y, quote z]


open Output Html in
def FieldType.toHtml (plural : Bool := false) : FieldType → Html
  | .string => if plural then "strings" else "String"
  | .stringOf x => s!"{x} (as string{if plural then "s" else ""}"
  | .version => if plural then "version strings" else "Version string"
  | .path => if plural then "paths" else "Path"
  | .array t => (if plural then "arrays of " else "Array of ") ++ t.toHtml true
  | .other _ y none => if plural then y ++ "s" else y
  | .other _ y (some z) => if plural then z else y
  | .bool => if plural then "Booleans" else "Boolean"
  | .target => if plural then "targets" else "target"
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

def Inline.tomlField (inTable : Name) (field : Name) : Inline where
  name := `Manual.Inline.tomlField
  data := ToJson.toJson (inTable, field)

def Block.tomlTable (arrayKey : Option String) (name : String) (typeName : Name) : Block where
  name := `Manual.Block.tomlTable
  data := ToJson.toJson (arrayKey, name, typeName)


structure TomlFieldOpts where
  inTable : Name
  field : Name
  typeDesc : String
  typeDescPlural : String
  type : Name
  sort : Option Nat

instance [Inhabited α] [Applicative f] : Inhabited (f α) where
  default := pure default

@[specialize]
private partial def many [Applicative f] [Alternative f] (p : f α) : f (List α) :=
  ((· :: ·) <$> p <*> many p) <|> pure []


def TomlFieldOpts.parse  [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m TomlFieldOpts :=
  TomlFieldOpts.mk <$> .positional `inTable .name <*> .positional `field .name <*> .positional `typeDesc .string <*> .positional `typeDescPlural .string <*> .positional `type .resolvedName <*> .named `sort .nat true

instance : Quote Empty where
  quote := nofun

@[directive_expander tomlField]
def tomlField : DirectiveExpander
  | args, contents => do
    let {inTable, field, typeDesc, typeDescPlural, type, sort} ← TomlFieldOpts.parse.run args
    let field : Toml.Field Empty := {name := field, type := .other type typeDesc typeDescPlural, docs? := none}
    let contents ← contents.mapM elabBlock
    return #[← ``(Block.other (Block.tomlField $(quote sort) $(quote inTable) $(quote field)) #[$contents,*])]

open Verso.Search in
def tomlTableDomainMapper := {
  displayName := "Lake TOML Table",
  className := "lake-toml-table-domain",
  dataToSearchables := "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => {
    let arrayKey = value[0].data.arrayKey;
    let arr = arrayKey ? `[[${arrayKey}]] — ` : '';
    return {
      searchKey: arr + value[0].data.description,
      address: `${value[0].address}#${value[0].id}`,
      domainId: 'Manual.lakeTomlTable',
      ref: value,
    }})
"
  : DomainMapper }.setFont { family := .code }

open Verso.Search in
def tomlFieldDomainMapper := {
  displayName := "Lake TOML Field",
  className := "lake-toml-field-domain",
  dataToSearchables := "(domainData) =>
    Object.entries(domainData.contents).map(([key, value]) => {
      let tableArrayKey = value[0].data.tableArrayKey;
      let arr = tableArrayKey ? `[[${tableArrayKey}]]` : 'package configuration';
      return {
        searchKey: `${value[0].data.field} in ${arr}`,
        address: `${value[0].address}#${value[0].id}`,
        domainId: 'Manual.lakeTomlField',
        ref: value,
      }})"
  : DomainMapper }.setFont { family := .code }

@[block_extension Block.tomlField]
def Block.tomlField.descr : BlockDescr where
  init s := s.addQuickJumpMapper tomlFieldDomain tomlFieldDomainMapper

  traverse id info _ := do
    let .ok (_, inTable, field) := FromJson.fromJson? (α := Option Nat × Name × Toml.Field Empty) info
      | do logError "Failed to deserialize field doc data"; pure none

    let tableArrayKey : Option Json := (← get).getDomainObject? tomlTableDomain inTable.toString |>.bind fun t =>
      t.data.getObjVal? "arrayKey" |>.toOption

    modify fun s =>
      let name := s!"{inTable} {field.name}"
      s |>.saveDomainObject tomlFieldDomain name id
        |>.saveDomainObjectData tomlFieldDomain name (json%{
          "table": $inTable.toString,
          "tableArrayKey": $(tableArrayKey.getD .null),
          "field": $field.name.toString
        })
    discard <| externalTag id (← read).path s!"{inTable}-{field.name}"
    pure none
  toTeX := none

  extraCss := [".namedocs .label a { color: inherit; }"]

  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (_, _inTable, field) := FromJson.fromJson? (α := Option Nat × Name × Toml.Field Empty) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize field doc data"; pure .empty
      let sig : Html := {{ {{field.name.toString}} }}

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <dt {{idAttr}}>
          <code class="field-name">{{sig}}</code>
        </dt>
        <dd>
            <p><strong>"Contains:"</strong>" " {{field.type.toHtml}}</p>
            {{← contents.mapM goB}}
        </dd>
      }}
  localContentItem _ info _ := open Verso.Output Html in do
    let (_, _inTable, field) ← FromJson.fromJson? (α := Option Nat × Name × Toml.Field Empty) info
    let name := field.name.toString
    pure #[
      (name, {{<code class="field-name">{{name}}</code>}})
    ]

private partial def flattenBlocks (blocks : Array (Block genre)) : Array (Block genre) :=
  blocks.flatMap fun
    | .concat bs =>
      flattenBlocks bs
    | other => #[other]

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

  toHtml := some <| fun _goI goB _id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .arr #[.str title, _fields] := info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize field category doc data"; pure .empty

      let (nonField, field) :=
        flattenBlocks contents |>.partition fun
          | .other {name := `Manual.Block.tomlField, ..} _ => false
          | _ => true

      return {{
        <div class="field-category">
          <p><strong>{{title}}":"</strong></p>
          {{← nonField.mapM goB}}
          <dl>
            {{← field.mapM goB}}
          </dl>
        </div>
      }}

@[block_extension Block.tomlTable]
def Block.tomlTable.descr : BlockDescr where
  init s :=
    s.addQuickJumpMapper tomlTableDomain tomlTableDomainMapper

  traverse id info _ := do
    let .ok (arrayKey, humanName, typeName) := FromJson.fromJson? (α := Option String × String × Name) info
        | do logError "Failed to deserialize FFI doc data"; pure none
    let arrayKeyJson := arrayKey.map Json.str |>.getD Json.null
    modify fun s =>
      s |>.saveDomainObject tomlTableDomain typeName.toString id
        |>.saveDomainObjectData tomlTableDomain typeName.toString (json%{"description": $humanName, "type": $typeName.toString, "arrayKey": $arrayKeyJson})

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
      let .ok (arrayKey, humanName, typeName) := FromJson.fromJson? (α := Option String × String × Name) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize Lake TOML table doc data"; pure .empty

      let tableArrayName : Option Toml.Highlighted := arrayKey.map fun k =>
        .tableHeader <| .tableDelim (.text "[[") ++ .tableName (some typeName.toString) (.key (some k) (.text k)) ++ .tableDelim (.text "]]")

      -- Don't include links here because they'd just be self-links anyway
      let tableArrayName : Option Html := tableArrayName.map (Toml.Highlighted.toHtml (fun _ => none) (fun _ _ => none))

      let sig : Html := {{ {{humanName}} {{tableArrayName.map ({{" — " <code class="toml">{{·}}</code> }}) |>.getD .empty }} }}

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
      let mut categorized : Std.HashMap String (Array (Block Genre.Manual)) := {}
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
        | (_, some title, .other which contents) =>
          let inCategory := categorized.getD title #[]
          .other which (contents ++ inCategory)
        | (_, _, blk) => blk


      let uncatHtml ← uncategorized.mapM goB
      let catHtml ← categories.mapM goB

      let fieldHeader := {{
        <p>
          <strong>
            {{if categories.isEmpty then "Fields:" else "Other Fields:"}}
          </strong>
        </p>
      }}

      let fieldHtml := {{
        {{if categories.isEmpty then .empty else catHtml}}
        {{if uncategorized.isEmpty then .empty
          else {{
            <div class="field-category">
              {{fieldHeader}}
              <dl class="toml-table-field-spec">
                {{uncatHtml}}
              </dl>
            </div>
          }}
        }}
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

  localContentItem _ info _ := open Verso.Output Html in do
    let (arrayKey, humanName, typeName) ← FromJson.fromJson? (α := Option String × String × Name) info
    if let some arrayKey := arrayKey then
      pure #[(s!"[[{arrayKey}]]", {{<code>s!"[[{arrayKey}]]"</code>}})]
    else
      pure #[(humanName, {{ {{humanName}} }})]


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
theorem builtTypes_exhaustive (isLower : s.decapitalize = s) : s ∈ buildTypes ↔ (Lake.BuildType.ofString? s).isSome := by
  simp only [buildTypes]
  constructor
  . intro h
    simp only [Lake.BuildType.ofString?]
    split <;> try (simp; done)
    simp_all
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
                else if type.isConstOf ``Lake.WorkspaceConfig then some (.other ``Lake.WorkspaceConfig "Workspace configuration" none)
                else if type.isConstOf ``Lake.BuildType then some (.oneOf buildTypes)
                else if type.isConstOf ``Lake.StdVer then some .version
                else if type.isConstOf ``Lake.StrPat then some (.other ``Lake.StrPat "String pattern" none)
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``Lean.LeanOption then some (.array (.other ``Lean.LeanOption "Lean option" none))
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``String then some (.array .string)
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``Name then some (.array .string)
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``System.FilePath then some (.array .path)
                else if type.isAppOfArity ``Array 1 && (type.getArg! 0).isConstOf ``Lake.PartialBuildKey then some (.array .target)
                else if type.isAppOfArity ``Option 1 && (type.getArg! 0).isConstOf ``Bool then some (.option .bool)
                else if type.isAppOfArity ``Option 1 && (type.getArg! 0).isConstOf ``String then some (.option .string)
                else if type.isAppOfArity ``Option 1 && (type.getArg! 0).isConstOf ``System.FilePath then some (.option .path)
                else if type.isAppOfArity ``Lake.TargetArray 1 && (type.getArg! 0).isConstOf ``Lake.Dynlib then
                  some (.array (.other ``Lake.Dynlib "dynamic library" "dynamic libraries"))
                else if type.isAppOfArity ``Lake.TargetArray 1 && (type.getArg! 0).isConstOf ``System.FilePath then
                  some (.array .path)
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

def Table.toBlock (arrayKey : Option String) (docs : Array (Block Genre.Manual)) (t : Table (Array (Block Genre.Manual))) : Array (Block Genre.Manual) :=
  let (fieldBlocks, notFields) := docs.partition (fun b => b matches Block.other {name:=`Manual.Block.tomlField, .. : Genre.Manual.Block} ..)

  #[.other (Block.tomlTable arrayKey t.name t.typeName) <| notFields ++ (fieldBlocks ++ t.fields.map (Field.toBlock t.typeName))]

end

end Toml

structure TomlTableOpts where
  /--
  `none` to describe the root of the configuration, or a key that points at a table array to
  describe a nested entry.
  -/
  arrayKey : Option String
  description : String
  name : Name
  skip : List Name

def TomlTableOpts.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m TomlTableOpts :=
  TomlTableOpts.mk <$> .positional `key arrayKey <*> .positional `description .string <*> .positional `name .resolvedName <*> many (.named `skip .name false)
where
  arrayKey := {
    description := "'root' for the root table, or a string that contains a key for nested tables",
    signature := .Ident ∪ .String
    get
      | .name n =>
        if n.getId == `root then pure none
        else throwErrorAt n "Expected 'root' or a string"
      | .str s => pure (some s.getString)
      | .num n => throwErrorAt n "Expected 'root' or a string"
  }


open Markdown in
/--
Interpret a structure type as a TOML table, and generate docs.
-/
@[directive_expander tomlTableDocs]
def tomlTableDocs : DirectiveExpander
  | args, contents => do
    let {arrayKey, description, name, skip} ← TomlTableOpts.parse.run args
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

    return #[← `(Block.concat (Toml.Table.toBlock $(quote arrayKey) #[$(docsStx),* , $userContents,*] $tableStx))]



namespace Toml


instance [Test α] : Test (Lake.OrdNameMap α) where
  toString xs := Id.run do
    let mut out : Std.Format := Std.Format.nil
    for (k, v) in xs.toTreeMap do
      out := out ++ .group (.nest 2 <| Test.toString k ++ " ↦" ++ .line ++ Test.toString v) ++ "," ++ .line
    return .group (.nest 2 <| "{" ++ out) ++ "}"

instance [{n : Name} → Test (f n)] : Test (Lake.DNameMap f) where
  toString xs := Id.run do
    let mut out : Std.Format := Std.Format.nil
    for ⟨k, v⟩ in xs do
      out := out ++ .group (.nest 2 <| Test.toString k ++ " ↦" ++ .line ++ Test.toString v) ++ "," ++ .line
    return .group (.nest 2 <| "{" ++ out) ++ "}"



mutual

partial def testPatDescr [Test α] [Test β] : (Lake.PatternDescr α β) → Std.Format
  | .not x => .group <| .nest 2 <| ".not" ++ .line ++ testPat x
  | .coe x => .group <| .nest 2 <| ".coe" ++ .line ++ Test.toString x
  | .any xs => .group <| .nest 2 <| ".any" ++ .line ++ "#[" ++ arrElems (xs.map testPat) ++ "]"
  | .all xs => .group <| .nest 2 <| ".all" ++ .line ++ "#[" ++ arrElems (xs.map testPat) ++ "]"
where
  arrElems (xs : Array Std.Format) : Std.Format :=
    .group <| .nest 2 <| (Std.Format.text "," ++ .line).joinSep xs.toList

partial def testPat [Test α] [Test β] : (Lake.Pattern α β) → Std.Format
  | {filter, name, descr?} =>
    let fields : List Std.Format := [
      "filter :=" ++ .line ++ Test.toString filter,
      "name :=" ++ .line ++ Test.toString name,
      "descr? :=" ++ .line ++ Test.toString (descr?.map testPatDescr),
    ]
    .group <| (.nest 2 <| "{" ++ .line ++ (Std.Format.text "," ++ .line).joinSep fields) ++ "}"
end

instance [Test α] [Test β] : Test (Lake.PatternDescr α β) := ⟨testPatDescr⟩
instance [Test α] [Test β] : Test (Lake.Pattern α β) := ⟨testPat⟩

deriving instance Repr for Lake.StrPatDescr

instance : Test (Lake.Script) where
  toString s := s!"#<script {s.name}>"

instance : Test (Lake.ExternLibConfig n n') where
  toString _ := s!"#<extern lib>"

instance : Test (Lake.OpaqueTargetConfig n n') where
  toString _ := s!"#<opaque target>"

instance : Test (Lake.OpaquePostUpdateHook α) where
  toString _ := s!"#<post-update-hook>"

instance : Test Lake.Toml.DecodeError where
  toString
    | {ref, msg} => s!"{msg} at {ref}"

deriving instance Test for Lake.Dependency
deriving instance Test for Lake.PackageConfig
deriving instance Test for Lake.LeanLibConfig
deriving instance Test for Lake.LeanExeConfig

instance : Test (Lake.ConfigType kind pkg name) where
  toString :=
    match kind with
    | `lean_lib => fun (x : Lake.LeanLibConfig name) => Test.toString x
    | `lean_exe => fun (x : Lake.LeanExeConfig name) => Test.toString x
    | `extern_lib => fun (x : Lake.ExternLibConfig pkg name) => Test.toString x
    | .anonymous => fun (x : Lake.OpaqueTargetConfig pkg name) => Test.toString x
    | _ => fun _ => "Impossible!"

instance : Test Lake.CacheRef where
  toString _ := "#<cacheref>"

private def contains (fmt : Format) (c : Char) : Bool :=
  match fmt with
  | .text s => s.contains c
  | .tag _ x | .group x .. | .nest _ x => contains x c
  | .append x y => contains x c || contains y c
  | .align .. | .line | .nil => false

instance [Test α] : Test (Option α) where
  toString
    | none => "none"
    | some x =>
      let s := Test.toString x
      let s := if contains s '(' || contains s ' ' then "(" ++ s ++ ")" else s
      s!"some " ++ s

deriving instance Test for Lake.ConfigDecl
deriving instance Test for Lake.PConfigDecl
deriving instance Test for Lake.NConfigDecl

deriving instance Test for Lake.Package



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

section

variable [Monad m] [MonadLiftT BaseIO m] [MonadFileMap m] [Lean.MonadLog m]

open Lean.Parser in
open Lake Toml in
def checkToml (α : Type)  [Inhabited α] [DecodeToml α] [Toml.Test α] (str : String) (what : Name) : m (Except String String) := do
  let ictx := mkInputContext str "<example TOML>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .error err =>
    return .error <| toString (← err.unreported.toArray.mapM (·.toString))
  | .ok tbl =>
    let .ok (out : α) errs := (tbl.tryDecode what).run #[]
    .ok <$> report out errs

structure Named (α : Name → Type u) where
  name : Name
  val : α name

instance [(n : Name) → Toml.Test (α n)] : Toml.Test (Named α) where
  toString
    | ⟨n, v⟩ => "{ " ++ .group (.nest 2 <| "name := " ++ n.toString ++ "," ++ .line ++ "val := " ++ Toml.Test.toString v ++ "}")

instance [(n : Name) →  Lake.DecodeToml (α n)] : Lake.DecodeToml (Named α) where
  decode v := do
    let table ← v.decodeTable --
    let name ← Lake.stringToLegalOrSimpleName <$> table.decode `name
    let val ← Lake.DecodeToml.decode v
    return ⟨name, val⟩

open Lean.Parser in
open Lake Toml in
def checkTomlArrayWithName (α : Name → Type) [(n : Name) → Inhabited (α n)] [(n : Name) → DecodeToml (α n)] [(n : Name) → Toml.Test (α n)] (str : String) (what : Name) : m (Except String String) := do
  let ictx := mkInputContext str "<example TOML>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .error err =>
    return .error <| toString (← err.unreported.toArray.mapM (·.toString))
  | .ok tbl =>
    let .ok (name : Name) errs := (tbl.tryDecode `name).run #[]
    let .ok out errs := (tbl.tryDecode what).run errs
    .ok <$> report (out : α name) errs


-- TODO this became private upstream, so it's been copied to fix the build.
-- Negotiate a public API.
open Lake Toml in
private def decodeTargetDecls
  (pkg : Name) (t : Table)
: DecodeM (Array (PConfigDecl pkg) × DNameMap (NConfigDecl pkg)) := do
  let r := (#[], {})
  let r ← go r LeanLib.keyword LeanLib.configKind LeanLibConfig.decodeToml
  let r ← go r LeanExe.keyword LeanExe.configKind LeanExeConfig.decodeToml
  let r ← go r InputFile.keyword InputFile.configKind InputFileConfig.decodeToml
  let r ← go r InputDir.keyword InputDir.configKind InputDirConfig.decodeToml
  return r
where
  go r kw kind (decode : {n : Name} → Table → DecodeM (ConfigType kind pkg n)) := do
    let some tableArrayVal := t.find? kw | return r
    let some vals ← tryDecode? tableArrayVal.decodeValueArray | return r
    vals.foldlM (init := r) fun r val => do
      let some t ← tryDecode? val.decodeTable | return r
      let some name ← tryDecode? <| stringToLegalOrSimpleName <$> t.decode `name
        | return r
      let (decls, map) := r
      if let some orig := map.get? name then
        modify fun es => es.push <| .mk val.ref s!"\
          {pkg}: target '{name}' was already defined as a '{orig.kind}', \
          but then redefined as a '{kind}'"
        return (decls, map)
      else
        let config ← @decode name t
        let decl : NConfigDecl pkg name :=
          -- Safety: By definition, config kind = facet kind for declarative configurations.
          unsafe {pkg, name, kind, config, wf_data := lcProof}
        return (decls.push decl.toPConfigDecl, map.insert name decl)

open Lean.Parser in
open Lake Toml in
def checkTomlPackage [Lean.MonadError m] (str : String) : m (Except String String) := do
  let ictx := mkInputContext str "<example TOML>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .error err =>
    return .error <| toString (← err.unreported.toArray.mapM (·.toString))
  | .ok tbl =>
    let .ok env ←
      EIO.toBaseIO <|
        Lake.Env.compute {home:=""} {sysroot:=""} none none
      | throwError "Failed to make env"
    let cfg : LoadConfig := {lakeEnv := env, wsDir := "."}
    let .ok (pkg : Lake.Package) errs := Id.run <| (EStateM.run · #[]) <| do
      let name ← stringToLegalOrSimpleName <$> tbl.tryDecode `name
      let config : PackageConfig name name ← PackageConfig.decodeToml tbl
      let (targetDecls, targetDeclMap) ← decodeTargetDecls name tbl
      let defaultTargets ← tbl.tryDecodeD `defaultTargets #[]
      let defaultTargets := defaultTargets.map stringToLegalOrSimpleName
      let depConfigs ← tbl.tryDecodeD `require #[]
      pure {
        dir := cfg.pkgDir
        relDir := cfg.relPkgDir
        relConfigFile := cfg.relConfigFile
        scope := cfg.scope
        remoteUrl := cfg.remoteUrl
        configFile := cfg.configFile
        config, depConfigs, targetDecls, targetDeclMap
        defaultTargets, name
        origName := name
      }

    .ok <$> report pkg errs

end

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
          -- TODO get the name first!
          match (← checkToml (Array (Named Lake.LeanLibConfig)) ((← parserInputString tomlStr) ++ "\n") `lean_lib) with
          | .error e => throwErrorAt tomlStr e
          | .ok v => pure v
        | `lean_exe, ``Lake.LeanExeConfig =>
          match (← checkToml (Array (Named Lake.LeanExeConfig)) ((← parserInputString tomlStr) ++ "\n") `lean_exe) with
          | .error e => throwErrorAt tomlStr e
          | .ok v => pure v
        | _, _ => throwError s!"Unsupported type {opts.type}"

        discard <| expectString "elaborated configuration output" expectedStr v (useLine := (·.any (!·.isWhitespace)))

        contents.mapM (elabBlock ⟨·⟩)

@[role_expander tomlField]
def tomlFieldInline : RoleExpander
  | args, inlines => do
    let table ← (ArgParse.positional `table .resolvedName).run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the field name"
    let name := name.getString

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other (Manual.Inline.tomlField $(quote table) $(quote name.toName)) #[Inline.code $(quote name)])]

@[inline_extension Manual.Inline.tomlField]
def tomlFieldInline.descr : InlineDescr where
  traverse _ _ _ := do
    pure none

  toTeX := none

  extraCss := [
r#"
.toml-field a {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
.toml-field a:hover {
  text-decoration: currentcolor underline solid;
}
"#]


  toHtml :=
    open Verso.Output.Html in
    some <| fun goB _id data content => do
      let .ok (tableName, fieldName) := fromJson? (α := Name × Name) data
        | HtmlT.logError s!"Failed to deserialize metadata for Lake option ref: {data}"; content.mapM goB

      if let some obj := (← read).traverseState.getDomainObject? tomlFieldDomain s!"{tableName} {fieldName}" then
        for id in obj.ids do
          if let some dest := (← read).traverseState.externalTags[id]? then
            return {{<code class="toml-field"><a href={{dest.link}}>{{fieldName.toString}}</a></code>}}
      else
        HtmlT.logError s!"No link destination for TOML field {tableName}:{fieldName}"

      pure {{<code class="toml-field">{{fieldName.toString}}</code>}}
