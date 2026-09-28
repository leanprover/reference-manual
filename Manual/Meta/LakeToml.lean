/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Manual.Meta.LakeToml.Toml

public import Manual.Meta.LakeToml.Table
public meta import Manual.Meta.LakeToml.Table
public import Manual.Meta.LakeToml.Check
public meta import Manual.Meta.LakeToml.Check
public meta import Manual.Meta.ExpectString
public meta import Manual.Meta.Basic
public meta import Verso.Doc.Elab.Block
public meta import VersoManual.Markdown
import MD4Lean.Basic

public section


open Verso ArgParse Doc Elab Genre.Manual Html Code
open Lean Elab
open SubVerso.Highlighting Highlighted
open Lean.Elab.Tactic.GuardMsgs
open Lean.Doc (CodeView)

set_option guard_msgs.diff true

namespace Manual


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

local instance [Inhabited α] [Applicative f] : Inhabited (f α) where
  default := pure default

meta section

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

end

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
private def tomlFieldDomainMapper := {
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
      | do reportError "Failed to deserialize field doc data"; pure none

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
        | do reportError "Failed to deserialize field doc data"; pure .empty
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

meta def TomlFieldCategoryOpts.parse [Monad m] [MonadError m] : ArgParse m TomlFieldCategoryOpts :=
  TomlFieldCategoryOpts.mk <$> .positional `title .string <*> many (.positional `field .name)

@[directive_expander tomlFieldCategory]
meta def tomlFieldCategory : DirectiveExpander
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
        | do reportError "Failed to deserialize field category doc data"; pure .empty

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
        | do reportError "Failed to deserialize FFI doc data"; pure none
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
        | do reportError "Failed to deserialize Lake TOML table doc data"; pure .empty

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

def Field.toBlock (inTable : Name) (f : Field (Array (Block Genre.Manual))) : Block Genre.Manual :=
  let (f, docs?) := f.takeDocs
  .other (Block.tomlField none inTable f) (docs?.getD #[])

def Table.toBlock (arrayKey : Option String) (docs : Array (Block Genre.Manual)) (t : Table (Array (Block Genre.Manual))) : Array (Block Genre.Manual) :=
  let (fieldBlocks, notFields) := docs.partition (fun b => b matches Block.other {name:=`Manual.Block.tomlField, .. : Genre.Manual.Block} ..)

  #[.other (Block.tomlTable arrayKey t.name t.typeName) <| notFields ++ (fieldBlocks ++ t.fields.map (Field.toBlock t.typeName))]


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

meta def TomlTableOpts.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m TomlTableOpts :=
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
meta def tomlTableDocs : DirectiveExpander
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



structure LakeTomlOpts where
  /-- The type to check it against -/
  type : Name
  /-- The field of the table to use -/
  field : Name
  /-- Whether to keep the result -/
  «show» : Bool

meta section

def LakeTomlOpts.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LakeTomlOpts :=
  LakeTomlOpts.mk <$> .positional `type .resolvedName <*> .positional `field .name <*> (.named `show .bool true <&> (·.getD true))



@[directive_expander lakeToml]
def lakeToml : DirectiveExpander
  | args, contents => do
    let opts ← LakeTomlOpts.parse.run args
    let (expected, contents) := contents.partition (namedCodeBlock `expected · |>.isSome)
    let toml := contents.filterMap (namedCodeBlock `toml ·)
    if h : expected.size ≠ 1 then
      throwError "Expected exactly 1 'expected' code block, got {expected.size}"
    else
      let some expectedStr := namedCodeBlock `expected expected[0]
        | throwErrorAt expected[0] "Expected an 'expected' code block with no arguments"
      if h : toml.size ≠ 1 then
        throwError "Expected exactly 1 toml code block, got {toml.size}"
      else
        let tomlStr := toml[0]
        let tomlInput := tomlStr.getVersoCodeBlock ++ "\n"
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

        discard <| expectString "elaborated configuration output" expectedStr v (useLine := (·.any (! Char.isWhitespace ·)))

        contents.mapM (elabBlock ⟨·⟩)

@[role_expander tomlField]
def tomlFieldInline : RoleExpander
  | args, inlines => do
    let table ← (ArgParse.positional `table .resolvedName).run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let some { content := name, .. } := CodeView.of arg
      | throwErrorAt arg "Expected code literal with the field name"
    let name := name.getVersoCode

    pure #[← `(show Verso.Doc.Inline Verso.Genre.Manual from .other (Manual.Inline.tomlField $(quote table) $(quote name.toName)) #[Inline.code $(quote name)])]

end

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
        | reportError s!"Failed to deserialize metadata for Lake option ref: {data}"; content.mapM goB

      if let some obj := (← read).traverseState.getDomainObject? tomlFieldDomain s!"{tableName} {fieldName}" then
        for id in obj.ids do
          if let some dest := (← read).traverseState.externalTags[id]? then
            return {{<code class="toml-field"><a href={{dest.link}}>{{fieldName.toString}}</a></code>}}
      else
        reportError s!"No link destination for TOML field {tableName}:{fieldName}"

      pure {{<code class="toml-field">{{fieldName.toString}}</code>}}
