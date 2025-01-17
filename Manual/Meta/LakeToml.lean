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

import Lake

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

def Block.tomlField (inTable : Name) (field : Toml.Field Empty) : Block where
  name := `Manual.Block.tomlField
  data := ToJson.toJson (inTable, field)

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

def TomlFieldOpts.parse  [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m TomlFieldOpts :=
  TomlFieldOpts.mk <$> .positional `inTable .name <*> .positional `field .name <*> .positional `typeDesc .string <*> .positional `type .resolvedName

instance : Quote Empty where
  quote := nofun

@[directive_expander tomlField]
def tomlField : DirectiveExpander
  | args, contents => do
    let {inTable, field, typeDesc, type} ← TomlFieldOpts.parse.run args
    let field : Toml.Field Empty := {name := field, type := .other type typeDesc, docs? := none}
    let contents ← contents.mapM elabBlock
    return #[← ``(Block.other (Block.tomlField $(quote inTable) $(quote field)) #[$contents,*])]


@[block_extension Block.tomlField]
def Block.tomlField.descr : BlockDescr where
  traverse id info _ := do
    let .ok (inTable, field) := FromJson.fromJson? (α := Name × Toml.Field Empty) info
      | do logError "Failed to deserialize FFI doc data"; pure none
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
      let .ok (inTable, field) := FromJson.fromJson? (α := Name × Toml.Field Empty) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize FFI doc data"; pure .empty
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

      let label := label.getD {{"field in TOML table"}}

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">{{label}}</span>
          <pre class="signature">{{sig}}</pre>
          <div class="text">
            <p><strong>"Contains:"</strong>" " {{field.type.toHtml}}</p>
            {{← contents.mapM goB}}
          </div>
        </div>
      }}

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
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (humanName, typeName) := FromJson.fromJson? (α := String × Name) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize FFI doc data"; pure .empty
      let sig : Html := {{ {{humanName}} }}

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">"TOML table"</span>
          <pre class="signature">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
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
                ast.blocks.mapM (blockFromMarkdownWithLean [])

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
  .other (Block.tomlField inTable f) (docs?.getD #[])

def Table.toBlock (docs : Array (Block Genre.Manual)) (t : Table (Array (Block Genre.Manual))) : Array (Block Genre.Manual) :=
  #[.other (Block.tomlTable t.name t.typeName) docs] ++
  t.fields.map (Field.toBlock t.typeName)

end

end Toml

instance [Inhabited α] [Applicative f] : Inhabited (f α) where
  default := pure default

@[specialize]
private partial def many [Applicative f] [Alternative f] (p : f α) : f (List α) :=
  ((· :: ·) <$> p <*> many p) <|> pure []

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
@[block_role_expander tomlTableDocs]
def tomlTableDocs : BlockRoleExpander
  | args, #[] => do
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

    return #[← `(Block.concat (Toml.Table.toBlock #[$(docsStx),*] $tableStx))]

  | _args, more => throwErrorAt more[0]! "Unexpected block argument"
