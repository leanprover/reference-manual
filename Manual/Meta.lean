/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
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

import Manual.Meta.Attribute
import Manual.Meta.Basic
import Manual.Meta.CheckMessages
import Manual.Meta.CustomStyle
import Manual.Meta.Env
import Manual.Meta.Example
import Manual.Meta.Figure
import Manual.Meta.LakeCheck
import Manual.Meta.LakeCmd
import Manual.Meta.LakeOpt
import Manual.Meta.LakeToml
import Manual.Meta.ParserAlias
import Manual.Meta.Syntax
import Manual.Meta.Tactics
import Manual.Meta.SpliceContents
import Manual.Meta.Markdown

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

@[directive_expander comment]
def comment : DirectiveExpander
  | _, _ => pure #[]

def Block.TODO : Block where
  name := `Manual.TODO

def Inline.TODO : Inline where
  name := `Manual.TODO

@[directive_expander TODO]
def TODO : DirectiveExpander
  | args, blocks => do
    ArgParse.done.run args
    PointOfInterest.save (← getRef) "TODO"
      (kind := .null)
      (detail? := some "Author's note")
    let content ← blocks.mapM elabBlock
    pure #[← `(Doc.Block.other Block.TODO #[$content,*])]

@[role_expander TODO]
def TODOinline : RoleExpander
  | args, inlines => do
    ArgParse.done.run args
    PointOfInterest.save (← getRef) "TODO"
      (kind := .null)
      (detail? := some "Author's note")
    let content ← inlines.mapM elabInline
    pure #[← `(Doc.Inline.other Inline.TODO #[$content,*])]


@[block_extension TODO]
def TODO.descr : BlockDescr where
  traverse _ _ _ := do
    if ← isDraft then pure none else pure (some <| .concat #[])
  toTeX := none
  extraCss := [r#"
div.TODO {
  border: 5px solid red;
  position: relative;
}
div.TODO::before {
  content: "TODO";
  position: absolute;
  top: 0;
  right: 0;
  color: red;
  font-size: large;
  font-weight: bold;
  transform: rotate(-90deg) translate(-2em);
}
"#]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="TODO">{{← content.mapM goB}}</div>}}

@[inline_extension TODO]
def TODO.inlineDescr : InlineDescr where
  traverse _ _ _ := do
    if ← isDraft then pure none else pure (some <| .concat #[])
  toTeX := none
  extraCss := [r#"
span.TODO {
  border: 3px solid red;
  display: inline;
  position: relative;
  float: right;
  clear: right;
  margin-top: 1rem;
  width: 15vw;
  margin-right: -17vw;
  color: red;
  font-size: large;
  font-weight: bold;
}
"#]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ _ content => do
      pure {{<span class="TODO">{{← content.mapM go}}</span>}}

def Inline.noVale : Inline where
  name := `Manual.noVale

structure NoValeConfig where
  why : String

def NoValeConfig.parse [Monad m] [MonadError m] : ArgParse m NoValeConfig :=
  NoValeConfig.mk <$> .positional `why .string

/--
Skip the grammar and style check of this text.

The string parameter should contain an explanation of why the text should be skipped.
-/
@[role_expander noVale]
def noVale : RoleExpander
  | args, contents => do
    let {why := _} ← NoValeConfig.parse.run args
    return #[← ``(Inline.other Inline.noVale #[$(← contents.mapM elabInline),*])]

@[inline_extension noVale]
def noVale.descr : InlineDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some <| fun go _ _ content => open Verso.Output.Html in do
    pure {{<span class="no-vale">{{← content.mapM go}}</span>}}

structure PlannedConfig where
  issue : Option Nat

def PlannedConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m PlannedConfig :=
  PlannedConfig.mk <$> ((some <$> .positional `issue .nat) <|> pure none)

def Block.planned : Block where
  name := `Manual.planned

@[directive_expander planned]
def planned : DirectiveExpander
  | args, blocks => do
    let {issue} ← PlannedConfig.parse.run args
    PointOfInterest.save (← getRef) s!"Planned content ({issue})" (kind := .event)
    let fileMap ← getFileMap
    let fileName ← getFileName
    let loc : Option (Nat × String) :=
      ((·.line, System.FilePath.normalize fileName |>.toString) ∘ fileMap.utf8PosToLspPos) <$> (← getRef).getPos?
    let content ← blocks.mapM elabBlock
    pure #[← `(Doc.Block.other {Block.planned with data := ToJson.toJson (α := Option Nat × Option (Nat × String)) ($(quote issue), $(quote loc))} #[$content,*])]

@[block_extension planned]
def planned.descr : BlockDescr where
  traverse _ data _ := do
    match FromJson.fromJson? (α := Option Nat × Option (Nat × String)) data with
    | .ok (none, loc?) | .ok (some 0, loc?) =>
       -- TODO add source locations to Verso ASTs upstream, then report here
      if let some (line, file) := loc? then
        logError s!"Missing issue number for planned content indicator at {file} line {line}"
      else
        logError s!"Missing issue number for planned content indicator"
    | .ok (some n, loc?) =>
      if !(← isDraft) then
        let loc := loc?.map (fun (l, f) => s!" at {f} line {l}") |>.getD ""
        logError s!"Planned content {n} in final rendering{loc}"
      else
        pure ()

    | .error e =>
      logError s!"Failed to deserialize issue number from {data} during traversal: {e}"
    pure none
  toTeX := none
  extraCss := [r#"
div.planned {
  font-style: italic;
}
div.planned .label {
  font-size: large;
  text-align: center;
  font-family: var(--verso-structure-font-family);
}
"#]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data content => do
      let issue : Option Nat ←
        match FromJson.fromJson? (α := Option Nat × Option (Nat × String)) data with
        | .ok v => pure v.1
        | .error e =>
          HtmlT.logError s!"Failed to deserialize issue number from {data}: {e}"
          pure none
      pure {{
        <div class="planned">
          <div class="label">"Planned Content"</div>
          {{← content.mapM goB}}
          {{if let some issue := issue then {{
            <p>
              "Tracked at issue "
                <a href=s!"https://github.com/leanprover/reference-manual/issues/{issue}">
                  s!"#{issue}"
                </a>
            </p>
            }} else .empty
          }}
        </div>
      }}

@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do pure #[← ``(Verso.Doc.Inline.code $(quote Lean.versionString))]
  | _, _ => throwError "Unexpected arguments"

inductive FFIDocType where
  | function
  | type
deriving DecidableEq, Repr, ToJson, FromJson

open Syntax in
open FFIDocType in
instance : Quote FFIDocType where
  quote
    | .function => mkCApp ``function #[]
    | .type => mkCApp ``type #[]

def FFIDocType.describe : FFIDocType → String
  | .function => "function"
  | .type => "type"

structure FFIConfig where
  name : String
  kind : FFIDocType := .function

def FFIConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m FFIConfig :=
  FFIConfig.mk <$> .positional `name .string <*> ((·.getD .function) <$> .named `kind kind true)
where
  kind : ValDesc m FFIDocType := {
    description := m!"{true} or {false}"
    get := fun
      | .name b => open FFIDocType in do
        let b' ← liftM <| realizeGlobalConstNoOverloadWithInfo b

        if b' == ``function then pure .function
        else if b' == ``type then pure .type
        else throwErrorAt b "Expected 'true' or 'false'"
      | other => throwError "Expected Boolean, got {repr other}"
  }

/--
Indicates that an element is a C type.

Currently does nothing other than indicate this fact for future use.
-/
@[role_expander ctype]
def ctype : RoleExpander
  | args, contents => do
    ArgParse.done.run args
    let #[x] := contents
      | throwError "Expected exactly one parameter"
    let `(inline|code($t)) := x
      | throwError "Expected exactly one code item"
    pure #[← ``(Inline.code $(quote t.getString))]

def Inline.ckw : Inline where
  name := `Manual.ckw

/--
Indicates that an element is a C keyword.
-/
@[role_expander ckw]
def ckw : RoleExpander
  | args, contents => do
    ArgParse.done.run args
    let #[x] := contents
      | throwError "Expected exactly one parameter"
    let `(inline|code($t)) := x
      | throwError "Expected exactly one code item"
    pure #[← ``(Inline.code $(quote t.getString))]

@[inline_extension ckw]
def ckw.descr : InlineDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some fun goI _ _ content => open Verso.Output.Html in do
    return {{<span class="c-keyword">{{← content.mapM goI}}</span>}}
  extraCss :=
    [".c-keyword code { font-weight: 600; }"]

def Block.ffi : Block where
  name := `Manual.ffi

@[directive_expander ffi]
def ffi : DirectiveExpander
  | args, blocks => do
    let config : FFIConfig ← FFIConfig.parse.run args
    if h : blocks.size = 0 then
      throwError "Expected at least one block"
    else
      let firstBlock := blocks[0]
      let moreBlocks := blocks.extract 1 blocks.size
      let `(block|``` | $contents ```) := firstBlock
        | throwErrorAt firstBlock "Expected code block"
      let body ← moreBlocks.mapM elabBlock
      pure #[← `(Block.other {Block.ffi with data := ToJson.toJson ($(quote config.name), $(quote config.kind), $(quote contents.getString))} #[$body,*])]

@[block_extension ffi]
def ffi.descr : BlockDescr where
  traverse id info _ := do
    let .ok (name, _declType, _signature) := FromJson.fromJson? (α := String × FFIDocType × String) info
      | do logError "Failed to deserialize FFI doc data"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name
    Index.addEntry id {term := Doc.Inline.code name}
    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (_name, ffiType, signature) := FromJson.fromJson? (α := String × FFIDocType × String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize FFI doc data"; pure .empty
      let sig : Html := {{<pre>{{signature}}</pre>}}

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">"FFI " {{ffiType.describe}}</span>
          <pre class="signature">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _ _ contents =>
    contents.mapM goB -- TODO



structure LeanSectionConfig where
  «variables» : Option String

section

variable [Monad m] [MonadError m] [MonadLiftT CoreM m]

instance : FromArgs LeanSectionConfig m where
  fromArgs :=
    LeanSectionConfig.mk <$> .named `variables .string true
end

section
open Lean Elab Command

-- Take from BuiltinCommands.lean

private def addScope (isNewNamespace : Bool) (header : String) (newNamespace : Name)
    (isNoncomputable : Bool := false) (attrs : List (TSyntax ``Parser.Term.attrInstance) := []) :
    CommandElabM Unit := do
  modify fun s => { s with
    env    := s.env.registerNamespace newNamespace,
    scopes := { s.scopes.head! with
      header := header, currNamespace := newNamespace
      isNoncomputable := s.scopes.head!.isNoncomputable || isNoncomputable
      attrs := s.scopes.head!.attrs ++ attrs
    } :: s.scopes
  }
  pushScope
  if isNewNamespace then
    activateScoped newNamespace





end
