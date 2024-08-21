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
import Manual.Meta.Example
import Manual.Meta.Figure
import Manual.Meta.Lean
import Manual.Meta.Syntax

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
    let content ← blocks.mapM elabBlock
    pure #[← `(Doc.Block.other Block.TODO #[$content,*])]

@[role_expander TODO]
def TODOinline : RoleExpander
  | args, inlines => do
    ArgParse.done.run args
    let content ← inlines.mapM elabInline
    pure #[← `(Doc.Inline.other Inline.TODO #[$content,*])]


@[block_extension TODO]
def TODO.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
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
    pure none
  toTeX := none
  extraCss := [r#"
span.TODO {
  border: 3px solid red;
  display: inline;
  position: relative;
  float: right;
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


@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do pure #[← ``(Verso.Doc.Inline.text $(quote Lean.versionString))]
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
      let `<low|(Verso.Syntax.codeblock (column ~_col) ~_open ~_args ~(.atom _info contents) ~_close )> := firstBlock
        | throwErrorAt firstBlock "Expected code block"
      let body ← moreBlocks.mapM elabBlock
      pure #[← `(Block.other {Block.ffi with data := ToJson.toJson ($(quote config.name), $(quote config.kind), $(quote contents))} #[$body,*])]

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

      let (_, _, xref) ← read
      let idAttr :=
        if let some (_, htmlId) := xref.externalTags[id]? then
          #[("id", htmlId)]
        else #[]


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
