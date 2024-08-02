import Lean.Data.Json

import Verso.Genre.Manual

import Manual.Meta.FFI.ClangEnv

open Lean Elab

open Verso ArgParse Doc Elab Monad
open Verso.Genre.Manual

open Manual.Meta.FFI

namespace Manual

inductive FFIDocType where
  | function
  | type
deriving DecidableEq, Repr, ToJson, FromJson

instance : ToMessageData FFIDocType where
  toMessageData
    | .function => .ofConst <| .const ``FFIDocType.function []
    | .type => .ofConst <| .const ``FFIDocType.type []

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
  FFIConfig.mk <$> .positional `name .string <*> (.positional `kind kind <|> pure .function)
where
  kind : ValDesc m FFIDocType := {
    description := m!"{FFIDocType.function} or {FFIDocType.type}"
    get := fun
      | .name b => open FFIDocType in do
        let b' ← liftM <| realizeGlobalConstNoOverloadWithInfo b

        if b' == ``function then pure .function
        else if b' == ``type then pure .type
        else throwErrorAt b "Expected 'true' or 'false'"
      | other => throwError "Expected Boolean, got {repr other}"
  }

def FFI.findInfo (name : String) : FFIDocType → String
  | .type =>
    if let some td := leanClangEnv.typedefsByName[name]? then
      toString (repr td)
    else if let some r := leanClangEnv.recordsByName[name]? then
      toString (repr r)
    else s!"Couldn't find type {name}"
  | .function =>
    if let some f := leanClangEnv.functions[name]? then
      toString (repr f)
    else s!"Couldn't find function {name}"

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
      pure #[← `(Block.other {Block.ffi with data := ToJson.toJson ($(quote config.name), $(quote config.kind), $(quote contents))} #[Block.code $(quote <| FFI.findInfo config.name config.kind), $body,*])]

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
