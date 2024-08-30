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


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual


initialize leanOutputs : EnvExtension (NameMap (List (MessageSeverity × String))) ←
  registerEnvExtension (pure {})

def Block.lean : Block where
  name := `Manual.lean

def Inline.lean : Inline where
  name := `Manual.lean

structure LeanBlockConfig where
  «show» : Option Bool := none
  keep : Option Bool := none
  name : Option Name := none
  error : Option Bool := none

def LeanBlockConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanBlockConfig :=
  LeanBlockConfig.mk <$> .named `show .bool true <*> .named `keep .bool true <*> .named `name .name true <*> .named `error .bool true

open Manual.Meta.Lean.Scopes (getScopes setScopes)

@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, str => do
    let config ← LeanBlockConfig.parse.run args
    let origScopes ← getScopes

    let altStr ← parserInputString str

    let ictx := Parser.mkInputContext altStr (← getFileName)
    let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString altStr, tacticCache? := none, snap? := none, cancelTk? := none}

    let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := origScopes}
    let mut pstate := {pos := 0, recovering := false}
    let mut cmds := #[]

    repeat
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
      cmds := cmds.push cmd
      pstate := ps'
      cmdState := {cmdState with messages := messages}


      cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.lean, stx := cmd})) do
        match (← liftM <| EIO.toIO' <| (Command.elabCommand cmd cctx).run cmdState) with
        | Except.error e => logError e.toMessageData; return cmdState
        | Except.ok ((), s) => return s

      if Parser.isTerminalCommand cmd then break

    let origEnv ← getEnv
    try
      setEnv cmdState.env
      setScopes cmdState.scopes

      for t in cmdState.infoState.trees do
        pushInfoTree t


      let mut hls := Highlighted.empty
      for cmd in cmds do
        hls := hls ++ (← highlight cmd cmdState.messages.toArray cmdState.infoState.trees)

      if config.show.getD true then
        pure #[← `(Block.other {Block.lean with data := ToJson.toJson $(quote hls)} #[Block.code $(quote str.getString)])]
      else
        pure #[]
    finally
      if !config.keep.getD true then
        setEnv origEnv

      if let some name := config.name then
        let msgs ← cmdState.messages.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

      match config.error with
      | none =>
        for msg in cmdState.messages.toArray do
          logMessage msg
      | some true =>
        if cmdState.messages.hasErrors then
          for msg in cmdState.messages.errorsToWarnings.toArray do
            logMessage msg
        else
          throwErrorAt str "Error expected in code block, but none occurred"
      | some false =>
        for msg in cmdState.messages.toArray do
          logMessage msg
        if cmdState.messages.hasErrors then
          throwErrorAt str "No error expected in code block, one occurred"
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str

@[role_expander lean]
def leanInline : RoleExpander
  | args, inlines => do
    let config ← LeanBlockConfig.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $term:str }) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let altStr ← parserInputString term

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt term e
    | .ok stx =>
      let (newMsgs, tree) ← withInfoTreeContext (mkInfoTree := mkInfoTree `leanInline (← getRef)) do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          discard <| Manual.Meta.Lean.Scopes.runWithVariables fun _ => Elab.Term.elabTerm stx none
          Core.getMessageLog
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then
        let msgs ← newMsgs.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

      match config.error with
      | none =>
        for msg in newMsgs.toArray do
          logMessage msg
      | some true =>
        if newMsgs.hasErrors then
          for msg in newMsgs.errorsToWarnings.toArray do
            logMessage msg
        else
          throwErrorAt term "Error expected in code, but none occurred"
      | some false =>
        for msg in newMsgs.toArray do
          logMessage msg
        if newMsgs.hasErrors then
          throwErrorAt term "No error expected in code, one occurred"

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))

      if config.show.getD true then
        pure #[← `(Inline.other {Inline.lean with data := ToJson.toJson $(quote hls)} #[Inline.code $(quote term.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str
  mkInfoTree (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree) : DocElabM InfoTree := do
    let tree := InfoTree.node (Info.ofCommandInfo { elaborator, stx }) trees
    let ctx := PartialContextInfo.commandCtx {
      env := ← getEnv, fileMap := ← getFileMap, mctx := {}, currNamespace := ← getCurrNamespace,
      openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
    }
    return InfoTree.context ctx tree

  modifyInfoTrees {m} [Monad m] [MonadInfoTree m] (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
    modifyInfoState fun s => { s with trees := f s.trees }

  -- TODO - consider how to upstream this
  withInfoTreeContext {m α} [Monad m] [MonadInfoTree m] [MonadFinally m] (x : m α) (mkInfoTree : PersistentArray InfoTree → m InfoTree) : m (α × InfoTree) := do
    let treesSaved ← getResetInfoTrees
    MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let tree  ← mkInfoTree st.trees
      modifyInfoTrees fun _ => treesSaved.push tree
      pure tree



@[block_extension lean]
def lean.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.blockHtml "examples"


@[inline_extension lean]
def lean.inlinedescr : InlineDescr where
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
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering inline HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"


def Block.signature : Block where
  name := `Manual.signature

declare_syntax_cat signature_spec
syntax ("def" <|> "theorem")? declId declSig : signature_spec

@[code_block_expander signature]
def signature : CodeBlockExpander
  | args, str => do
    ArgParse.done.run args
    let altStr ← parserInputString str

    match Parser.runParserCategory (← getEnv) `signature_spec altStr (← getFileName) with
    | .error e => throwError e
    | .ok stx =>
      let `(signature_spec|$[$kw]? $name:declId $sig:declSig) := stx
        | throwError m!"Didn't understand parsed signature: {indentD stx}"
      let cmdCtx : Command.Context := {
        fileName := ← getFileName,
        fileMap := ← getFileMap,
        tacticCache? := none,
        snap? := none,
        cancelTk? := none
      }
      let cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, infoState := ← getInfoState}
      let ((hls, _, _, _), st') ← ((SubVerso.Examples.checkSignature name sig).run cmdCtx).run cmdState
      setInfoState st'.infoState

      pure #[← `(Block.other {Block.signature with data := ToJson.toJson $(quote (Highlighted.seq hls))} #[Block.code $(quote str.getString)])]

@[block_extension signature]
def signature.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML signature: " ++ err ++ "\n" ++ toString data
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.blockHtml "examples"

open Syntax (mkCApp) in
open MessageSeverity in
instance : Quote MessageSeverity where
  quote
    | .error => mkCApp ``error #[]
    | .information => mkCApp ``information #[]
    | .warning => mkCApp ``warning #[]

open Syntax (mkCApp) in
open Position in
instance : Quote Position where
  quote
    | ⟨line, column⟩ => mkCApp ``Position.mk #[quote line, quote column]

def Block.syntaxError : Block where
  name := `Manual.syntaxError

structure SyntaxErrorConfig where
  name : Name
  «show» : Bool := true
  category : Name := `command
  prec : Nat := 0

defmethod ValDesc.nat [Monad m] [MonadError m] : ValDesc m Nat where
  description := m!"a name"
  get
    | .num x => pure x.getNat
    | other => throwError "Expected number, got {repr other}"

def SyntaxErrorConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SyntaxErrorConfig :=
  SyntaxErrorConfig.mk <$>
    .positional `name .name <*>
    ((·.getD true) <$> .named `show .bool true) <*>
    ((·.getD `command) <$> .named `category .name true) <*>
    ((·.getD 0) <$> .named `precedence .nat true)

open Lean.Parser in
@[code_block_expander syntaxError]
def syntaxError : CodeBlockExpander
  | args, str => do
    let config ← SyntaxErrorConfig.parse.run args
    let s := str.getString
    match runParserCategory (← getEnv) (← getOptions) config.category s with
    | .ok stx =>
      throwErrorAt str m!"Expected a syntax error for category {config.category}, but got {indentD stx}"
    | .error es =>
      let msgs := es.map fun (pos, msg) =>
        (.error, mkErrorStringWithPos  "<example>" pos msg)
      modifyEnv (leanOutputs.modifyState · (·.insert config.name msgs))
      return #[← `(Block.other {Block.syntaxError with data := ToJson.toJson ($(quote s), $(quote es))} #[Block.code $(quote s)])]

@[block_extension syntaxError]
def syntaxError.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [
    r"
.syntax-error {
  white-space: normal;
}
.syntax-error::before {
  counter-reset: linenumber;
}
.syntax-error > .line {
  display: block;
  white-space: pre;
  counter-increment: linenumber;
  font-family: var(--verso-code-font-family);
}
.syntax-error > .line::before {
  -webkit-user-select: none;
  display: inline-block;
  content: counter(linenumber);
  border-right: 1px solid #ddd;
  width: 2em;
  padding-right: 0.25em;
  margin-right: 0.25em;
  font-family: var(--verso-code-font-family);
  text-align: right;
}

:is(.syntax-error > .line):has(.parse-message)::before {
  color: red;
  font-weight: bold;
}

.syntax-error .parse-message > code {
  display:none;
}
.syntax-error .parse-message {
  position: relative;
}
.syntax-error .parse-message::before {
  content: '🛑';
  text-decoration: none;
  position: absolute;
  top: 0; left: 0;
  color: red;
}
"
  ]
  extraJs := [
    highlightingJs
  ]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (str, (msgs : (List (Position × String)))) =>
        let mut pos : String.Pos := ⟨0⟩
        let mut out : Array Html := #[]
        let mut line : Array Html := #[]
        let filemap := FileMap.ofString str
        let mut msgs := msgs
        for lineNum in [1:filemap.getLastLine] do
          pos := filemap.lineStart lineNum
          let lineEnd := str.prev (filemap.lineStart (lineNum + 1))
          repeat
            match msgs with
            | [] => break
            | (pos', msg) :: more =>
              let pos' := filemap.ofPosition pos'
              if pos' > lineEnd then break
              msgs := more
              line := line.push <| str.extract pos pos'
              line := line.push {{<span class="parse-message has-info error"><code class="hover-info">{{msg}}</code></span>"\n"}}
              pos := pos'
          line := line.push <| str.extract pos lineEnd
          out := out.push {{<code class="line">{{line}}</code>}}
          line := #[]
          pos := str.next lineEnd

        pure {{<pre class="syntax-error hl lean">{{out}}</pre>}}

def Block.leanOutput : Block where
  name := `Manual.leanOutput

structure LeanOutputConfig where
  name : Ident
  «show» : Bool := true
  severity : Option MessageSeverity
  summarize : Bool
  whitespace : WhitespaceMode

def LeanOutputConfig.parser [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanOutputConfig :=
  LeanOutputConfig.mk <$>
    .positional `name output <*>
    ((·.getD true) <$> .named `show .bool true) <*>
    .named `severity sev true <*>
    ((·.getD false) <$> .named `summarize .bool true) <*>
    ((·.getD .exact) <$> .named `whitespace ws true)
where
  output : ValDesc m Ident := {
    description := "output name",
    get := fun
      | .name x => pure x
      | other => throwError "Expected output name, got {repr other}"
  }
  opt {α} (p : ArgParse m α) : ArgParse m (Option α) := (some <$> p) <|> pure none
  optDef {α} (fallback : α) (p : ArgParse m α) : ArgParse m α := p <|> pure fallback
  sev : ValDesc m MessageSeverity := {
    description := open MessageSeverity in m!"The expected severity: '{``error}', '{``warning}', or '{``information}'",
    get := open MessageSeverity in fun
      | .name b => do
        let b' ← realizeGlobalConstNoOverloadWithInfo b
        if b' == ``MessageSeverity.error then pure MessageSeverity.error
        else if b' == ``MessageSeverity.warning then pure MessageSeverity.warning
        else if b' == ``MessageSeverity.information then pure MessageSeverity.information
        else throwErrorAt b "Expected '{``error}', '{``warning}', or '{``information}'"
      | other => throwError "Expected severity, got {repr other}"
  }
  ws : ValDesc m WhitespaceMode := {
    description := open WhitespaceMode in m!"The expected whitespace mode: '{``exact}', '{``normalized}', or '{``lax}'",
    get := open WhitespaceMode in fun
      | .name b => do
        let b' ← realizeGlobalConstNoOverloadWithInfo b
        if b' == ``WhitespaceMode.exact then pure WhitespaceMode.exact
        else if b' == ``WhitespaceMode.normalized then pure WhitespaceMode.normalized
        else if b' == ``WhitespaceMode.lax then pure WhitespaceMode.lax
        else throwErrorAt b "Expected '{``exact}', '{``normalized}', or '{``lax}'"
      | other => throwError "Expected whitespace mode, got {repr other}"
  }

defmethod Lean.NameMap.getOrSuggest [Monad m] [MonadInfoTree m] [MonadError m]
    (map : NameMap α) (key : Ident) : m α := do
  match map.find? key.getId with
  | some v => pure v
  | none =>
    for (n, _) in map do
      -- TODO once Levenshtein is merged upstream, use it here
      if FuzzyMatching.fuzzyMatch key.getId.toString n.toString || FuzzyMatching.fuzzyMatch n.toString key.getId.toString  then
        Suggestion.saveSuggestion key n.toString n.toString
    throwErrorAt key "'{key}' not found - options are {map.toList.map (·.fst)}"

@[code_block_expander leanOutput]
def leanOutput : CodeBlockExpander
 | args, str => do
    let config ← LeanOutputConfig.parser.run args
    let msgs : List (MessageSeverity × String) ← leanOutputs.getState (← getEnv) |>.getOrSuggest config.name

    for (sev, txt) in msgs do
      if mostlyEqual config.whitespace str.getString txt then
        if let some s := config.severity then
          if s != sev then
            throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr sev}"
        if config.show then
          let content ← `(Block.other {Block.leanOutput with data := ToJson.toJson ($(quote sev), $(quote txt), $(quote config.summarize))} #[Block.code $(quote str.getString)])
          return #[content]
        else return #[]

    for (_, m) in msgs do
      Verso.Doc.Suggestion.saveSuggestion str (m.take 30 ++ "…") m
    throwErrorAt str "Didn't match - expected one of: {indentD (toMessageData <| msgs.map (·.2))}\nbut got:{indentD (toMessageData str.getString)}"
where
  sevStr : MessageSeverity → String
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

  mostlyEqual (ws : WhitespaceMode) (s1 s2 : String) : Bool :=
    ws.apply s1.trim == ws.apply s2.trim

@[block_extension leanOutput]
def leanOutput.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, summarize) : MessageSeverity × String × Bool) =>
        let wrap html :=
          if summarize then {{<details><summary>"Expand..."</summary>{{html}}</details>}}
          else html
        pure <| wrap {{<div class={{getClass sev}}><pre>{{txt}}</pre></div>}}
where
  getClass
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

def Inline.name : Inline where
  name := `Manual.name

structure NameConfig where
  full : Option Name

def NameConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m NameConfig :=
  NameConfig.mk <$> ((fun _ => none) <$> .done <|> .positional `name ref <|> pure none)
where
  ref : ValDesc m (Option Name) := {
    description := m!"reference name"
    get := fun
      | .name x =>
        some <$> liftM (realizeGlobalConstNoOverloadWithInfo x)
      | other => throwError "Expected Boolean, got {repr other}"
  }


@[role_expander name]
partial def name : RoleExpander
  | args, #[arg] => do
    let cfg ← NameConfig.parse.run args
    let `(inline|code{ $name:str }) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg (cfg.full.getD exampleName) (canonical := true)
    let _resolvedName ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.name, stx := identStx})) <| realizeGlobalConstNoOverloadWithInfo identStx

    let hl : Highlighted ← constTok (cfg.full.getD exampleName) name.getString

    pure #[← `(Inline.other {Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote name.getString)])]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"
where
  constTok name str := do
    let docs ← findDocString? (← getEnv) name
    let sig := toString (← (PrettyPrinter.ppSignature name)).1
    pure <| .token ⟨.const name sig docs, str⟩

@[inline_extension name]
def name.descr : InlineDescr where
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
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"
