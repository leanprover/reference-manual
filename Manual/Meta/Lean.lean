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

import Manual.Meta.Basic
import Manual.Meta.ExpectString
import Manual.Meta.Lean.Scopes
import Manual.Meta.Lean.Block


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

/--
The largest number of characters expected on a line
-/
-- TODO make this into an option instead
def Meta.maxCodeColumns : Nat := 60

def Meta.warnLongLines [Monad m] [MonadFileMap m] [MonadLog m] [AddMessageContext m] [MonadOptions m] (indent? : Option Nat) (str : StrLit) : m (Array (Nat × StrLit × MessageData)) := do
  let fileMap ← getFileMap
  let maxCol := maxCodeColumns + indent?.getD 0
  let mut warnings := #[]
  if let some startPos := str.raw.getPos? then
    if let some stopPos := str.raw.getTailPos? then
      let ⟨startLine, _⟩ := fileMap.utf8PosToLspPos startPos
      let ⟨stopLine, _⟩ := fileMap.utf8PosToLspPos stopPos
      for l in [startLine:stopLine] do
        let nextStart := fileMap.lineStart (l + 1)
        let ⟨_, endCol⟩ := fileMap.utf8PosToLspPos (nextStart - ⟨1⟩)
        if endCol > maxCol then
          let thisStart := fileMap.lineStart l
          let fakeLiteral := Syntax.mkStrLit (fileMap.source.extract thisStart nextStart) (.synthetic thisStart nextStart)
          let msg := m!"Line {l} is too long ({endCol} columns exceeds {maxCol})"
          warnings := warnings.push (l, fakeLiteral, msg)
  pure warnings


initialize leanOutputs : EnvExtension (NameMap (List (MessageSeverity × String))) ←
  registerEnvExtension (pure {})

def Inline.lean (hls : Highlighted) : Inline where
  name := `Manual.lean
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]

structure LeanBlockConfig where
  «show» : Option Bool := none
  keep : Option Bool := none
  name : Option Name := none
  error : Option Bool := none
  fresh : Bool := false

def LeanBlockConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanBlockConfig :=
  LeanBlockConfig.mk <$> .named `show .bool true <*> .named `keep .bool true <*> .named `name .name true <*> .named `error .bool true <*> .namedD `fresh .bool false

structure LeanInlineConfig extends LeanBlockConfig where
  /-- The expected type of the term -/
  type : Option StrLit
  /-- Universe variables allowed in the term -/
  universes : Option StrLit



def LeanInlineConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanInlineConfig :=
  LeanInlineConfig.mk <$> LeanBlockConfig.parse <*> .named `type strLit true <*> .named `universes strLit true
where
  strLit : ValDesc m StrLit := {
    description := "string literal containing an expected type",
    get
      | .str s => pure s
      | other => throwError "Expected string, got {repr other}"
  }


open Manual.Meta.Lean.Scopes (getScopes setScopes runWithOpenDecls runWithVariables)

private def abbrevFirstLine (width : Nat) (str : String) : String :=
  let str := str.trimLeft
  let short := str.take width |>.replace "\n" "⏎"
  if short == str then short else short ++ "…"

def LeanBlockConfig.outlineMeta : LeanBlockConfig → String
  | {«show», error, ..} =>
    match «show», error with
    | some true, true | none, true => " (error)"
    | some false, true => " (hidden, error)"
    | some false, false => " (hidden)"
    | _, _ => " "

@[code_block_expander lean]
def lean : CodeBlockExpander
  | args, str => withoutAsync <| do
    let config ← LeanBlockConfig.parse.run args

    PointOfInterest.save (← getRef) ((config.name.map toString).getD (abbrevFirstLine 20 str.getString))
      (kind := Lsp.SymbolKind.file)
      (detail? := some ("Lean code" ++ config.outlineMeta))

    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)

    let origScopes ← if config.fresh then pure [{header := ""}] else getScopes

    -- Turn of async elaboration so that info trees and messages are available when highlighting syntax
    let origScopes := origScopes.modifyHead fun sc => {sc with opts := Elab.async.set sc.opts false}

    let altStr ← parserInputString str

    let ictx := Parser.mkInputContext altStr (← getFileName)
    let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString altStr, snap? := none, cancelTk? := none}

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

      if let some col := col? then
        hls := hls.deIndent col

      if config.show.getD true then
        pure #[← ``(Block.other (Block.lean $(quote hls)) #[Block.code $(quote str.getString)])]
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

      if config.show.getD true then
        for (_line, lit, msg) in (← Meta.warnLongLines col? str) do
          logWarningAt lit msg
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str

@[code_block_expander leanTerm]
def leanTerm : CodeBlockExpander
  | args, str => withoutAsync <| do
    let config ← LeanInlineConfig.parse.run args

    let altStr ← parserInputString str

    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)

    let leveller :=
      if let some us := config.universes then
        let us :=
          us.getString.splitOn " " |>.filterMap fun (s : String) =>
            if s.isEmpty then none else some s.toName
        Elab.Term.withLevelNames us
      else id

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt str e
    | .ok stx =>
      let (newMsgs, tree) ← do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog

          let tree' ← runWithOpenDecls <| runWithVariables fun _vars => do
            let expectedType ← config.type.mapM fun (s : StrLit) => do
              match Parser.runParserCategory (← getEnv) `term s.getString (← getFileName) with
              | .error e => throwErrorAt stx e
              | .ok stx => withEnableInfoTree false do
                let t ← leveller <| Elab.Term.elabType stx
                Term.synthesizeSyntheticMVarsNoPostponing
                let t ← instantiateMVars t
                if t.hasExprMVar || t.hasLevelMVar then
                  throwErrorAt s "Type contains metavariables: {t}"
                pure t

            let e ← Elab.Term.elabTerm (catchExPostpone := true) stx expectedType
            Term.synthesizeSyntheticMVarsNoPostponing
            let _ ← Term.levelMVarToParam (← instantiateMVars e)

            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure <| InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Manual.leanInline, str⟩) (← getInfoState).trees)
          pure (← Core.getMessageLog, tree')
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then
        let msgs ← newMsgs.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

      pushInfoTree tree

      match config.error with
      | none =>
        for msg in newMsgs.toArray do
          logMessage msg
      | some true =>
        if newMsgs.hasErrors then
          for msg in newMsgs.errorsToWarnings.toArray do
            logMessage msg
        else
          throwErrorAt str "Error expected in code, but none occurred"
      | some false =>
        for msg in newMsgs.toArray do
          logMessage msg
        if newMsgs.hasErrors then
          throwErrorAt str "No error expected in code, one occurred"

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))
      let hls :=
        if let some col := col? then
          hls.deIndent col
        else hls

      if config.show.getD true then
        pure #[← ``(Block.other (Block.lean $(quote hls)) #[Block.code $(quote str.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


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


@[role_expander lean]
def leanInline : RoleExpander
  -- Async elab is turned off to make sure that info trees and messages are available when highlighting
  | args, inlines => withoutAsync do
    let config ← LeanInlineConfig.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $term:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let altStr ← parserInputString term

    let leveller :=
      if let some us := config.universes then
        let us :=
          us.getString.splitOn " " |>.filterMap fun (s : String) =>
            if s.isEmpty then none else some s.toName
        Elab.Term.withLevelNames us
      else id

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt term e
    | .ok stx =>

      let (newMsgs, type, tree) ← do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          let (tree', t) ← runWithOpenDecls <| runWithVariables fun _ => do

            let expectedType ← config.type.mapM fun (s : StrLit) => do
              match Parser.runParserCategory (← getEnv) `term s.getString (← getFileName) with
              | .error e => throwErrorAt term e
              | .ok stx => withEnableInfoTree false do
                let t ← leveller <| Elab.Term.elabType stx
                Term.synthesizeSyntheticMVarsNoPostponing
                let t ← instantiateMVars t
                if t.hasExprMVar || t.hasLevelMVar then
                  throwErrorAt s "Type contains metavariables: {t}"
                pure t

            let e ← leveller <| Elab.Term.elabTerm (catchExPostpone := true) stx expectedType
            Term.synthesizeSyntheticMVarsNoPostponing
            let e ← Term.levelMVarToParam (← instantiateMVars e)
            let t ← Meta.inferType e >>= instantiateMVars >>= (Meta.ppExpr ·)
            let t := Std.Format.group <| (← Meta.ppExpr e) ++ (" :" ++ .line) ++ t

            Term.synthesizeSyntheticMVarsNoPostponing
            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure <| (InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Manual.leanInline, arg⟩) (← getInfoState).trees), t)
          pure (← Core.getMessageLog, t, tree')
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then
        let msgs ← newMsgs.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

      pushInfoTree tree

      if let `(inline|role{%$s $f $_*}%$e[$_*]) ← getRef then
        Hover.addCustomHover (mkNullNode #[s, e]) type
        Hover.addCustomHover f type

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
        pure #[← `(Inline.other (Inline.lean $(quote hls)) #[Inline.code $(quote term.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


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



@[role_expander inst]
def inst : RoleExpander
  | args, inlines => withoutAsync <| do
    let config ← LeanBlockConfig.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $term:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let altStr ← parserInputString term

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt term e
    | .ok stx =>
      let (newMsgs, tree) ← do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          let tree' ← runWithOpenDecls <| runWithVariables fun _ => do
            let e ← Elab.Term.elabTerm (catchExPostpone := true) stx none
            Term.synthesizeSyntheticMVarsNoPostponing
            let _ ← Term.levelMVarToParam (← instantiateMVars e)
            Term.synthesizeSyntheticMVarsNoPostponing
            -- TODO this is the only difference from the normal inline Lean. Abstract the commonalities out!
            discard <| Meta.synthInstance e
            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure <| InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Manual.leanInline, arg⟩) (← getInfoState).trees)
          pure (← Core.getMessageLog, tree')
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then
        let msgs ← newMsgs.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

      pushInfoTree tree

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
        pure #[← `(Inline.other (Inline.lean $(quote hls)) #[Inline.code $(quote term.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


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


@[inline_extension lean]
def lean.inlinedescr : InlineDescr where
  traverse id data _ := do
    let .arr #[_, defined] := data
      | logError "Expected two-element JSON for Lean code" *> pure none
    match FromJson.fromJson? defined with
    | .error err =>
      logError <| "Couldn't deserialize Lean code while traversing inline example: " ++ err
      pure none
    | .ok (defs : Array Name) =>
      let path ← (·.path) <$> read
      for n in defs do
        let _ ← externalTag id path n.toString
        modify (·.saveDomainObject exampleDomain n.toString id)
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
      let .arr #[hlJson, _] := data
        | HtmlT.logError "Expected two-element JSON for Lean code" *> pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering inline HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"

def Inline.option : Inline where
  name := `Manual.option

@[role_expander option]
def option : RoleExpander
  | args, inlines => withoutAsync do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $optName:str )) := arg
      | throwErrorAt arg "Expected code literal with the option name"
    let optName := optName.getString.toName
    let optDecl ← getOptionDecl optName
    let hl : Highlighted := optTok optName optDecl.declName optDecl.descr

    pure #[← `(Inline.other {Inline.option with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote optName.toString)])]
where
  optTok (name declName : Name) (descr : String) : Highlighted :=
    .token ⟨.option name declName descr , name.toString⟩

@[inline_extension option]
def option.descr : InlineDescr where
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
        HtmlT.logError <| "Couldn't deserialize Lean option code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"

@[directive_expander leanSection]
def leanSection : DirectiveExpander
  | args, contents => do
    let name? ← ArgParse.run ((some <$> .positional `name .string) <|> pure none) args
    let arg ← `(argument| «show» := false)
    let code := name?.map (s!"section {·}") |>.getD "section"
    let start ← `(block|```lean $arg | $(quote code) ```)
    let code := name?.map (s!"end {·}") |>.getD "end"
    let «end» ← `(block|```lean $arg | $(quote code) ```)
    return #[← elabBlock start] ++ (← contents.mapM elabBlock) ++ #[← elabBlock «end»]


def Block.signature : Block where
  name := `Manual.signature

declare_syntax_cat signature_spec
syntax ("def" <|> "theorem")? declId declSig : signature_spec

structure SignatureConfig where
  «show» : Bool := true

def SignatureConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m SignatureConfig :=
  SignatureConfig.mk <$>
    ((·.getD true) <$> .named `show .bool true)


@[code_block_expander signature]
def signature : CodeBlockExpander
  | args, str => withoutAsync do
    let {«show»} ← SignatureConfig.parse.run args
    let altStr ← parserInputString str
    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)


    match Parser.runParserCategory (← getEnv) `signature_spec altStr (← getFileName) with
    | .error e => throwError e
    | .ok stx =>
      let `(signature_spec|$[$kw]? $name:declId $sig:declSig) := stx
        | throwError m!"Didn't understand parsed signature: {indentD stx}"

      PointOfInterest.save (← getRef) (toString name.raw)
        (kind := Lsp.SymbolKind.file)
        (detail? := some "Signature")

      let cmdCtx : Command.Context := {
        fileName := ← getFileName,
        fileMap := ← getFileMap,
        snap? := none,
        cancelTk? := none
      }
      let cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, infoState := ← getInfoState}
      let hls ←
        try
          let ((hls, _, _, _), st') ← ((SubVerso.Examples.checkSignature name sig).run cmdCtx).run cmdState
          setInfoState st'.infoState
          pure (Highlighted.seq hls)
        catch e =>
          let fmt ← PrettyPrinter.ppSignature (TSyntax.mk name.raw[0]).getId
          Suggestion.saveSuggestion str (fmt.fmt.pretty 60) (fmt.fmt.pretty 30 ++ "\n")
          throw e

      let hls :=
        if let some col := col? then
          hls.deIndent col
        else hls

      if «show» then
        pure #[← `(Block.other {Block.signature with data := ToJson.toJson $(quote hls)} #[Block.code $(quote str.getString)])]
      else
        pure #[]

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

def SyntaxErrorConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SyntaxErrorConfig :=
  SyntaxErrorConfig.mk <$>
    .positional `name (ValDesc.name.as m!"name for later reference") <*>
    .namedD `show .bool true <*>
    .namedD `category (ValDesc.name.as m!"syntax category (default 'command')") `command <*>
    .namedD `precedence .nat 0

open Lean.Parser in
@[code_block_expander syntaxError]
def syntaxError : CodeBlockExpander
  | args, str => withoutAsync do
    let config ← SyntaxErrorConfig.parse.run args

    PointOfInterest.save (← getRef) config.name.toString
      (kind := Lsp.SymbolKind.file)
      (detail? := some "Syntax error")

    let s := str.getString
    match runParserCategory' (← getEnv) (← getOptions) config.category s with
    | .ok stx =>
      throwErrorAt str m!"Expected a syntax error for category {config.category}, but got {indentD stx}"
    | .error es =>
      let msgs := es.toList.map fun {pos, endPos, text := msg} =>
        (.error, mkErrorStringWithPos  "<example>" pos msg (endPos := endPos))
      modifyEnv (leanOutputs.modifyState · (·.insert config.name msgs))
      Hover.addCustomHover (← getRef) <| MessageData.joinSep (msgs.map fun (sev, msg) => m!"{sevStr sev}:{indentD msg}") Format.line

      return #[← `(Block.other {Block.syntaxError with data := ToJson.toJson ($(quote s), $(quote es))} #[Block.code $(quote s)])]
where
  sevStr : MessageSeverity → String
    | .information => "info"
    | .warning => "warning"
    | .error => "error"

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

.syntax-error .parse-message > code.hover-info {
  display:none;
}

.syntax-error .parse-message {
  white-space: pre;
  text-decoration-skip-ink: none;
  color: red;
  font-weight: 600;
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
      | .ok (str, (msgs : (Array SyntaxError))) =>
        let mut pos : String.Pos := ⟨0⟩
        let mut out : Array Html := #[]
        let mut line : Array Html := #[]
        let filemap := FileMap.ofString str
        let mut msgs := msgs.toSubarray
        for lineNum in [1:filemap.getLastLine] do
          pos := filemap.lineStart lineNum
          let lineEnd := str.prev (filemap.lineStart (lineNum + 1))
          repeat
            if h : msgs.size = 0 then break
            else
              let {pos := errPos, endPos, text := errText} := msgs[0]
              let pos' := filemap.ofPosition errPos
              if pos' > lineEnd then break
              let pos'' := filemap.ofPosition endPos

              msgs := msgs.drop 1
              line := line.push <| str.extract pos pos'
              let spanned := str.extract pos' pos''  -- TODO account for cases where the error range spans multiple lines
              -- If the error is just a newline, add a space so there's something to highlight
              let spanned := if spanned.isEmpty || spanned.all (· == '\n') then " " ++ spanned else spanned
              line := line.push {{<span class="parse-message has-info error"><code class="hover-info">{{errText}}</code>{{spanned}}</span>}}
              pos := pos''
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
  normalizeMetas : Bool

def LeanOutputConfig.parser [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m LeanOutputConfig :=
  LeanOutputConfig.mk <$>
    .positional `name output <*>
    ((·.getD true) <$> .named `show .bool true) <*>
    .named `severity sev true <*>
    ((·.getD false) <$> .named `summarize .bool true) <*>
    ((·.getD .exact) <$> .named `whitespace ws true) <*>
    .namedD `normalizeMetas .bool true
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
      if FuzzyMatching.fuzzyMatch key.getId.toString n.toString || FuzzyMatching.fuzzyMatch n.toString key.getId.toString then
        Suggestion.saveSuggestion key n.toString n.toString
    throwErrorAt key "'{key}' not found - options are {map.toList.map (·.fst)}"

@[code_block_expander leanOutput]
def leanOutput : CodeBlockExpander
 | args, str => do
    let config ← LeanOutputConfig.parser.run args

    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)

    PointOfInterest.save (← getRef) (config.name.getId.toString)
      (kind := Lsp.SymbolKind.file)
      (selectionRange := config.name)
      (detail? := some ("Lean output" ++ (config.severity.map (s!" ({sevStr ·})") |>.getD "")))

    let msgs : List (MessageSeverity × String) ← leanOutputs.getState (← getEnv) |>.getOrSuggest config.name

    let expected :=
      if config.normalizeMetas then
        normalizeMetavars str.getString
      else str.getString

    for (sev, txt) in msgs do
      let actual :=
        if config.normalizeMetas then
          normalizeMetavars txt
        else txt
      if mostlyEqual config.whitespace expected actual then
        if let some s := config.severity then
          if s != sev then
            throwErrorAt str s!"Expected severity {sevStr s}, but got {sevStr sev}"
        if config.show then
          let content ← `(Block.other {Block.leanOutput with data := ToJson.toJson ($(quote sev), $(quote txt), $(quote config.summarize))} #[Block.code $(quote str.getString)])
          return #[content]
        else return #[]

    for (_, m) in msgs do
      let m := "".pushn ' ' (col?.getD 0) ++ if m.endsWith "\n" then m else m ++ "\n"
      Verso.Doc.Suggestion.saveSuggestion str (abbreviateString m) m
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

def NameConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT TermElabM m] : ArgParse m NameConfig :=
  NameConfig.mk <$> ((fun _ => none) <$> .done <|> .positional `name ref)
where
  ref : ValDesc m (Option Name) := {
    description := m!"reference name"
    get := fun
      | .name x =>
        try
          let resolved ← liftM (runWithOpenDecls (runWithVariables fun _ => realizeGlobalConstNoOverloadWithInfo x))
          return some resolved
        catch
          | .error ref e => throwErrorAt ref e
          | _ => return none
      | other => throwError "Expected reference name, got {repr other}"
  }

def constTok [Monad m] [MonadEnv m] [MonadLiftT MetaM m] [MonadLiftT IO m]
    (name : Name) (str : String) :
    m Highlighted := do
  let docs ← findDocString? (← getEnv) name
  let sig := toString (← (PrettyPrinter.ppSignature name)).1
  pure <| .token ⟨.const name sig docs false, str⟩

@[role_expander name]
def name : RoleExpander
  | args, #[arg] => do
    let cfg ← NameConfig.parse.run args
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg (cfg.full.getD exampleName) (canonical := true)

    try
      let resolvedName ←
        runWithOpenDecls <| runWithVariables fun _ =>
          withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.name, stx := identStx})) do
            realizeGlobalConstNoOverloadWithInfo identStx

      let hl : Highlighted ← constTok resolvedName name.getString

      pure #[← `(Inline.other {Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote name.getString)])]
    catch e =>
      logErrorAt identStx e.toMessageData
      pure #[← `(Inline.code $(quote name.getString))]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Unexpected arguments"


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

-- Placeholder for module names (eventually hyperlinking these will be important, so better to tag them now)

@[role_expander module]
def module : RoleExpander
  | args, #[arg] => do
    let cfg ← ArgParse.done.run args
    let `(inline|code( $name:str )) := arg
      | throwErrorAt arg "Expected code literal with the module's name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg exampleName (canonical := true)
    pure #[← ``(Doc.Inline.code $(quote name.getString))]
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Expected code literal with the module's name"
    else
      throwError "Expected code literal with the module's name"
