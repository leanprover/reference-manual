/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import VersoManual

import Verso.Doc
import Verso.Syntax
import MD4Lean
import Manual.Meta
import Std.Internal.Parsec.String

import Manual.ErrorExplanation
import Manual.ErrorExplanationDummyData

open Verso.Genre.Manual.InlineLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option guard_msgs.diff true

open Std.Internal Lean Elab Term Verso Doc Elab Genre Manual Markdown

namespace Manual

inductive ErrorExplanationCodeInfo.Kind
  | broken | fixed
deriving Repr, Inhabited, BEq

instance : ToString ErrorExplanationCodeInfo.Kind where
  toString
  | .broken => "broken"
  | .fixed => "fixed"

structure ErrorExplanationCodeInfo where
  lang : String
  kind? : Option ErrorExplanationCodeInfo.Kind
  title? : Option String
deriving Repr

namespace ErrorExplanationCodeInfo
open Parsec Parsec.String

namespace Parse

def word : Parser String := fun it =>
  -- TODO: allow escaping
  let it' := it.find fun c => c == '"'
  .success it' (it.extract it')

def languageName : Parser String := fun it =>
  let it' := it.find fun c => !c.isAlphanum
  .success it' (it.extract it')

def snippetKind : Parser Kind := do
  (pstring "broken" *> pure .broken)
  <|> (pstring "fixed" *> pure .fixed)

def title : Parser String :=
  skipChar '(' *> optional ws *> skipString "title" *> ws *> skipString ":=" *> ws *> skipChar '"' *>
  word
  <* skipChar '"' <* optional ws <* skipChar ')'

def attr : Parser (Kind ⊕ String) :=
  .inl <$> snippetKind <|> .inr <$> title

def infoString : Parser ErrorExplanationCodeInfo := do
  let lang ← languageName
  let attrs ← Parsec.many (ws *> attr)
  let mut kind? := Option.none
  let mut title? := Option.none
  for attr in attrs do
    match attr with
    | .inl k =>
      if kind?.isNone then
        kind? := some k
      else
        Parsec.fail "redundant kind specifications"
    | .inr n =>
      if title?.isNone then
        title? := some n
      else
        Parsec.fail "redundant name specifications"
  return { lang, title?, kind? }

end Parse

def parse (s : String) : Except String ErrorExplanationCodeInfo :=
  Parse.infoString.run s |>.mapError (fun s => s!"Invalid code block info string: {s}")

end ErrorExplanationCodeInfo

section LeanRendering

open Verso Genre Manual SubVerso Highlighting

def runMWE (input : String) : MetaM (Command.State × Parser.InputContext × Array (Syntax ⊕ Substring)) := do
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (hdrStx, s, msgs) ← Parser.parseHeader inputCtx
  let (env, msgs) ← processHeader hdrStx {} msgs inputCtx
  let cmdState := Command.mkState env msgs

  -- If header processing failed, don't try to elaborate the body; however, we
  -- must still parse it for the syntax highlighter
  let shouldElab := !msgs.hasErrors
  let mut (cmdState, stxs) ← processCommands inputCtx s cmdState shouldElab

  -- TODO: improve efficiency
  stxs := #[hdrStx] ++ stxs
  let stxOrStrs ← addMissingSubstrs stxs inputCtx
  return (cmdState, inputCtx, stxOrStrs)
where
  processCommands (inputCtx : Parser.InputContext) (s : Parser.ModuleParserState) (cmdState : Command.State) (doElab : Bool) := do
    let mut s := s
    let mut cmdState := cmdState
    let mut stxs := #[]
    repeat
      let scope := cmdState.scopes.head!
      let pmctx : Parser.ParserModuleContext := {
        env := cmdState.env,
        options := scope.opts,
        currNamespace := scope.currNamespace,
        openDecls := scope.openDecls
      }
      let (stx, s', msgs') := Parser.parseCommand inputCtx pmctx s cmdState.messages
      s := s'
      cmdState := {cmdState with messages := msgs'}
      stxs := stxs.push stx
      let cmdCtx : Command.Context := {
        cmdPos       := s.pos
        fileName     := inputCtx.fileName
        fileMap      := inputCtx.fileMap
        snap?        := none
        cancelTk?    := none
      }
      if doElab then
        try
          (_, cmdState) ← Command.elabCommandTopLevel stx |>.run cmdCtx |>.run cmdState
        catch e =>
          throwError m!"Error during command elaboration: {e.toMessageData}"
      if Parser.isTerminalCommand stx then
        break
    return (cmdState, stxs)

  addMissingSubstrs (stxs : Array Syntax) (inputCtx : Parser.InputContext) : MetaM (Array (Syntax ⊕ Substring)) := do
    -- HACK: fill in the (malformed) source that was skipped by the parser
    let mut last : String.Pos := 0
    let mut stxOrStrs : Array (Syntax ⊕ Substring) := #[]
    for stx in stxs do
      let some this := stx.getPos?
        | stxOrStrs := stxOrStrs.push (.inl stx)  -- empty headers have no info
          continue
      if this != last then
        let missedStr := Substring.mk inputCtx.input last this
        stxOrStrs := stxOrStrs.push (.inr missedStr)
      stxOrStrs := stxOrStrs.push (.inl stx)
      last := stx.getTrailingTailPos?.getD this
    return stxOrStrs

private def abbrevFirstLine (width : Nat) (str : String) : String :=
  let str := str.trimLeft
  let short := str.take width |>.replace "\n" "⏎"
  if short == str then short else short ++ "…"

-- TODO: calling this repeatedly for s spans with an m-message log should be O(max(m,s)), not O(m*s)
private def findMessagesForUnparsedSpan (ictx : Parser.InputContext) (src : Substring) (msgs : Array Message) : IO Highlighted := do
  let msgsHere := msgs.filterMap fun m =>
    let pos := ictx.fileMap.ofPosition m.pos
    let endPos := ictx.fileMap.ofPosition (m.endPos.getD m.pos)
    if src.startPos ≤ pos && pos ≤ src.stopPos then
      some (m, pos, min src.stopPos endPos)
    else
      none

  if msgsHere.isEmpty then
    return .text src.toString

  let mut res := #[]
  for (msg, start, fin) in msgsHere do
    if src.startPos < start then
      let initialSubstr := { src with stopPos := start }
      res := res.push (.text initialSubstr.toString)
    let kind : Highlighted.Span.Kind :=
      match msg.severity with
      | .error => .error
      | .warning => .warning
      | .information => .info
    let content := { src with startPos := start, stopPos := fin }
    res := res.push (.span #[(kind, ← openUntil.contents msg)] (.text content.toString))
    if fin < src.stopPos then
      let finalSubstr := { src with startPos := fin }
      res := res.push (.text finalSubstr.toString)
  return .seq res


def leanMWE : CodeBlockExpander
  | args, str => Manual.withoutAsync <| do
    let config ← LeanBlockConfig.parse.run args

    let src := str.getString
    let (cmdState, inputCtx, cmds) ← runMWE src
    try
      let mut hls := Highlighted.empty
      let nonSilentMsgs := cmdState.messages.toArray.filter (!·.isSilent)
      for cmd in cmds do
        let hl ←
          match cmd with
          | .inl cmd => withTheReader Core.Context (fun ctx => { ctx with
                  fileMap := inputCtx.fileMap
                  fileName := inputCtx.fileName }) <|
                highlight cmd nonSilentMsgs cmdState.infoState.trees
          | .inr cmd =>
            findMessagesForUnparsedSpan inputCtx cmd nonSilentMsgs
        hls := hls ++ hl

      if let some name := config.name then
        let msgs ← nonSilentMsgs.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        saveOutputs name msgs.toList
      let range : Option Lsp.Range := none
      pure #[← ``(Block.other (Block.lean $(quote hls) (some $(quote (← getFileName))) $(quote range)) #[Block.code $(quote str.getString)])]
    finally
      unsafe cmdState.env.freeRegions
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str

end LeanRendering

def Block.errorExample (titles : Array String) : Block where
  name := `Manual.Block.errorExample
  data := toJson titles

@[block_extension Block.errorExample]
def Block.errorExample.descr : BlockDescr where
  traverse id data _blocks := do
    let name :=
      match FromJson.fromJson? (α := Option String) data with
      | .ok (some name) => name
      | _ => "error-example"
    discard <| externalTag id (← read).path name
    pure none
  toTeX := none
  extraCss := [r#"
.error-example-tabpanel-hidden {
  display: none;
}
.error-example-container:not(:last-child) {
  border-bottom: 1px solid gray;
  padding-bottom: var(--verso--box-padding);
}
.error-example-tab-list [role="tab"] {
  position: relative;
  z-index: 1;
  background: white;
  border: 0;
  padding: 0.2em;
  cursor: pointer;
}
.error-example-tab-list [role="tab"]:not(:last-child) {
  margin-right: 1rem;
}
.error-example-tab-list [role="tab"][aria-selected="true"] {
  border-bottom: 1px solid gray;
}
  "#]
  extraJs := [
r#"
window.addEventListener('DOMContentLoaded', () => {
  const tabLists = document.querySelectorAll('.error-example-tab-list')
  tabLists.forEach(tabList => {
    const tabs = tabList.querySelectorAll(':scope > [role="tab"]')

    const setActiveTab = (e) => {
      for (const tab of tabs) {
        const controllee = document.getElementById(tab.getAttribute('aria-controls'))
        if (tab === e.target) {
          tab.setAttribute('aria-selected', true)
          controllee.classList.remove('error-example-tabpanel-hidden')
        } else {
          tab.setAttribute('aria-selected', false)
          controllee.classList.add('error-example-tabpanel-hidden')
        }
      }
    }

    tabs.forEach(tab => {
      tab.addEventListener('click', setActiveTab)
    })

    let focusedIdx = 0
    tabList.addEventListener('keydown', e => {
      if (e.key === 'ArrowRight' || e.key === 'ArrowLeft') {
        tabs[focusedIdx].setAttribute('tabindex', -1)
        focusedIdx =
          e.key === 'ArrowRight'
          ? (focusedIdx + 1) % tabs.length
          : (focusedIdx - 1 + tabs.length) % tabs.length
        tabs[focusedIdx].setAttribute('tabindex', 0)
        tabs[focusedIdx].focus()
      }
    })
  })
})
  "#]
  toHtml := some fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
    let .ok titles := FromJson.fromJson? (α := Array String) info
      | HtmlT.logError "Invalid titles JSON for example block"
        pure .empty
    unless titles.size == contents.size do
      HtmlT.logError "Mismatched number of titles and contents for example block: \
        Found {contents.size} tab panels but {titles.size} titles."
      return .empty
    let some (_, htmlId) := (← HtmlT.state).externalTags[id]?
      | HtmlT.logError "Could not find tag for error example"
        pure .empty
    let buttons ← titles.mapIdxM fun i (title : String) => do
      let (tabIndex, selected) := if i == 0 then ("0", "true") else ("-1", "false")
      let idxStr := toString i
      return {{
        <button type="button" role="tab"
            aria-selected={{selected}}
            tabindex={{tabIndex}}
            id={{s!"{htmlId.toString}-button-{idxStr}"}}
            aria-controls={{s!"{htmlId.toString}-panel-{idxStr}"}}>
          {{title}}
        </button>
      }}
    let panels ← contents.mapIdxM fun i b => do
      let className := if i == 0 then "" else "error-example-tabpanel-hidden"
      let idxStr := toString i
      return {{
        <div role="tabpanel"
            class={{className}}
            id={{s!"{htmlId.toString}-panel-{idxStr}"}}
            aria-labelledby={{s!"{htmlId.toString}-button-{i}"}}>
          {{ ← goB b }}
        </div>
      }}
    pure {{
      <div class="error-example-container">
        <div class="error-example-tab-list" role="tablist" aria-label="Code Samples">
          {{buttons}}
        </div>
        <div class="error-example-tab-view">
          {{panels}}
        </div>
      </div>
    }}

private def mkExampleName (errorName : Name) (idx : Nat) : String :=
  s!"{errorName.toString}-block{idx}"

structure ExplanMDElabContext where
  name : Name

structure ExplanMDElabState where
  codeBlockIdx : Nat

abbrev ExplanMDElabM := ReaderT ExplanMDElabContext (StateT ExplanMDElabState DocElabM)

def tryElabErrorExplanationCodeBlock (errorName : Name) (info? lang : Option String) (str : String) : ExplanMDElabM Term := do
  if let some info := info? then
    let { lang, kind?, .. } ← match ErrorExplanationCodeInfo.parse info with
      | .ok x => pure x
      | .error e => throwError e
    if lang == "output" then
      -- TODO: unify with below case
      let name := mkExampleName errorName (← get).codeBlockIdx
      let args := #[(← `(argument| $(mkIdent name.toName):ident))]
      let parsedArgs ← parseArgs args
      let blocks ← withFreshMacroScope <| leanOutput parsedArgs (quote str)
      return (← ``(Verso.Doc.Block.concat #[$blocks,*]))
    else if kind?.isSome then
      modify fun s => { s with codeBlockIdx := s.codeBlockIdx + 1 }
      let mut args := #[]
      let name := mkExampleName errorName (← get).codeBlockIdx
      args := args.push (← `(argument| name := $(mkIdent name.toName):ident))
      if let some kind := kind? then
        let errorVal ← if kind == .broken then `(arg_val|true) else `(arg_val|false)
        args := args.push (← `(argument| error := $errorVal))
      let parsedArgs ← parseArgs args
      let blocks ← withFreshMacroScope <| leanMWE parsedArgs (quote str)
      return (← ``(Verso.Doc.Block.concat #[$blocks,*]))
  -- If this isn't labeled as an MWE, fall back on the usual elaborator
  tryElabBlockCode info? lang str

/-- The code contents of an example, not including any subsequent description. -/
private structure ExampleContents where
  title : Array Term
  codeBlocks : Array (Term × Option String)
  descrBlocks : Array Term

structure ExplanElabContext where
  /-- The blocks in the error explanation to elaborate. -/
  blocks : Array MD4Lean.Block
  /-- Name of the error described by the explanation being elaborated. -/
  name : Name

structure ExplanElabState where
  /-- The index of the next block in the context's `blocks` to elaborate. -/
  blockIdx : Nat := 0
  /-- Active Markdown header levels that can be closed by subsequent Markdown -/
  levels : List (Nat × Nat) := []
  /-- The index of the current code block within this explanation. -/
  codeBlockIdx : Nat := 0

abbrev ExplanElabM := ReaderT ExplanElabContext (StateT ExplanElabState PartElabM)

def ExplanElabM.run (x : ExplanElabM α) (name : Name) (blocks : Array MD4Lean.Block) :
    PartElabM (α × ExplanElabState) :=
  ReaderT.run x { name, blocks } |>.run {}

def ExplanElabM.nextBlock? : ExplanElabM (Option MD4Lean.Block) := do
  let curBlockIdx := (← get).blockIdx
  let blocks := (← read).blocks
  if h : curBlockIdx ≥ blocks.size then
    return none
  else
    modify fun s => { s with blockIdx := s.blockIdx + 1 }
    return blocks[curBlockIdx]

def ExplanElabM.backtrack : ExplanElabM Unit := do
  modify fun s => { s with blockIdx := s.blockIdx - 1 }

def ExplanElabM.liftExplanMDElabM (x : ExplanMDElabM α) : ExplanElabM α := do
  let { codeBlockIdx, .. } ← get
  let { name, .. } ← read
  let (res, st) ← x.run { name } { codeBlockIdx }
  modify fun s => { s with codeBlockIdx := st.codeBlockIdx }
  return res

instance : MonadLift ExplanMDElabM ExplanElabM where
  monadLift := ExplanElabM.liftExplanMDElabM

-- TODO: try to reduce duplication between this and the next function
def blockFromExplanationMarkdown (b : MD4Lean.Block) : ExplanElabM Term := do
  let name := (← read).name
  let tactics ← Elab.Tactic.Doc.allTacticDocs
  let keywords := tactics.map (·.userName)
  let ref ← getRef
  let s ← (saveState : TermElabM _)
  let (block, outputs) ←
    try
      let res ←
        blockFromMarkdown b
          (handleHeaders := Markdown.strongEmphHeaders)
          (elabInlineCode := some fun p s => tryElabInlineCode tactics keywords p s)
          (elabBlockCode := some fun i l s => withRef ref <| tryElabErrorExplanationCodeBlock name i l s)
      synthesizeSyntheticMVarsUsingDefault
      pure (res, leanOutputs.getState (← getEnv))
    finally
      -- TODO: this logic is now inappropriate because it's swallowing elab errors
      let { messages, .. } ← getThe Core.State
      s.restore
      modifyThe Core.State fun s => { s with messages }
  -- This is necessary after state restoration so we can refer to the generated outputs
  modifyEnv (leanOutputs.setState · outputs)
  return block

def partFromExplanationMarkdown (b : MD4Lean.Block) : ExplanElabM Unit := do
  let tactics ← Elab.Tactic.Doc.allTacticDocs
  let keywords := tactics.map (·.userName)
  let ref ← getRef
  let s ← (saveState : TermElabM _)
  let name := (← read).name
  let (ls, outputs) ←
    try
      let res ←
        addPartFromMarkdown b
          (handleHeaders := Markdown.strongEmphHeaders)
          (elabInlineCode := some fun p s => tryElabInlineCode tactics keywords p s)
          (elabBlockCode := some fun i l s => withRef ref <| tryElabErrorExplanationCodeBlock name i l s)
      synthesizeSyntheticMVarsUsingDefault
      pure (res, leanOutputs.getState (← getEnv))
    finally
      -- TODO: this logic is now inappropriate because it's swallowing elab errors
      let { messages, .. } ← getThe Core.State
      s.restore
      modifyThe Core.State fun s => { s with messages }
  modifyThe ExplanElabState ({ · with levels := ls })
  -- This is necessary after state restoration so we can refer to the generated outputs
  modifyEnv (leanOutputs.setState · outputs)

private def infoOfCodeBlock : MD4Lean.Block → Except String ErrorExplanationCodeInfo
  | .code info _ _ _ => do
    let txt ← attr' info
    ErrorExplanationCodeInfo.parse txt
  | el => .error s!"block element is not a code block but instead:\n{repr el}"

private def blockHasExplanationCodeInfo
    (b : MD4Lean.Block) (expLang : String)
    (expKind? : Option ErrorExplanationCodeInfo.Kind := none)
  : DocElabM Bool := do
  let { kind?, lang, .. } ← match infoOfCodeBlock b with
  | .ok x => pure x
  | .error _ => return false
  let optMatch {α : Type} [BEq α] (expected? : Option α) (actual? : Option α) :=
    if let some expected := expected? then
      some expected == actual?
    else
      true
  return lang == expLang && optMatch expKind? kind?

private def expectExplanationCodeInfo
    (b : MD4Lean.Block) (expLang : String) (expKind : ErrorExplanationCodeInfo.Kind)
  : DocElabM Unit := do
  let { kind?, lang, .. } ← match infoOfCodeBlock b with
    | .ok x => pure x
    | .error e => throwError e
  unless lang == expLang do
    throwError "Expected a code block with language '{expLang}', but found '{lang}'"
  unless kind? == some expKind do
    let str := kind?.map toString |>.getD "unspecified"
    throwError "Expected a code block of kind '{expKind}', but found '{str}'"

-- TODO: do this properly
private def termsOfTexts (txts : Array MD4Lean.Text) : DocElabM (Array Term) := do
  let (stxs, _) ← (txts.mapM (inlineFromMarkdown ·)).run' none {
    elabInlineCode := tryElabInlineCode #[] #[]
    headerHandlers := ⟨Markdown.strongEmphHeaders⟩,
    elabBlockCode := tryElabBlockCode
  } {}
  return stxs

private def examplesHeader := "Examples"

private def isExamplesHeaderText (txt : Array MD4Lean.Text) : Bool :=
  if _ : txt.size = 1 then
    match txt[0] with
    | .normal str => str.trim == "Examples"
    | _ => false
  else false

private def makeExample (contents : ExampleContents) : DocElabM Term := do
  let {title, codeBlocks, descrBlocks } := contents
  let titles := codeBlocks.mapIdx fun i (_, title?) =>
    let fallback :=
      if i == 0 then
        "Original"
      else if codeBlocks.size == 2 then
        "Fixed"
      else
        s!"Fixed {i}"
    title?.getD fallback
  let codeBlocks := codeBlocks.map Prod.fst
  let codeExample ← ``(Block.other (Block.errorExample $(quote titles)) #[$codeBlocks,*])
  ``(Block.other (Block.example none (opened := true))
            #[Block.para #[$title,*], $codeExample, $descrBlocks,*])

def titleOfCodeBlock? (b : MD4Lean.Block) : Option String := do
  let info ← infoOfCodeBlock b |>.toOption
  info.title?

def closeExplanationPart : PartElabM Unit := do
  if let some ctxt' := (← getThe PartElabM.State).partContext.close default then -- TODO: source position!
    modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
  else
    throwError m!"Failed to close the last-opened explanation part"

def addNonExampleBlocks (allowExamplesHeader := true) := do
  repeat
    let some block ← ExplanElabM.nextBlock?
      | return
    if let MD4Lean.Block.header 1 txt := block then
      if isExamplesHeaderText txt then
        if allowExamplesHeader then
          partFromExplanationMarkdown block
          break
        else
          throwError "Found multiple 'Examples' headers in the same explanation"
    partFromExplanationMarkdown block

def getBrokenTermAndTitle : ExplanElabM (Term × Option String) := do
  let some brokenBlock ← ExplanElabM.nextBlock?
      | throwError "Found a header for a new example, but no following `broken` code block"
    expectExplanationCodeInfo brokenBlock "lean" .broken
    let brokenTerm ← blockFromExplanationMarkdown brokenBlock
    let title? := titleOfCodeBlock? brokenBlock
    return (brokenTerm, title?)

partial def repeatedly (x : ExplanElabM (Option α)) : ExplanElabM (Array α) :=
  return (← go x).toArray
where
  go x := do
    if let some result := (← x) then
      return result :: (← go x)
    else
      return []

def getOutputTerm? : ExplanElabM (Option Term) := do
  let some block ← ExplanElabM.nextBlock?
    | return none
  if (← blockHasExplanationCodeInfo block "output") then
    return some (← blockFromExplanationMarkdown block)
  else
    ExplanElabM.backtrack
    return none

def getFixedTermAndTitle? : ExplanElabM (Option (Term × Option String)) := do
  let some block ← ExplanElabM.nextBlock?
    | return none
  if (← blockHasExplanationCodeInfo block "lean" (some .fixed)) then
    let title? := titleOfCodeBlock? block
    return some (← blockFromExplanationMarkdown block, title?)
  else
    ExplanElabM.backtrack
    return none

def getFixedTermAndOutputs? : ExplanElabM (Option (Term × Array Term × Option String)) := do
  let some (fixedTerm, fixedTitle?) ← getFixedTermAndTitle? | return none
  let outputs ← repeatedly getOutputTerm?
  return some (fixedTerm, outputs, fixedTitle?)

def getExampleDescriptionTerm? : ExplanElabM (Option Term) := do
  let some block ← ExplanElabM.nextBlock?
    | return none
  if block matches .header 2 _ then
    ExplanElabM.backtrack
    return none
  else
    return some (← blockFromMarkdown block)

def addExampleBlocks : ExplanElabM Unit := do
  repeat
    let some (.header 2 txts) ← ExplanElabM.nextBlock?
      | return
    let title ← termsOfTexts txts
    -- Broken code and output(s)
    let (brokenCodeTerm, brokenTitle?) ← getBrokenTermAndTitle
    let brokenOutputTerms ← repeatedly getOutputTerm?
    if brokenOutputTerms.isEmpty then
      throwError m!"Missing output for broken code snippet in example '{title}'"
    -- TODO: parse and add titles for blocks
    let brokenWithTitle :=
      (← ``(Block.concat #[$brokenCodeTerm, $brokenOutputTerms,*]), brokenTitle?)

    -- Fixed version(s) with optional output(s)
    let fixedTermsAndOutputs ← repeatedly getFixedTermAndOutputs?
    if fixedTermsAndOutputs.isEmpty then
      throwError m!"Found a `broken` code block but no following `fixed` code block for example '{title}'"
    let fixedWithTitles ← fixedTermsAndOutputs.mapM fun (code, outs, title?) =>
      return (← ``(Block.concat #[$code, $outs,*]), title?)

    -- Arbitrary description of above code blocks
    let exampleDescrs ← repeatedly getExampleDescriptionTerm?
    let exampleInfo : ExampleContents := {
      title
      codeBlocks := #[brokenWithTitle] ++ fixedWithTitles
      descrBlocks := exampleDescrs
    }
    let ex ← makeExample exampleInfo
    PartElabM.addBlock ex

def addExplanationBlocks : ExplanElabM Unit := do
  addNonExampleBlocks
  addExampleBlocks
  addNonExampleBlocks (allowExamplesHeader := false)

def errorExplanationDomain := `Manual.errorExplanation

def Inline.errorExplanation (errorName : Name) (summary : String) : Inline where
  name := `Manual.Inline.errorExplanation
  data := toJson #[errorName.toString, summary]

@[inline_extension Inline.errorExplanation]
def Inline.errorExplanation.descr : InlineDescr where
  init st := st
    |>.setDomainTitle errorExplanationDomain "Error Explanations"
    |>.setDomainDescription errorExplanationDomain "Explanations of error messages and warnings produced during compilation"

  traverse id info _ := do
    let .ok #[errorName, summary] := FromJson.fromJson? (α := Array String) info
      | Manual.logError s!"Invalid JSON for error explanation:\n{info}"; pure none
    modify fun s =>
      s |>.saveDomainObject errorExplanationDomain errorName id
        |>.saveDomainObjectData errorExplanationDomain errorName (json%{"summary": $summary})
    let path ← (·.path) <$> read
    discard <| Verso.Genre.Manual.externalTag id path errorName
    pure none

  toTeX := none
  toHtml := some fun go id _info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
    let xref ← HtmlT.state
    let idAttr := xref.htmlId id
    return {{
      <span {{idAttr}}>
        {{← contents.mapM go}}
      </span>
    }}

def Block.errorExplanationMetadata (metadata : ErrorExplanation.Metadata) : Block where
  name := `Manual.Block.errorExplanationMetadata
  data := toJson metadata

@[block_extension Block.errorExplanationMetadata]
def Block.errorExplanationMetadata.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := ["
  .error-explanation-metadatum:not(:last-child):after {
    content: '|';
    margin: 0 10px;
  }
  .error-explanation-removed-warning {
    border: 1px solid var(--verso-warning-color);
    border-radius: 0.5rem;
    padding-left: var(--verso--box-padding);
    padding-right: var(--verso--box-padding);
  }
  "]
  toHtml := some fun _goI _goB _id info _contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
    let .ok metadata := FromJson.fromJson? (α := ErrorExplanation.Metadata) info
      | HtmlT.logError "Failed to parse info for error explanation metadata block:\n{metadata}"
        pure .empty
    let deprecatedWarning :=
      if metadata.removedVersion.isSome then
        {{ <div class="error-explanation-removed-warning">
             <p><strong>"Note: "</strong> "This diagnostic is no longer produced by the compiler."</p>
           </div> }}
      else
        .empty
    let sevText := if metadata.severity matches .warning then "Warning" else "Error"
    let entries := #[("Severity", sevText), ("Since", metadata.sinceVersion)]
      ++ (metadata.removedVersion.map fun v => #[("Removed", v)]).getD #[]
    let entries := entries.map fun (label, data) =>
      {{ <span class="error-explanation-metadatum">
           <strong>{{Html.text true label}}": "</strong>
           {{Html.text true data}}
          </span> }}
    return {{
      <div class="error-explanation-metadata">
        {{deprecatedWarning}}
        <p><em>{{metadata.summary}}</em></p>
        <p>{{entries}}</p>
        <hr />
      </div>
    }}

deriving instance Quote for ErrorExplanation.Metadata

def addExplanationMetadata (metadata : ErrorExplanation.Metadata) : PartElabM Unit := do
  PartElabM.addBlock (← ``(Block.other (Block.errorExplanationMetadata $(quote metadata)) #[]))

structure ExplanationConfig where
  name : Ident

variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] in
def ExplanationConfig.parser : ArgParse.ArgParse m ExplanationConfig :=
  ExplanationConfig.mk <$> .positional `name {
    description := "name of error whose explanation to display",
    get := fun
      | .name x => pure x
      | other => throwError "Expected error name, got {repr other}"
  }

def addExplanationBlocksFor (name : Name) : PartElabM Unit := do
  let explan? ← getErrorExplanation? name
  match explan? with
  | .none =>
    throwError m!"Adding explanation blocks failed: Could not find explanation for {name}"
  | some explan =>
    try
      let some ast := MD4Lean.parse explan.doc
        | throwErrorAt (← getRef) "Failed to parse docstring as Markdown"
      addExplanationMetadata explan.metadata
      -- TODO: do we need error handling after the fact?
      let (_, { levels, .. }) ← addExplanationBlocks.run name ast.blocks
      for _ in levels do
        closeExplanationPart
    catch
      | .error ref msg => throw <| .error ref m!"Failed to process explanation for {name}: {msg}"
      | e => throw e

/--
Renders a single error explanation for `name` via `{explanation name}`.
-/
@[part_command Verso.Syntax.block_role]
def explanation : PartCommand
  | `(block|block_role{explanation $args*}) => do
    let config ← ExplanationConfig.parser.run (← parseArgs args)
    addExplanationBlocksFor config.name.getId
  | _ => Lean.Elab.throwUnsupportedSyntax

open Verso Doc Elab ArgParse in
open Lean in
@[part_command Verso.Syntax.block_role]
def makeExplanations : PartCommand
  | `(block|block_role{make_explanations}) => do
    let explans ← getErrorExplanationsSorted
    for (name, explan) in explans do
      let titleString := name.toString
      let titleBits := #[← ``(Inline.other (
          Inline.errorExplanation $(quote name) $(quote explan.metadata.summary))
        #[Inline.code $(quote titleString)])]
      PartElabM.push {
        titleSyntax := quote (k := `str) titleString,
        expandedTitle := some (titleString, titleBits),
        metadata := none,
        blocks := #[],
        priorParts := #[]
      }
      addExplanationBlocksFor name
      closeExplanationPart
  | _ => throwUnsupportedSyntax
