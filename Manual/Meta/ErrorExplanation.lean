/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import VersoManual

import Manual.Meta

import Lean.ErrorExplanations

import PreprocessedExplanations

open Lean Elab
open Verso.ArgParse
open Verso.Doc Elab
open Verso.Genre.Manual Markdown InlineLean
open SubVerso.Highlighting

set_option pp.rawOnError true
set_option guard_msgs.diff true

namespace Manual

/-- Loads the JSON data file for the preprocessed MWE code block `name`. -/
def loadPreprocessedMWE (name : Name) (contents : String)
    : MetaM (Highlighted × Array (MessageSeverity × String)) := do
  let fileName : String := name.toString ++ ".json"
  let path := preprocessedExplanationsRoot / fileName
  unless (← System.FilePath.pathExists path) do
    throwError m!"Did not find expected preprocessed code block file `{path}`. \
      Run `lake build error_explanations`."
  let fileContents ← IO.FS.readFile path
  let json ← ofExcept <| Json.parse fileContents
  let hls ← ofExcept <| json.getObjVal? "highlighted"
    >>= FromJson.fromJson? (α := Highlighted)
  let messages ← ofExcept <| json.getObjVal? "messages"
    >>= FromJson.fromJson? (α := Array (MessageSeverity × String))
  let fileHash ← ofExcept <| json.getObjVal? "hash"
    >>= FromJson.fromJson? (α := UInt64)
  let fileVersion ← ofExcept <| json.getObjVal? "version" >>= Json.getStr?
  unless fileHash == hash contents && fileVersion == Lean.versionString do
    throwError m!"Preprocessed code block data file `{path}` is out of date. \
      Run `lake build error_explanations`."
  return (hls, messages)

/--
A modified version of `Verso.Genre.Manual.InlineLean.lean` for rendering an MWE
in an error explanation.
-/
def explanationMWE : CodeBlockExpander
  | args, str => Manual.withoutAsync <| do
    let config ← LeanBlockConfig.parse.run args

    let some name := config.name
      | throwError "Explanation MWE is missing a name"
    let (hls, msgs) ← loadPreprocessedMWE name str.getString
    saveOutputs name msgs.toList

    pure #[← ``(Block.other
      (Block.lean $(quote hls) (some $(quote (← getFileName))) none)
      #[Block.code $str])]

/-
A tabbed container for MWEs in an error explanation example. Must satisfy the
invariant that `titles.size` is equal to the number of children of this block.
-/
block_extension Block.tabbedMWEs (titles : Array String) where
  data := toJson titles
  traverse id data _blocks := do
    let name :=
      match FromJson.fromJson? (α := Option String) data with
      | .ok (some name) => name
      | _ => "error-example"
    discard <| externalTag id (← read).path name
    pure none
  toTeX := none
  extraCss := [r#"
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
/* this rule and the following ensure that all tabs are the same height */
.error-example-tab-view {
  display: flex;
}
.error-example-tabpanel {
  margin-right: -100%;
  width: 100%;
  display: block;
}
.error-example-tabpanel.error-example-tabpanel-hidden {
  visibility: hidden;
}
.error-example-tabpanel .hl.lean .token {
  /* unset transition to avoid lag when switching panels */
  transition: visibility 0s;
}
  "#]
  extraJs := [r#"
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
      HtmlT.logError s!"Mismatched number of titles and contents for example block: \
        Found {contents.size} tab panels but {titles.size} titles."
      return .empty
    let some { htmlId, .. } := (← HtmlT.state).externalTags[id]?
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
      let className := "error-example-tabpanel" ++ if i == 0 then "" else " error-example-tabpanel-hidden"
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

/--
Given the name of the explanation in which it occurs and its index among all
code blocks therein, generates a name for a code block in an error explanation.
This is used for output tracking and to locate its corresponding JSON file.
-/
private def mkExampleName (errorName : Name) (idx : Nat) : Name :=
  errorName ++ s!"block{idx}".toName

structure ExplanCodeElabM.Context where
  name : Name

structure ExplanCodeElabM.State where
  codeBlockIdx : Nat

/--
The monad in which code blocks within an error explanation are elaborated.
-/
abbrev ExplanCodeElabM :=
  ReaderT ExplanCodeElabM.Context (StateT ExplanCodeElabM.State DocElabM)

/--
Attempts to elaborate block code in an error explanation: Lean (and unlabeled)
blocks should have a corresponding preprocessing cache file, output blocks are
checked against their corresponding Lean block's output, and all other code
blocks are rendered using the default Verso code element.
-/
def tryElabErrorExplanationCodeBlock (errorName : Name) (errorSev : MessageSeverity)
    (info? _lang : Option String) (str : String) : ExplanCodeElabM Term := do
  if let some info := info? then
    let { lang, kind?, .. } ← match ErrorExplanation.CodeInfo.parse info with
      | .ok x => pure x
      | .error e => throwError e
    if lang == "output" then
      let codeBlockIdx := (← get).codeBlockIdx - 1
      let name := mkExampleName errorName codeBlockIdx
      let args := #[(← `(argument| $(mkIdent name):ident))]
      let parsedArgs ← parseArgs args
      let blocks ← try
        withFreshMacroScope <| leanOutput parsedArgs (quote str)
      catch
        | .error ref msg =>
          let kindStr := kind?.map (s!" ({·} example)") |>.getD ""
          -- Log rather than throw so we can detect all invalid outputs in a
          -- single build
          logErrorAt ref m!"Invalid output for {(← read).name} code block \
            #{codeBlockIdx}{kindStr}: {msg}"
          pure #[← ``(Verso.Doc.Block.code "<invalid output>")]
        | e@(.internal ..) => throw e
      return (← ``(Verso.Doc.Block.concat #[$blocks,*]))
    else if lang == "" || lang == "lean" then
      let mut args := #[]
      let name := mkExampleName errorName (← get).codeBlockIdx
      args := args.push (← `(argument| name := $(mkIdent name):ident))
      if let some kind := kind? then
        let errorVal ← if kind == .broken && errorSev == .error then
          `(arg_val|true)
        else
          `(arg_val|false)
        args := args.push (← `(argument| error := $errorVal))
      let parsedArgs ← parseArgs args
      let blocks ← withFreshMacroScope <| explanationMWE parsedArgs (quote str)
      modify fun s => { s with codeBlockIdx := s.codeBlockIdx + 1 }
      return (← ``(Verso.Doc.Block.concat #[$blocks,*]))
  -- If this isn't labeled as an MWE, fall back on a basic code block
  ``(Verso.Doc.Block.code $(quote str))

/-- The code contents of an example, not including any subsequent description. -/
private structure ExampleContents where
  title : Array Term
  codeBlocks : Array (Term × Option String)
  descrBlocks : Array Term

structure ExplanElabM.Context where
  /-- The blocks in the error explanation to elaborate. -/
  blocks : Array MD4Lean.Block
  /-- Name of the error described by the explanation being elaborated. -/
  name : Name
  /-- Severity of error described by the explanation being elaborated. -/
  severity : MessageSeverity

structure ExplanElabM.State where
  /-- The index of the next block in the context's `blocks` to elaborate. -/
  blockIdx : Nat := 0
  /-- Active Markdown header levels that can be closed by subsequent Markdown -/
  levels : List (Nat × Nat) := []
  /-- The index of the current code block within this explanation. -/
  codeBlockIdx : Nat := 0

/-- The monad in which error explanations are elaborated. -/
abbrev ExplanElabM := ReaderT ExplanElabM.Context (StateT ExplanElabM.State PartElabM)

def ExplanElabM.run (x : ExplanElabM α) (name : Name)
    (severity : MessageSeverity) (blocks : Array MD4Lean.Block) :
    PartElabM (α × ExplanElabM.State) :=
  ReaderT.run x { name, blocks, severity } |>.run {}

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

def ExplanElabM.liftExplanCodeElabM (x : ExplanCodeElabM α) : ExplanElabM α := do
  let { codeBlockIdx, .. } ← get
  let { name, .. } ← read
  let (res, st) ← x.run { name } { codeBlockIdx }
  modify fun s => { s with codeBlockIdx := st.codeBlockIdx }
  return res

instance : MonadLift ExplanCodeElabM ExplanElabM where
  monadLift := ExplanElabM.liftExplanCodeElabM

/--
Elaborates inline code in strict mode, restoring the state afterward.

We have to do state restoration after each inline elaboration because the block
elaborator needs to have its `TermElabM` state changes persisted, as the part
elaborator modifies this state during elaboration.
-/
private def tryElabInlineCodeStrictRestoringState
    (tactics : Array Tactic.Doc.TacticDoc) (keywords : Array String)
    (prevWord? : Option String) (str : String) : ExplanElabM Term := do
  let b ← (saveState : TermElabM _)
  try
    let t ← tryElabInlineCodeStrict tactics keywords prevWord? str
    Term.synthesizeSyntheticMVarsUsingDefault
    pure t
  finally
    b.restore

/-- Returns a Verso term corresponding to `b`. -/
def blockFromExplanationMarkdown (b : MD4Lean.Block) : ExplanElabM Term := do
  let { name, severity .. } ← read
  let tactics ← Elab.Tactic.Doc.allTacticDocs
  let keywords := tactics.map (·.userName)
  let ref ← getRef
  blockFromMarkdown b
    (handleHeaders := Markdown.strongEmphHeaders)
    (elabInlineCode := some (tryElabInlineCodeStrictRestoringState tactics keywords))
    (elabBlockCode := some fun i l s => withRef ref <|
      tryElabErrorExplanationCodeBlock name severity i l s)

/-- Add block(s) corresponding to `b` to the current document part. -/
def addPartFromExplanationMarkdown (b : MD4Lean.Block) : ExplanElabM Unit := do
  let tactics ← Elab.Tactic.Doc.allTacticDocs
  let keywords := tactics.map (·.userName)
  let ref ← getRef
  let {name, severity .. } ← read
  let ls ← addPartFromMarkdown b
    (handleHeaders := Markdown.strongEmphHeaders)
    (elabInlineCode := some (tryElabInlineCodeStrictRestoringState tactics keywords))
    (elabBlockCode := some fun i l s => withRef ref <|
      tryElabErrorExplanationCodeBlock name severity i l s)
  modifyThe ExplanElabM.State ({ · with levels := ls })

/-- Extracts and parses the info string of a code block. -/
private def infoOfCodeBlock : MD4Lean.Block → Except String ErrorExplanation.CodeInfo
  | .code info _ _ _ => do
    let txt ← attr' info
    ErrorExplanation.CodeInfo.parse txt
  | el => .error s!"Cannot get code block info from non-code block element:\n{repr el}"

/--
Returns `true` if `b` is a block with language `expLang` and, if
`expKind? = some expKind`, kind `expKind`.
-/
private def blockHasExplanationCodeInfo
    (b : MD4Lean.Block) (expLang : String)
    (expKind? : Option ErrorExplanation.CodeInfo.Kind := none)
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

/-- Throws an error if `b` is not a code block with language `expLang` and kind `expKind`. -/
private def expectExplanationCodeInfo
    (b : MD4Lean.Block) (expLang : String) (expKind : ErrorExplanation.CodeInfo.Kind)
    : DocElabM Unit := do
  let { kind?, lang, .. } ← match infoOfCodeBlock b with
    | .ok x => pure x
    | .error e => throwError  e
  unless lang == expLang do
    throwError "Expected a code block with language `{expLang}`, but found `{lang}`"
  unless kind? == some expKind do
    let str := kind?.map toString |>.getD "unspecified"
    throwError "Expected a code block of kind `{expKind}`, but found `{str}`"

/-- Returns `true` if `txt` is the "Examples" header text. -/
private def isExamplesHeaderText (txt : Array MD4Lean.Text) : Bool :=
  if _ : txt.size = 1 then
    match txt[0] with
    | .normal str => str.trim == "Examples"
    | _ => false
  else false

/-- Convert the accumulated contents of an example into a Verso block term. -/
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
  let codeExample ←
    ``(Block.other (Block.tabbedMWEs $(quote titles)) #[$codeBlocks,*])
  ``(Block.other (Block.example none (opened := true))
      #[Block.para #[$title,*], $codeExample, $descrBlocks,*])

private def titleOfCodeBlock? (b : MD4Lean.Block) : Option String := do
  let info ← infoOfCodeBlock b |>.toOption
  info.title?

/-- Closes the last-opened section, throwing an error on failure. -/
def closeEnclosingSection : PartElabM Unit := do
  -- We use `default` as the source position because the Markdown doesn't have one
  if let some ctxt' := (← getThe PartElabM.State).partContext.close default then
    modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
  else
    throwError m!"Failed to close the last-opened explanation part"

/-- Adds explanation blocks until the "Examples" header is reached. -/
def addNonExampleBlocks := do
  repeat
    let some block ← ExplanElabM.nextBlock?
      | return
    if let MD4Lean.Block.header 1 txt := block then
      if isExamplesHeaderText txt then
        addPartFromExplanationMarkdown block
        break
    addPartFromExplanationMarkdown block

/--
Get the next code block if it's a broken Lean block along with its title.

Note that this function errors on failure, since we never backtrack if a broken
code block is missing, and doing so allows us to provide more granular error
messages.
-/
def getBrokenTermAndTitle : ExplanElabM (Term × Option String) := do
  let some brokenBlock ← ExplanElabM.nextBlock?
    | throwError "Found a header for a new example, but no following `broken` code block"
  -- We don't bother backtracking here since we can't recover
  expectExplanationCodeInfo brokenBlock "lean" .broken
  let brokenTerm ← blockFromExplanationMarkdown brokenBlock
  let title? := titleOfCodeBlock? brokenBlock
  return (brokenTerm, title?)

/-- Execute `x` until it returns `none`. -/
partial def repeatedly (x : ExplanElabM (Option α)) : ExplanElabM (Array α) :=
  go x #[]
where
  go x acc := do
    if let some result := (← x) then
      go x (acc.push result)
    else
      return acc

/-- Get the next block if it is an output code block. -/
def getOutputTerm? : ExplanElabM (Option Term) := do
  let some block ← ExplanElabM.nextBlock?
    | return none
  if (← blockHasExplanationCodeInfo block "output") then
    return some (← blockFromExplanationMarkdown block)
  else
    ExplanElabM.backtrack
    return none

/-- Get the next code block if it is a fixed Lean block, and, if so, its title if it has one. -/
def getFixedTermAndTitle? : ExplanElabM (Option (Term × Option String)) := do
  let some block ← ExplanElabM.nextBlock?
    | return none
  if (← blockHasExplanationCodeInfo block "lean" (some .fixed)) then
    let title? := titleOfCodeBlock? block
    return some (← blockFromExplanationMarkdown block, title?)
  else
    ExplanElabM.backtrack
    return none

/-- Get the next block(s) if they are a fixed code block with zero or more outputs. -/
def getFixedTermAndOutputs? : ExplanElabM (Option (Term × Array Term × Option String)) := do
  let some (fixedTerm, fixedTitle?) ← getFixedTermAndTitle? | return none
  let outputs ← repeatedly getOutputTerm?
  return some (fixedTerm, outputs, fixedTitle?)

/-- Get the next block to elaborate if it's not an example-terminating header. -/
def getExampleDescriptionTerm? : ExplanElabM (Option Term) := do
  let some block ← ExplanElabM.nextBlock?
    | return none
  if block matches .header 1 _ | .header 2 _ then
    ExplanElabM.backtrack
    return none
  else
    return some (← blockFromExplanationMarkdown block)

/--
Add blocks corresponding to the "Examples" section of the explanation. Assumes
that the "Examples" header itself has already been added, and will repeatedly
add examples beginning with a level-2 header, followed by broken and fixed code
blocks with outputs, and descriptions thereof.
-/
def addExampleBlocks : ExplanElabM Unit := do
  repeat
    let some block@(.header 2 titleTexts) ← ExplanElabM.nextBlock? | return
    let `(Verso.Doc.Block.other #[$titleStxs,*]) ← blockFromMarkdown block
        [fun (stxs : Array Term) => ``(Verso.Doc.Block.other #[$stxs,*])]
      | throwError "Unexpected output when elaborating example header"
    let title := titleStxs.getElems
    let titleStr := String.join
      (titleTexts.mapM stringFromMarkdownText |>.toOption.getD #[]).toList

    -- Broken code and output(s)
    let (brokenCodeTerm, brokenTitle?) ← getBrokenTermAndTitle
    let brokenOutputTerms ← repeatedly getOutputTerm?
    if brokenOutputTerms.isEmpty then
      throwError m!"Missing output for broken code snippet in example '{titleStr}'"
    let brokenWithTitle :=
      (← ``(Block.concat #[$brokenCodeTerm, $brokenOutputTerms,*]), brokenTitle?)

    -- Fixed version(s) with optional output(s)
    let fixedTermsAndOutputs ← repeatedly getFixedTermAndOutputs?
    if fixedTermsAndOutputs.isEmpty then
      throwError m!"Found a `broken` code block but no following `fixed` code block for example '{titleStr}'"
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

/--
Adds blocks constituting the explanation body to the document. The topmost
routine for rendering an explanation in `ExplanElabM`.
-/
def addExplanationBodyBlocks : ExplanElabM Unit := do
  addNonExampleBlocks
  addExampleBlocks

deriving instance Quote for ErrorExplanation.Metadata

block_extension Block.errorExplanationMetadata (metadata : ErrorExplanation.Metadata) where
  data := toJson metadata
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
      if metadata.removedVersion?.isSome then
        {{ <div class="error-explanation-removed-warning">
             <p><strong>"Note: "</strong> "This diagnostic is no longer produced."</p>
           </div> }}
      else
        .empty
    let sevText := if metadata.severity matches .warning then "Warning" else "Error"
    let entries := #[("Severity", sevText), ("Since", metadata.sinceVersion)]
      ++ (metadata.removedVersion?.map fun v => #[("Removed", v)]).getD #[]
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

/-- Adds the specified explanation metadata to the document. -/
def addExplanationMetadata (metadata : ErrorExplanation.Metadata) : PartElabM Unit := do
  PartElabM.addBlock (← ``(Block.other (Block.errorExplanationMetadata $(quote metadata)) #[]))

/-- Adds the metadata and bofy of the explanation with name `name` to the document. -/
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
      let (_, { levels, .. }) ← addExplanationBodyBlocks.run name explan.metadata.severity ast.blocks
      for _ in levels do
        closeEnclosingSection
    catch
      | .error ref msg => throw <| .error ref m!"Failed to process explanation for {name}: {msg}"
      | e => throw e

def errorExplanationDomain := `Manual.errorExplanation

def Inline.errorExplanation (errorName : Name) (summary : String) : Inline where
  name := `Manual.Inline.errorExplanation
  data := toJson #[errorName.toString, summary]

@[inline_extension Inline.errorExplanation]
def Inline.errorExplanation.descr : InlineDescr where
  init st := st
    |>.setDomainTitle errorExplanationDomain "Error Explanations"
    |>.setDomainDescription errorExplanationDomain
        "Explanations of error messages and warnings produced during compilation"

  traverse id info _ := do
    let .ok #[errorName, summary] := FromJson.fromJson? (α := Array String) info
      | logError s!"Invalid JSON for error explanation:\n{info}"; pure none
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

/-- Configuration for an `explanation` block. -/
structure ExplanationConfig where
  name : Ident

def ExplanationConfig.parser [Monad m] [MonadError m] : ArgParse m ExplanationConfig :=
  ExplanationConfig.mk <$> .positional `name {
    description := "name of error whose explanation to display",
    get := fun
      | .name x => pure x
      | other => throwError "Expected error name, got {repr other}"
  }

/-- Renders the error explanation for `name` via `{explanation name}`. -/
@[part_command Verso.Syntax.block_role]
def explanation : PartCommand
  | `(block|block_role{explanation $args*}) => do
    let config ← ExplanationConfig.parser.run (← parseArgs args)
    addExplanationBlocksFor config.name.getId
  | _ => Lean.Elab.throwUnsupportedSyntax

open Verso Doc Elab ArgParse in
open Lean in
/-- Renders all error explanations as parts of the current page. -/
@[part_command Verso.Syntax.block_role]
def make_explanations : PartCommand
  | `(block|block_role{make_explanations}) => do
    let explans ← getErrorExplanationsSorted
    for (name, explan) in explans do
      let titleString := name.toString
      let titleBits := #[← ``(Inline.other
        (Inline.errorExplanation $(quote name) $(quote explan.metadata.summary))
        #[Inline.code $(quote titleString)])]
      PartElabM.push {
        titleSyntax := quote (k := `str) titleString,
        expandedTitle := some (titleString, titleBits),
        metadata := none,
        blocks := #[],
        priorParts := #[]
      }
      addExplanationBlocksFor name
      closeEnclosingSection
  | _ => throwUnsupportedSyntax
