/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import VersoManual

import Manual.Meta

import Lean.ErrorExplanations


open Verso (ArgParse)
open Verso.ArgParse (parseThe)
open Verso.Doc Elab
open Verso.Genre.Manual Markdown InlineLean
open SubVerso.Highlighting
open scoped Lean.Doc.Syntax
open Lean Elab
example := Quote


set_option pp.rawOnError true
set_option guard_msgs.diff true

namespace Manual


register_option manual.requireErrorExplanations : Bool := {
  defValue := true,
  descr := "Whether to fail or warn when error explanations don't match. Must be `true` for releases."
}

open Verso.Output Html in
/-
A block used to render error messages that don't match what they're expected to (rather than falling
back to a placeholder message). These need to be fixed upstream.
-/
block_extension Block.errorFallback (messageString : String) where
  data := .str messageString
  traverse _ _ _ := return none
  toHtml := some fun _goI _goB _id data _contents => do
    let .str messageString := data
      | HtmlT.logError "Failed to deserialize fallback message"
        return .empty
    return {{
      <pre class="lean-output error"><span class="verso-message">{{messageString}}</span></pre>
    }}
  toTeX := none

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
    println! name
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
  levels : Markdown.HeaderMapping := default
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
    | .normal str => str.trimAscii.copy == "Examples"
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
  let titleString := inlinesToString (← getEnv) title
  let codeBlocks := codeBlocks.map Prod.fst
  let codeExample ←
    ``(Block.other (Block.tabbedMWEs $(quote titles)) #[$codeBlocks,*])
  ``(Block.other (Block.example $(quote titleString) none (opened := true))
      #[Block.para #[$title,*], $codeExample, $descrBlocks,*])

private def titleOfCodeBlock? (b : MD4Lean.Block) : Option String := do
  let info ← infoOfCodeBlock b |>.toOption
  info.title?

/-- Execute `x` until it returns `none`. -/
partial def repeatedly (x : ExplanElabM (Option α)) : ExplanElabM (Array α) :=
  go x #[]
where
  go x acc := do
    if let some result := (← x) then
      go x (acc.push result)
    else
      return acc

deriving instance Quote for ErrorExplanation.Metadata

block_extension Block.errorExplanationMetadata (metadata : ErrorExplanation.Metadata) where
  data := toJson metadata
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := ["
  .error-explanation-metadata {
    margin-bottom: 2rem; /* Double the paragraph margin */
  }

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
      </div>
    }}

/-- Adds the specified explanation metadata to the document. -/
def addExplanationMetadata (metadata : ErrorExplanation.Metadata) : PartElabM Unit := do
  PartElabM.addBlock (← ``(Block.other (Block.errorExplanationMetadata $(quote metadata)) #[]))

/-- Adds the metadata and body of the explanation with name `name` to the document. -/
def addExplanationBlocksFor (name : Name) : PartElabM Unit := do
  let explan? ← getErrorExplanation? name
  match explan? with
  | .none =>
    throwError m!"Adding explanation blocks failed: Could not find explanation for {name}"
  | some explan =>
    try
      -- let some ast := MD4Lean.parse explan.doc
      --   | throwErrorAt (← getRef) "Failed to parse docstring as Markdown"
      addExplanationMetadata explan.metadata
      -- let (_, { levels, .. }) ← addExplanationBodyBlocks.run name explan.metadata.severity ast.blocks
      -- closeEnclosingSections levels
    catch
      | .error ref msg => throw <| .error ref m!"Failed to process explanation for {name}: {msg}"
      | e => throw e

def errorExplanationDomain := `Manual.errorExplanation

open Verso.Search in
def errorExplanationDomainMapper :=
  DomainMapper.withDefaultJs errorExplanationDomain "Error Explanation" "error-explanation-domain"
    |>.setFont { family := .code }

inline_extension Inline.errorExplanation (errorName : Name) (summary : String) where
  data := toJson #[errorName.toString, summary]

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
    signature := .Ident
    get := fun
      | .name x => pure x
      | other => throwError "Expected error name, got {repr other}"
  }

/-- Renders the error explanation for `name` via `{explanation name}`. -/
@[part_command Lean.Doc.Syntax.command]
def explanation : PartCommand
  | `(block|command{explanation $args*}) => do
    let config ← ExplanationConfig.parser.run (← parseArgs args)
    addExplanationBlocksFor config.name.getId
  | _ => Lean.Elab.throwUnsupportedSyntax

/--
Returns the suffix of `name` as a string containing soft-hyphen characters at reasonable split points.
-/
def getBreakableSuffix (name : Name) : Option String := do
  let suffix ← match name with
    | .str _ s => s
    | .num _ n => toString n
    | .anonymous => none
  let breakableHtml := softHyphenateText false suffix
  htmlText breakableHtml
where
  htmlText : Verso.Output.Html → String
    | .text _ txt => txt
    | .seq elts => elts.foldl (· ++ htmlText ·) ""
    | .tag _nm _attrs children => htmlText children


@[part_command Lean.Doc.Syntax.command]
def include_explanation : PartCommand
  | `(block|command{include_explanation $args* }) => do
    match ← parseArgs args with
    | #[.anon (.name errorId), .anon (.name moduleId)] =>
      let errorName := errorId.getId
      let errorExplanationModuleName := docName moduleId.getId
      let errorExplanation ← realizeGlobalConstNoOverloadWithInfo (mkIdentFrom moduleId errorExplanationModuleName)

      let .some _ ← getErrorExplanation? errorName
        | logWarningAt errorId m!"The name {errorId} is not a known error"
      modifyEnv (Manual.errorExplanationsAdded.modifyState · (·.insert errorName))

      PartElabM.closePartsUntil 0 (← getRef).getHeadInfo.getPos!
      PartElabM.addPart <| .included (mkIdentFrom moduleId errorExplanation)


    | _ => throwError "Expected two arguments: an error explanation identifier name (e.g. `lean.inductiveParamMissing`) and a module name (e.g. `Manual.ErrorExplanations.InductiveParamMissing`)"

  | _ => throwUnsupportedSyntax
where
 resolved id := mkIdentFrom id <$> realizeGlobalConstNoOverloadWithInfo (mkIdentFrom id (docName id.getId))

open Verso.Doc.Elab in
open Lean in
/-- Renders all error explanations as parts of the current page. -/
@[part_command Lean.Doc.Syntax.command]
def make_explanations : PartCommand
  | `(block|command{make_explanations}) => do
    let explans ← getErrorExplanationsSorted
    for (errorName, explan) in explans do
      let false := Manual.errorExplanationsAdded.getState (← getEnv) |>.contains errorName
        | logInfo m!"Skipping {errorName}"
      let titleString := errorName.toString
      let titleBits := #[← ``(Inline.other
        (Inline.errorExplanation $(quote errorName) $(quote explan.metadata.summary))
        #[Inline.text "About: ", Inline.code $(quote titleString)])]
      let some shortTitleString := getBreakableSuffix errorName
        | throwError m!"Found invalid explanation name `{errorName}` when generating explanations section"
      PartElabM.push {
        titleSyntax := quote (k := `str) s!"About..: {titleString}",
        expandedTitle := some (titleString, titleBits),
        metadata := some (← `({ shortTitle := $(quote shortTitleString) })),
        blocks := #[],
        priorParts := #[]
      }
      addExplanationBlocksFor errorName
      closeEnclosingSection
  | _ => throwUnsupportedSyntax
