/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta.Figure
import Manual.Meta.LzCompress
import Lean.Elab.InfoTree.Types

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Lean.Doc.Syntax

open Lean Elab

namespace Manual

def Block.example (descriptionString : String) (name : Option String) (opened : Bool) (liveText : Option String := none) : Block where
  -- FIXME: This should be a double-backtickable name
  name := `Manual.example
  data := ToJson.toJson (descriptionString, name, opened, (none : Option Tag), liveText)
  properties := .empty |>.insert `Verso.Genre.Manual.exampleDefContext descriptionString

/-- The type of the Json stored with Block.example -/
abbrev ExampleBlockJson := String × Option String × Bool × Option Tag × Option String

structure ExampleConfig where
  description : FileMap × TSyntaxArray `inline
  /-- Name for refs -/
  tag : Option String := none
  keep : Bool := false
  opened : Bool := false


section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m]

def ExampleConfig.parse  : ArgParse m ExampleConfig :=
  ExampleConfig.mk <$> .positional `description .inlinesString
                   <*> .named `tag .string true
                   <*> (.named `keep .bool true <&> (·.getD false))
                   <*> (.named `open .bool true <&> (·.getD false))

instance : FromArgs ExampleConfig m where
  fromArgs := ExampleConfig.parse
end

def prioritizedElab [Monad m] (prioritize : α → m Bool) (act : α  → m β) (xs : Array α) : m (Array β) := do
  let mut out := #[]
  let mut later := #[]
  for h:i in [0:xs.size] do
    let x := xs[i]
    if ← prioritize x then
      out := out.push (i, (← act x))
    else later := later.push (i, x)
  for (i, x) in later do
    out := out.push (i, (← act x))
  out := out.qsort (fun (i, _) (j, _) => i < j)
  return out.map (·.2)

def isLeanBlock : TSyntax `block → CoreM Bool
  | `(block|```$nameStx:ident $_args*|$_contents:str```) => do
    let name ← realizeGlobalConstNoOverload nameStx
    return name == ``Verso.Genre.Manual.InlineLean.lean
  | _ => pure false

structure LeanBlockContent where
  content : Option String
  shouldElab : Bool

def getLeanBlockContents? : TSyntax `block → DocElabM (LeanBlockContent)
  | `(block|```$nameStx:ident $args*|$contents:str```) => do
    let name ← realizeGlobalConstNoOverload nameStx
    if name == ``Manual.imports then
      return { content := some contents.getString, shouldElab := false }
    if name != ``Verso.Genre.Manual.InlineLean.lean then
      return { content := none, shouldElab := false }
    let args ← Verso.Doc.Elab.parseArgs args
    let args ← parseThe InlineLean.LeanBlockConfig args
    if !args.keep || args.error then
      return { content := none, shouldElab := true }
    pure <| { content := some contents.getString, shouldElab := true }
  | _ => pure { content := none, shouldElab := false }

/--
Elaborates all Lean blocks first, enabling local forward references
-/
@[directive_expander leanFirst]
def leanFirst : DirectiveExpander
  | args, contents => do
    let () ← ArgParse.done.run args

    -- Elaborate Lean blocks first, so inlines in prior blocks can refer to them
    prioritizedElab (isLeanBlock ·) elabBlock contents

/-- Turn a list of lean blocks into one string with the appropriate amount of whitespace -/
def renderExampleContent (exampleBlocks : List String) : String :=
  "\n\n".intercalate <| exampleBlocks.map (·.trim)

/-- info: "a\n\nb\n\nc" -/
#guard_msgs in
#eval renderExampleContent ["\n  \na\n", "\n b", "c  "]

/-- A domain for named examples -/
def examples : Domain := {}

@[directive_expander «example»]
def «example» : DirectiveExpander
  | args, contents => do
    let cfg ← parseThe ExampleConfig args

    let description ←
      DocElabM.withFileMap cfg.description.1 <|
      cfg.description.2.mapM elabInline
    let descriptionString := inlinesToString (← getEnv) cfg.description.2
    PointOfInterest.save (← getRef) (inlinesToString (← getEnv) cfg.description.2)
      (selectionRange := mkNullNode cfg.description.2)
      (kind := Lsp.SymbolKind.interface)
      (detail? := some "Example")

    let accumulate (b : TSyntax `block) : StateT (List String) DocElabM Bool := do
      let {content, shouldElab} ← getLeanBlockContents? b
      if let some x := content then
        modify (· ++ [x])
      pure shouldElab

    -- Elaborate Lean blocks first, so inlines in prior blocks can refer to them
    -- Also accumulate text of lean blocks.
    let exampleCode := prioritizedElab accumulate (elabBlock ·) contents
      |>.run []
    let (blocks, acc) ←
      if cfg.keep then exampleCode
      else withoutModifyingEnv <| exampleCode
    let liveLinkContent := if acc = [] then none else some (renderExampleContent acc)
    -- Examples are represented using the first block to hold the description. Storing it in the JSON
    -- entails repeated (de)serialization.
    pure #[← ``(Block.other (Block.example $(quote descriptionString) $(quote cfg.tag) (opened := $(quote cfg.opened)) $(quote liveLinkContent))
                #[Block.para #[$description,*], $blocks,*])]

@[block_extension «example»]
def example.descr : BlockDescr where
  traverse id data contents := do
    match FromJson.fromJson? data (α := ExampleBlockJson) with
    | .error e => logError s!"Error deserializing example tag: {e}"; pure none
    | .ok (descrString, none, _, _, _) => do
      modify (·.saveDomainObject ``examples descrString id)
      pure none
    | .ok (descrString, some x, opened, none, liveText) =>
      modify (·.saveDomainObject ``examples descrString id)
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.example descrString none false liveText with
        id := some id,
        data := toJson (some x, opened, some tag)} contents -- Is this line reachable?
    | .ok (descrString, some _, _, some _, liveText) =>
      modify (·.saveDomainObject ``examples descrString id)
      pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun goI goB id data blocks => do
      if h : blocks.size < 1 then
        HtmlT.logError "Malformed example"
        pure .empty
      else
        let .para description := blocks[0]
          | HtmlT.logError "Malformed example - description not paragraph"; pure .empty
        let (descrString, opened, liveText) ←
          match FromJson.fromJson? data (α := ExampleBlockJson) with
          | .error e => HtmlT.logError s!"Error deserializing example data {data}: {e}"; pure ("", false, none)
          | .ok (descrString, _, opened, _, liveText) => pure (descrString, opened, liveText)
        let xref ← HtmlT.state
        let ctxt ← HtmlT.context
        let mut attrs := xref.htmlId id
        if opened then
          attrs := attrs.push ("open", "")
        withReader (fun ρ => { ρ with definitionIds := xref.definitionIds ctxt, codeOptions.definitionsAsTargets := true}) do
          let liveLink := match liveText with
          | .none => Output.Html.empty
          | .some content =>
            let href := s!"javascript:openLiveLink(\"{lzCompress content}\")"
            -- This link is `display: none` hidden by default, and enabled by maybeShowLiveLinks,
            -- assuming we detect that we're a sufficiently recent version of the manual
            -- to be compatible with the versions served by https://live.lean-lang.org
            {{ <div class="live-link"><a href={{href}}>"Live ↪"</a></div> }}
          pure {{
            <details class="example" {{attrs}}>
              <summary class="description">{{← description.mapM goI}}</summary>
              <div class="example-content">
                {{← blocks.extract 1 blocks.size |>.mapM goB}}
                  {{liveLink}}
              </div>
            </details>
          }}
  extraJs := [
r#"function openDetailsForHashTarget() {
  // Get the current hash from the URL
  const hash = window.location.hash;

  // Exit early if no hash is present
  if (!hash) return;

  // Remove the # to get the actual ID
  const targetId = hash.substring(1);

  // Find the target element
  const targetElement = document.getElementById(targetId);

  // Exit if target element doesn't exist
  if (!targetElement) return;

  // Find the closest details element that contains the target
  const detailsElement = targetElement.closest('details');

  // If the target is inside a details element, open it
  if (detailsElement) {
    detailsElement.open = true;
  }
}

function liveLinkUrlOfCodez(codez) {
  if (window.metadata !== undefined && window.metadata.stable) {
    return "https://live.lean-lang.org/#project=mathlib-stable&codez=" + codez;
  }
  if (window.metadata !== undefined && window.metadata.latest) {
    return "https://live.lean-lang.org/#codez=" + codez;
  }
  return undefined;
}

function maybeShowLiveLinks() {
  if (liveLinkUrlOfCodez('') !== undefined) {
    const style = document.createElement('style');
    style.textContent = `.live-link { display: initial !important; }`;
    document.head.appendChild(style);
  }
}

function openLiveLink(codez) {
  const url = liveLinkUrlOfCodez(codez);
  if (url !== undefined) {
    window.open(url, '_blank')
  }
  else {
    // This case shouldn't be possible, because maybeShowLiveLinks returns undefined,
    // then maybeShowLiveLinks wouldn't have ever shown the links in the first place.
    // Just in case, throw up a dialog.
    alert("Don't know which version of live to use. Please report this at https://github.com/leanprover/reference-manual/issues");
  }
}

function pageInit() {
  openDetailsForHashTarget();
  maybeShowLiveLinks();
}

// Run the function when the page loads
document.addEventListener('DOMContentLoaded', pageInit);

// Also run when the hash changes (for single-page applications)
window.addEventListener('hashchange', pageInit);

// Run immediately in case the script loads after DOMContentLoaded
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', pageInit);
} else {
  pageInit();
}
"#
  ]
  extraCss := [
r#".example {
  border: 1px solid #98B2C0;
  border-radius: 0.5rem;
  margin-bottom: var(--verso--box-vertical-margin);
  margin-top: var(--verso--box-vertical-margin);
}
/* 1400 px is the cutoff for when the margin notes move out of the margin and into floated elements. */
@media screen and (700px < width <= 1400px) {
  .example {
    clear: both; /* Don't overlap margin notes with examples */
  }
}
.example .description::before {
  content: "Example: ";
}
.example .description {
  font-style: italic;
  font-family: var(--verso-structure-font-family);
  padding: var(--verso--box-padding);
}
.example[open] .description {
  margin-bottom: 0;
}
.example-content {
  padding: 0 var(--verso--box-padding) var(--verso--box-padding);
  position: relative;
}
.example-content > :first-child {
  margin-top: 0;
}
.example-content p:last-child {
  margin-bottom:0;
}
.example .hl.lean.block {
  overflow-x: auto;
}
.live-link {
  font-family: var(--verso-structure-font-family);
  position: absolute;
  bottom: 0px;
  right: 0px;
  padding: 0.5rem;
  border-top: 1px solid #98B2C0;
  border-left: 1px solid #98B2C0;
  border-top-left-radius: 0.5rem;
  display: none; /* default to not showing */
}
.live-link a {
  text-decoration: none;
  color: var(--lean-blue);
}
"#
  ]


def Block.keepEnv : Block where
  name := `Manual.example

-- TODO rename to `withoutModifyingEnv` or something more clear
@[directive_expander keepEnv]
def keepEnv : DirectiveExpander
  | args, contents => do
    let () ← ArgParse.done.run args
    PointOfInterest.save (← getRef) "keepEnv" (kind := .package)
    withoutModifyingEnv <| withSaveInfoContext <| contents.mapM elabBlock


@[block_extension keepEnv]
def keepEnv.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun _ goB _ _ blocks => do
      blocks.mapM goB
