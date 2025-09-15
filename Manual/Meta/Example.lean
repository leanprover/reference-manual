/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta.Figure
import Lean.Elab.InfoTree.Types

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Lean.Doc.Syntax

open Lean Elab

namespace Manual

def Block.example (descriptionString : String) (name : Option String) (opened : Bool) : Block where
  name := `Manual.example
  data := ToJson.toJson (descriptionString, name, opened, (none : Option Tag))
  properties := .empty |>.insert `Verso.Genre.Manual.exampleDefContext descriptionString

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
    let name ← realizeGlobalConstNoOverloadWithInfo nameStx
    return name == ``Verso.Genre.Manual.InlineLean.lean
  | _ => pure false

/--
Elaborates all Lean blocks first, enabling local forward references
-/
@[directive_expander leanFirst]
def leanFirst : DirectiveExpander
  | args, contents => do
    let () ← ArgParse.done.run args

    -- Elaborate Lean blocks first, so inlines in prior blocks can refer to them
    prioritizedElab (isLeanBlock ·) elabBlock contents

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
    -- Elaborate Lean blocks first, so inlines in prior blocks can refer to them
    let blocks ←
      if cfg.keep then
        prioritizedElab (isLeanBlock ·) elabBlock contents
      else
        withoutModifyingEnv <| prioritizedElab (isLeanBlock ·) elabBlock contents
    -- Examples are represented using the first block to hold the description. Storing it in the JSON
    -- entails repeated (de)serialization.
    pure #[← ``(Block.other (Block.example $(quote descriptionString) $(quote cfg.tag) (opened := $(quote cfg.opened)))
                #[Block.para #[$description,*], $blocks,*])]

@[block_extension «example»]
def example.descr : BlockDescr where
  traverse id data contents := do
    match FromJson.fromJson? data (α := String × Option String × Bool × Option Tag) with
    | .error e => logError s!"Error deserializing example tag: {e}"; pure none
    | .ok (descrString, none, _, _) => do
      modify (·.saveDomainObject ``examples descrString id)
      pure none
    | .ok (descrString, some x, opened, none) =>
      modify (·.saveDomainObject ``examples descrString id)
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.example descrString none false with id := some id, data := toJson (some x, opened, some tag)} contents
    | .ok (descrString, some _, _, some _) =>
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
        let (descrString, opened) ←
          match FromJson.fromJson? data (α := String × Option String × Bool × Option Tag) with
          | .error e => HtmlT.logError s!"Error deserializing example data: {e}"; pure ("", false)
          | .ok (descrString, _, opened, _) => pure (descrString, opened)
        let xref ← HtmlT.state
        let ctxt ← HtmlT.context
        let mut attrs := xref.htmlId id
        if opened then
          attrs := attrs.push ("open", "")
        withReader (fun ρ => { ρ with definitionIds := xref.definitionIds ctxt, codeOptions.definitionsAsTargets := true}) do
          pure {{
            <details class="example" {{attrs}}>
              <summary class="description">{{← description.mapM goI}}</summary>
              <div class="example-content">
                {{← blocks.extract 1 blocks.size |>.mapM goB}}
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

// Run the function when the page loads
document.addEventListener('DOMContentLoaded', openDetailsForHashTarget);

// Also run when the hash changes (for single-page applications)
window.addEventListener('hashchange', openDetailsForHashTarget);

// Run immediately in case the script loads after DOMContentLoaded
if (document.readyState === 'loading') {
  document.addEventListener('DOMContentLoaded', openDetailsForHashTarget);
} else {
  openDetailsForHashTarget();
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
