/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta.Figure
import Manual.Meta.Lean
import Lean.Elab.InfoTree.Types

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab

namespace Manual

def Block.example (name : Option String) : Block where
  name := `Manual.example
  data := ToJson.toJson (name, (none : Option Tag))

structure ExampleConfig where
  description : FileMap × Array Syntax
  /-- Name for refs -/
  name : Option String := none
  keep : Bool := false


def ExampleConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m ExampleConfig :=
  ExampleConfig.mk <$> .positional `description .inlinesString <*> .named `name .string true <*> (.named `keep .bool true <&> (·.getD false))

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

def isLeanBlock : Syntax → CoreM Bool
  | `(block|```$nameStx:ident $_args*|$_contents:str```) => do
    let name ← realizeGlobalConstNoOverloadWithInfo nameStx
    return name == ``lean
  | _ => pure false


@[directive_expander «example»]
def «example» : DirectiveExpander
  | args, contents => do
    let cfg ← ExampleConfig.parse.run args

    let description ←
      DocElabM.withFileMap cfg.description.1 <|
      cfg.description.2.mapM elabInline
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
    pure #[← ``(Block.other (Block.example $(quote cfg.name)) #[Block.para #[$description,*], $blocks,*])]

@[block_extension «example»]
def example.descr : BlockDescr where
  traverse id data contents := do
    match FromJson.fromJson? data (α := Option String × Option Tag) with
    | .error e => logError s!"Error deserializing example tag: {e}"; pure none
    | .ok (none, _) => pure none
    | .ok (some x, none) =>
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.example none with id := some id, data := toJson (some x, some tag)} contents
    | .ok (some _, some _) => pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun goI goB id _data blocks => do
      if h : blocks.size < 1 then
        HtmlT.logError "Malformed example"
        pure .empty
      else
        let .para description := blocks[0]
          | HtmlT.logError "Malformed example - description not paragraph"; pure .empty
        let xref ← HtmlT.state
        let attrs := xref.htmlId id
        pure {{
          <details class="example" {{attrs}}>
            <summary class="description">{{← description.mapM goI}}</summary>
            {{← blocks.extract 1 blocks.size |>.mapM goB}}
          </details>
        }}
  extraCss := [
r#".example {
  padding: 1.5em;
  border: 1px solid #98B2C0;
  border-radius: 0.5em;
  margin-bottom: 0.75em;
  margin-top: 0.75em;
  clear: both; /* Don't overlap margin notes with examples */
}
.example p:last-child {margin-bottom:0;}
.example .description::before {
  content: "Example: ";
}
.example[open] .description {
  margin-bottom: 1em;
}
.example .description {
  font-style: italic;
  font-family: var(--verso-structure-font-family);
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
