/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Lean.Elab.InfoTree.Types

import Manual.Meta.Basic

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab



namespace Manual

def Block.figure (name : Option String) : Block where
  name := `Manual.figure
  data := ToJson.toJson (name, (none : Option Tag))

structure FigureConfig where
  caption : FileMap × Array Syntax
  /-- Name for refs -/
  name : Option String := none


def FigureConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `caption .inlinesString <*> .named `name .string true

@[directive_expander figure]
def figure : DirectiveExpander
  | args, contents => do
    let cfg ← FigureConfig.parse.run args

    PointOfInterest.save (← getRef) (inlinesToString (← getEnv) cfg.caption.2)
      (selectionRange := mkNullNode cfg.caption.2)
      (kind := Lsp.SymbolKind.interface)
      (detail? := some "Figure")

    let caption ← DocElabM.withFileMap cfg.caption.1 <|
      (cfg.caption.2.map (⟨·⟩)).mapM elabInline
    let blocks ← contents.mapM elabBlock
    -- Figures are represented using the first block to hold the caption. Storing it in the JSON
    -- entails repeated (de)serialization.
    pure #[← ``(Block.other (Block.figure $(quote cfg.name)) #[Block.para #[$caption,*], $blocks,*])]

@[block_extension figure]
def figure.descr : BlockDescr where
  traverse id data contents := do
    match FromJson.fromJson? data (α := Option String × Option Tag) with
    | .error e => logError s!"Error deserializing figure tag: {e}"; pure none
    | .ok (none, _) => pure none
    | .ok (some x, none) =>
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.figure none with id := some id, data := toJson (some x, some tag)} contents
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
        HtmlT.logError "Malformed figure"
        pure .empty
      else
        let .para caption := blocks[0]
          | HtmlT.logError "Malformed figure - caption not paragraph"; pure .empty
        let xref ← HtmlT.state
        let attrs := xref.htmlId id
        pure {{
          <figure {{attrs}}>
            {{← blocks.extract 1 blocks.size |>.mapM goB}}
            <figcaption>{{← caption.mapM goI}}</figcaption>
          </figure>
        }}
