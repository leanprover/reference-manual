/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual

import Illuminate

open Verso ArgParse Doc Elab Genre.Manual Html
open Lean Elab
open Verso.SyntaxUtils (parserInputString)
open Verso.Doc.Html (HtmlT)
open Verso.Output (Html)

open Verso.Genre.Manual.InlineLean.Scopes (getScopes runWithOpenDecls runWithVariables)

namespace Manual

section BlockExtension

block_extension Block.diagram (svg : String) (width : String) where
  data := Json.arr #[.str svg, .str width]
  extraCss := [
    r#"
.diagram svg text[font-family="text"] {
  font-family: var(--verso-text-font-family);
}
.diagram svg text[font-family="monospace"] {
  font-family: var(--verso-code-font-family);
}
"#
  ]
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[.str svgStr, .str w] := data
        | HtmlT.logError "Expected two-element JSON for diagram" *> pure .empty
      let style := "width: " ++ w
      pure {{
        <div class="diagram" style={{style}}>
          {{Html.text false svgStr}}
        </div>
      }}
  usePackages := ["svg"]
  toTeX :=
    some <| fun _ _ id data _ => do
      let .arr #[.str svgStr, .str w] := data
        | TeX.logError "Expected two-element JSON for diagram" *> pure .empty
      let filename := s!"diagram-{id}.svg"
      IO.FS.writeFile filename svgStr
      let widthOpt := if w == "100%" then "width=\\textwidth" else s!"width={w}"
      pure (.raw s!"\\begin\{center}\\includesvg[{widthOpt}]\{{filename}}\\end\{center}\n")

end BlockExtension


section Config

variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

structure DiagramConfig where
  width : String

def DiagramConfig.parse : ArgParse m DiagramConfig :=
  DiagramConfig.mk <$> .namedD' `width "100%"

instance : FromArgs DiagramConfig m := ⟨DiagramConfig.parse⟩

end Config


open Lean.Widget Lean.Elab.Term Lean.Meta Illuminate in
private meta unsafe def diagramExpanderUnsafe (config : DiagramConfig) (str : StrLit) :
    DocElabM Term := withoutAsync do
  let altStr ← parserInputString str

  match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
  | .error e => throwErrorAt str e
  | .ok stx =>
    let svgStr ← runWithOpenDecls <| runWithVariables fun _vars => do
      let diaTy ← Meta.mkAppM ``Illuminate.Diagram #[.const ``Illuminate.SVG []]
      let e ← Elab.Term.elabTerm stx (some diaTy)
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e

      -- Don't evaluate if elaboration produced errors
      if (← Core.getMessageLog).hasErrors then
        return ""

      -- Evaluate to get SVG string
      let svgExpr := mkApp (mkConst ``Illuminate.diagramToSvg) e
      let svgStr ← evalExpr String (mkConst ``String) svgExpr

      -- Store diagram for widget RPC re-evaluation
      let env ← getEnv
      let opts ← getOptions
      let id ← Illuminate.nextDiagramId.modifyGet fun n => (n, n + 1)
      let sd : Illuminate.StoredDiagram := {
        env, opts, expr := e, gadgets := #[], regions := {}, returnsDwi := false
      }
      Illuminate.diagramStore.modify (·.push (id, sd))

      -- Attach widget with CSS variable defaults for the infoview context
      let widgetSvg := "<div style=\"--verso-text-font-family: sans-serif; --verso-code-font-family: monospace;\">" ++
        "<style>svg text[font-family=\"text\"] { font-family: var(--verso-text-font-family); } " ++
        "svg text[font-family=\"monospace\"] { font-family: var(--verso-code-font-family); }</style>" ++
        svgStr ++ "</div>"
      let props : Json := .mkObj [
        ("exprId", toJson id),
        ("initialSvg", .str widgetSvg),
        ("parameters", .arr #[])]
      savePanelWidgetInfo Illuminate.diagramWidget.javascriptHash.val (pure props) str

      pure svgStr

    ``(Block.other (Block.diagram $(quote svgStr) $(quote config.width)) #[Block.code $(quote str.getString)])

open Lean.Widget Lean.Elab.Term Lean.Meta Illuminate in
@[implemented_by diagramExpanderUnsafe]
private opaque diagramExpanderImpl (config : DiagramConfig) (str : StrLit) : DocElabM Term

@[code_block]
def diagram : CodeBlockExpanderOf DiagramConfig
  | config, str => diagramExpanderImpl config str

namespace Diagram
open Illuminate

private def braceDepth : Float := 12
private def braceGap : Float := 4
private def monoStyle : TextStyle := { fontSize := 10, fontFamily := "monospace" }
def fieldLabelStyle : TextStyle := { fontSize := 10, fontFamily := "sans-serif" }
def txt (s : String) : Diagram SVG :=
  Diagram.text s fieldLabelStyle
def twoLine (description typeLine : String) : Diagram SVG :=
  .styledText (base := fieldLabelStyle) <| description ++ "\n" ++ family "monospace" typeLine

def field (name : Lean.Name) (label : String) (w : Float) : Diagram SVG :=
  Diagram.atop
    (.text label monoStyle)
    ((Diagram.rect w 28 (fill := Color.white) (name := name)).padRight (-0.5) |>.padLeft (-0.5))

def fieldWithBrace (name : Lean.Name) (label : String) (w : Float)
    (braceDepth braceGap : Float) (braceLabel : Diagram SVG) : Diagram SVG :=
  let box := field name label w
  let brace := Diagram.curlyBrace (w - 8) (depth := braceDepth) (label := some braceLabel) (angle := 3 * pi / 2)
  let braceEnv := brace.getEnvelope
  let excess := braceEnv[Vec2.east] - w / 2
  let brace := if excess > 0 then brace |>.padLeft (-excess) |>.padRight (-excess) else brace
  Diagram.vsep braceGap [box, brace]

inductive LayoutType where
  | header
  | object
  | size_t
  | data (width : Option Float)

def LayoutType.width : LayoutType → Float
  | .header | .object => 90
  | .size_t => 70
  | .data none => 180
  | .data (some w) => w

def layoutDiagram (fields : List (String × LayoutType × Option (Diagram SVG))) : Diagram SVG :=
  .hcat (align := .top) <| fields.map fun (lbl, t, braceLabel) =>
    let name := Name.str .anonymous lbl
    match braceLabel with
    | none => field name lbl t.width
    | some u => fieldWithBrace name lbl t.width braceDepth braceGap u
