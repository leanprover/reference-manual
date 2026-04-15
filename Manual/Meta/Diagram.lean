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

block_extension Block.diagram (svg : String) (width : String) (inline : Bool) where
  data := Json.arr #[.str svg, .str width, .bool inline]
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
      let .arr #[.str svgStr, .str w, .bool inl] := data
        | HtmlT.logError "Expected three-element JSON for diagram" *> pure .empty
      let style := "width: " ++ w ++ if inl then "; display: inline-block; vertical-align: middle" else ""
      pure {{
        <div class="diagram" style={{style}}>
          {{Html.text false svgStr}}
        </div>
      }}
  usePackages := ["svg"]
  toTeX :=
    some <| fun _ _ id data _ => do
      let .arr #[.str svgStr, .str w, .bool inl] := data
        | TeX.logError "Expected three-element JSON for diagram" *> pure .empty
      let filename := s!"diagram-{id}.svg"
      IO.FS.writeFile filename svgStr
      let widthOpt := if w == "100%" then "width=\\textwidth" else s!"width={w}"
      if inl then
        pure (.raw s!"\\includesvg[{widthOpt}]\{{filename}}")
      else
        pure (.raw s!"\\begin\{center}\\includesvg[{widthOpt}]\{{filename}}\\end\{center}\n")

block_extension Block.row (alignItems : String) where
  data := Json.str alignItems
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ blockHtml _ data content => do
      let .str ai := data | HtmlT.logError "Expected string JSON for row" *> pure .empty
      let style := s!"display: flex; flex-wrap: wrap; align-items: {ai}; gap: 1em;"
      pure {{
        <div class="diagram-row" style={{style}}>
          {{← content.mapM blockHtml}}
        </div>
      }}
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM go

end BlockExtension


/--
Parses a decimal float string (e.g. `"3.14"`, `"-0.5"`).
Returns `none` for unrecognized formats.
-/
private def parseFloatStr (s : String) : Option Float :=
  let (neg, s) : Bool × String :=
    if s.startsWith "-" then (true, (s.drop 1).copy) else (false, s)
  let result : Option Float := match s.splitOn "." with
    | [intStr] =>
      intStr.toNat?.map fun n => Float.ofScientific n true 0
    | [intStr, fracStr] =>
      intStr.toNat?.bind fun n =>
        if fracStr.isEmpty then some (Float.ofScientific n true 0)
        else fracStr.toNat?.map fun frac =>
          Float.ofScientific n true 0 + Float.ofScientific frac true fracStr.length
    | _ => none
  result.map fun f => if neg then -f else f

/--
A `ValDesc` for float arguments: accepts integer numerals (e.g. `1`) and
string literals containing decimal numbers (e.g. `"0.08"`).
-/
private def floatValDesc [Monad m] [MonadError m] : ValDesc m Float where
  description := doc!"a number"
  signature := .Num ∪ .String
  get
    | .num n => pure (Float.ofScientific n.getNat true 0)
    | .str s =>
      match parseFloatStr s.getString with
      | some f => pure f
      | none => throwError "Expected a number, got {repr s.getString}"
    | .name n => throwError "Expected a number, got identifier {n.getId}"

section Config

variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

structure DiagramConfig where
  width : Option String
  scale : Option Float
  inline : Bool

def DiagramConfig.parse : ArgParse m DiagramConfig :=
  DiagramConfig.mk <$> .named' `width true <*> .named `scale floatValDesc true <*> .flag `inline false

instance : FromArgs DiagramConfig m := ⟨DiagramConfig.parse⟩

structure RowConfig where
  align : String

def RowConfig.parse : ArgParse m RowConfig :=
  RowConfig.mk <$> .namedD' `align "top"

instance : FromArgs RowConfig m := ⟨RowConfig.parse⟩

end Config

open Illuminate in
/--
Returns the viewBox width (in diagram units) of an SVG diagram, using the same
padding as `Illuminate.diagramToSvg` (padding = 5). Used to compute an em-based
CSS width when the `scale` parameter is specified. Returns 0 for empty diagrams.
-/
def diagramViewBoxWidth (d : Diagram SVG) : Float :=
  match d.getEnvelope with
  | .empty => 0
  | .nonempty env => env Vec2.west + env Vec2.east + 10

open Lean.Widget Lean.Elab.Term Lean.Meta Illuminate in
private meta unsafe def diagramExpanderUnsafe (config : DiagramConfig) (str : StrLit) :
    DocElabM Term := withoutAsync do
  if config.width.isSome && config.scale.isSome then
    throwErrorAt str "Cannot specify both 'width' and 'scale' in a diagram block"

  let altStr ← parserInputString str

  match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
  | .error e => throwErrorAt str e
  | .ok stx =>
    let (svgStr, diagramWidth) ← runWithOpenDecls <| runWithVariables fun _vars => do
      let diaTy ← Meta.mkAppM ``Illuminate.Diagram #[.const ``Illuminate.SVG []]
      let e ← Elab.Term.elabTerm stx (some diaTy)
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e

      -- Don't evaluate if elaboration produced errors
      if (← Core.getMessageLog).hasErrors then
        return ("", 0)

      -- Evaluate to get SVG string
      let svgExpr := mkApp (mkConst ``Illuminate.diagramToSvg) e
      let svgStr ← evalExpr String (mkConst ``String) svgExpr

      -- Compute diagram width from envelope if scale is needed
      let diagramWidth : Float ← if config.scale.isSome then do
        let widthExpr := mkApp (mkConst ``Manual.diagramViewBoxWidth) e
        evalExpr Float (mkConst ``Float) widthExpr
      else
        pure 0

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

      pure (svgStr, diagramWidth)

    let cssWidth : String := match config.scale with
      | none => config.width.getD "100%"
      | some scale =>
        if diagramWidth > 0 then s!"{diagramWidth * scale}em" else "100%"

    ``(Block.other (Block.diagram $(quote svgStr) $(quote cssWidth) $(quote config.inline)) #[Block.code $(quote str.getString)])

open Lean.Widget Lean.Elab.Term Lean.Meta Illuminate in
@[implemented_by diagramExpanderUnsafe]
private opaque diagramExpanderImpl (config : DiagramConfig) (str : StrLit) : DocElabM Term

@[code_block]
def diagram : CodeBlockExpanderOf DiagramConfig
  | config, str => diagramExpanderImpl config str

/-- Arranges the contained blocks in a horizontal row using flexbox. -/
@[directive]
def row : DirectiveExpanderOf RowConfig
  | config, stxs => do
    let alignItems ← match config.align with
      | "top"    => pure "flex-start"
      | "middle" => pure "center"
      | "bottom" => pure "flex-end"
      | other    => throwError "Expected 'top', 'middle', or 'bottom' for 'align', got {repr other}"
    let args ← stxs.mapM elabBlock
    ``(Block.other (Block.row $(quote alignItems)) #[ $[ $args ],* ])

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
