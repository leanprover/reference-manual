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
