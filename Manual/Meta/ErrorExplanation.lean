/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

module
import VersoManual.Html.SoftHyphenate
public import Manual.Meta.ErrorExplanation.Example
public import Manual.Meta.ErrorExplanation.Header

public section

open Lean
open Verso.Doc
open Verso.Genre.Manual
open Elab

namespace Manual

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
    | .text txt | .raw txt => txt
    | .seq elts => elts.foldl (· ++ htmlText ·) ""
    | .element _nm _attrs children => htmlText children
