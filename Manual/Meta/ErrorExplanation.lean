/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import VersoManual
import Manual.Meta
import Manual.Meta.ErrorExplanation.Example
import Manual.Meta.ErrorExplanation.Header

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
    | .text _ txt => txt
    | .seq elts => elts.foldl (· ++ htmlText ·) ""
    | .tag _nm _attrs children => htmlText children


