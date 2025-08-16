
/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Manual
import Manual.Meta
import VersoManual

open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Verso.Output.Html in
def plausible := {{
    <script defer="defer" data-domain="lean-lang.org/doc/reference/latest" src="https://plausible.io/js/script.outbound-links.js"></script>
  }}

def main :=
  manualMain (%doc Manual) (config := config)
where
  config := Config.addSearch <| Config.addKaTeX {
    extraFiles := [("static", "static")],
    extraCss := [
      "/static/colors.css",
      "/static/theme.css",
      "/static/print.css",
      "/static/fonts/source-serif/source-serif-text.css",
      "/static/fonts/source-code-pro/source-code-pro.css",
      "/static/fonts/source-sans/source-sans-3.css",
      "/static/fonts/noto-sans-mono/noto-sans-mono.css"
    ],
    extraJs := [
      -- Print stylesheet improvements
      {filename := "/static/print.js"}
    ],
    extraHead := #[plausible],
    extraContents := #[],
    emitTeX := false,
    emitHtmlSingle := true, -- for proofreading
    logo := some "/static/lean_logo.svg",
    sourceLink := some "https://github.com/leanprover-community/mathlib-manual",
    issueLink := some "https://github.com/leanprover-community/mathlib-manual/pulls",
  }
