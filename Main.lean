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
    <script defer="defer" data-domain="lean-lang.org" src="https://plausible.io/js/script.outbound-links.js"></script>
  }}

open Verso.Output.Html in
def staticJs := {{
    <script src="static/print.js"></script>
  }}

open Verso.Output.Html in
def staticCss := {{
    <link rel="stylesheet" href="static/colors.css" />
    <link rel="stylesheet" href="static/theme.css" />
    <link rel="stylesheet" href="static/print.css" />
    <link rel="stylesheet" href="static/fonts/source-serif/source-serif-text.css" />
    <link rel="stylesheet" href="static/fonts/source-code-pro/source-code-pro.css" />
    <link rel="stylesheet" href="static/fonts/source-sans/source-sans-3.css" />
    <link rel="stylesheet" href="static/fonts/noto-sans-mono/noto-sans-mono.css" />
  }}

def main :=
  manualMain (%doc Manual) (config := config)
where
  config := Config.addSearch <| Config.addKaTeX {
    extraFiles := [("static", "static")],
    extraHead := #[plausible, staticJs, staticCss],
    emitTeX := false,
    emitHtmlSingle := true, -- for proofreading
    logo := some "/static/lean_logo.svg",
    sourceLink := some "https://github.com/leanprover/reference-manual",
    issueLink := some "https://github.com/leanprover/reference-manual/issues",
  }
