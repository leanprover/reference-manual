/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Manual
import Manual.Meta
import VersoManual
import Manual.ExtractExamples

open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Verso.Output.Html in
def plausible := {{
    <script defer="defer" data-domain="lean-lang.org" src="https://plausible.io/js/script.outbound-links.js"></script>
  }}

open Verso.Output.Html in
def staticJs := {{
    <script src="static/metadata.js"></script>
    <script src="static/print.js"></script>
    {{ if false then -- Flip this bit to test live links locally
        {{ <script>"window.metadata = {'latest': true};"</script> }}
      else
        .empty }}
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
  manualMain (%doc Manual) (config := config) (extraSteps := [extractExamples])
where
  config := {
    extraFiles := [("static", "static")],
    extraHead := #[plausible, staticJs, staticCss],
    emitTeX := false,
    emitHtmlSingle := .no,
    logo := some "/static/lean_logo.svg",
    sourceLink := some "https://github.com/leanprover/reference-manual",
    issueLink := some "https://github.com/leanprover/reference-manual/issues",
  }
