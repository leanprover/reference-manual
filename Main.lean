/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Manual
import Manual.Meta
import VersoManual

open Verso.Genre.Manual

open Verso.Output.Html in
def searchModule := {{
    <script type="module" src="/static/search/search-init.js"></script>
  }}


def main :=
  manualMain (%doc Manual) (config := config)
where
  config := {
    extraFiles := [("static", "static")],
    extraCss := [
      "/static/colors.css",
      "/static/theme.css",
      "/static/print.css",
      "/static/search/search-box.css",
      "/static/fonts/source-serif/source-serif-text.css",
      "/static/fonts/source-code-pro/source-code-pro.css",
      "/static/katex/katex.min.css"
    ],
    extraJs := [
      -- Search box
      "/static/search/fuzzysort.js",
      -- KaTeX
      "/static/katex/katex.min.js",
      "/static/math.js",
      -- Print stylesheet improvements
      "/static/print.js"
    ],
    extraHead := #[searchModule],
    emitTeX := false,
    emitHtmlSingle := true, -- for proofreading
    logo := some "/static/lean_logo.svg",
    sourceLink := some "https://github.com/leanprover/reference-manual",
    issueLink := some "https://github.com/leanprover/reference-manual/issues"
  }
