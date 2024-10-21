/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Manual
import Manual.Meta
import VersoManual

open Verso.Genre.Manual


def main :=
  manualMain (%doc Manual) (config := config)
where
  config := {
    extraFiles := [("static", "static")],
    extraCss := ["/static/colors.css", "/static/theme.css", "/static/print.css", "/static/fonts/source-serif/source-serif-text.css", "/static/fonts/source-code-pro/source-code-pro.css", "/static/katex/katex.min.css"],
    extraJs := ["/static/katex/katex.min.js", "/static/math.js", "/static/print.js"],
    emitTeX := false,
    emitHtmlSingle := true, -- for proofreading
    logo := some "/static/lean_logo.svg"
  }
