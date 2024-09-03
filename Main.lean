import Manual
import Manual.Meta
import VersoManual

open Verso.Genre.Manual


def main :=
  manualMain (%doc Manual)
    (config := config)
where
  config := {
    extraFiles := [("static", "static")],
    extraCss := ["/static/colors.css", "/static/theme.css", "/static/inter/inter.css", "/static/firacode/fira_code.css", "/static/katex/katex.min.css"],
    extraJs := ["/static/katex/katex.min.js", "/static/math.js"]
    emitTeX := false
    emitHtmlSingle := false
  }
