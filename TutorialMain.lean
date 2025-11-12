/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoTutorial
import Tutorial

open Verso.Genre.Manual
open Verso.Genre.Tutorial

open Verso.Output.Html in
def plausible := {{
    <script defer="defer" data-domain="lean-lang.org" src="https://plausible.io/js/script.outbound-links.js"></script>
  }}

open Verso.Output.Html in
def staticJs := {{
    <script src="static/metadata.js"></script>
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

open Verso.Doc Concrete in
def tutorials : Tutorials where
  content :=
  (verso (.none) "foo"
   :::::::
   abc
   :::::::).toPart

  topics := #[
    { title := "Tactics"
      description := #[blocks!"..."]
      tutorials := #[%doc Tutorial.VCGen, %doc Tutorial.Grind.IndexMap]
    }

  ]

def main :=
  tutorialsMain tutorials (config := {remoteConfigFile := "tutorial-remotes.json", destination := "_tutorial-out"})
