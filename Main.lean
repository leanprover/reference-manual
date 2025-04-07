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
def searchModule := {{
    <script type="module" src="/static/search/search-init.js"></script>
  }}


def KaTeXLicense : LicenseInfo where
  identifier := "MIT"
  dependency := "KaTeX"
  howUsed := "KaTeX is used to render mathematical notation."
  link := "https://katex.org/"
  text := #[(some "The MIT License", text)]
where
  text := r#"
Copyright (c) 2013-2020 Khan Academy and other contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"#


def addKaTeX (config : Config) : Config :=
  {config with
    extraCss := "/static/katex/katex.min.css" :: config.extraCss,
    extraJs := "/static/katex/katex.min.js" :: "/static/math.js" :: config.extraJs,
    licenseInfo := KaTeXLicense :: config.licenseInfo
  }


def fuzzysortLicense : LicenseInfo where
  identifier := "MIT"
  dependency := "fuzzysort v3.1.0"
  howUsed := "The fuzzysort library is used in the search box to quickly filter results."
  link := "https://github.com/farzher/fuzzysort"
  text := #[(some "The MIT License", text)]
where
  text := r#"
Copyright (c) 2018 Stephen Kamenar

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"#

def w3ComboboxLicense : LicenseInfo where
  identifier := "W3C-20150513"
  dependency := "Editable Combobox With Both List and Inline Autocomplete Example, from the W3C's ARIA Authoring Practices Guide (APG)"
  howUsed := "The search box component includes code derived from the example code in the linked article from the W3C's ARIA Authoring Practices Guide (APG)."
  link := "https://www.w3.org/WAI/ARIA/apg/patterns/combobox/examples/combobox-autocomplete-both/"
  text := #[(some "Software and Document License - 2023 Version", text)]
where
  text := r#"Permission to copy, modify, and distribute this work, with or without
modification, for any purpose and without fee or royalty is hereby granted,
provided that you include the following on ALL copies of the work or portions
thereof, including modifications:

 * The full text of this NOTICE in a location viewable to users of the redistributed or derivative work.

 * Any pre-existing intellectual property disclaimers, notices, or terms and conditions. If none exist, the W3C software and document short notice should be included.

 * Notice of any changes or modifications, through a copyright statement on the new code or document such as "This software or document includes material copied from or derived from "Editable Combobox With Both List and Inline Autocomplete Example" at https://www.w3.org/WAI/ARIA/apg/patterns/combobox/examples/combobox-autocomplete-both/. Copyright © 2024 World Wide Web Consortium. https://www.w3.org/copyright/software-license-2023/"


"#

def main :=
  manualMain (%doc Manual) (config := config)
where
  config := addKaTeX {
    extraFiles := [("static", "static")],
    extraCss := [
      "/static/colors.css",
      "/static/theme.css",
      "/static/print.css",
      "/static/search/search-box.css",
      "/static/fonts/source-serif/source-serif-text.css",
      "/static/fonts/source-code-pro/source-code-pro.css",
      "/static/fonts/source-sans/source-sans-3.css",
    ],
    extraJs := [
      -- Search box
      "/static/search/fuzzysort.js",
      -- Print stylesheet improvements
      "/static/print.js"
    ],
    extraHead := #[searchModule],
    emitTeX := false,
    emitHtmlSingle := true, -- for proofreading
    logo := some "/static/lean_logo.svg",
    sourceLink := some "https://github.com/leanprover/reference-manual",
    issueLink := some "https://github.com/leanprover/reference-manual/issues"
    -- Licenses for the search box
    licenseInfo := [fuzzysortLicense, w3ComboboxLicense]
  }
