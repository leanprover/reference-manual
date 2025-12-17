/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoTutorial
import VersoBlog
import Tutorial
import Tutorial.Meta.Theme
import VersoWeb.Theme

open Verso.Genre.Manual
open Verso.Genre.Tutorial
open Verso.Genre.Blog (Page)

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

def version (_content : Array (Verso.Doc.Inline g)) : Verso.Doc.Inline g := .text Lean.versionString

open Verso.Doc Concrete in
def tutorials : Tutorials where
  content :=
  (verso (Page) "Tutorials"
   :::::::
   These tutorials are written for version {version}[] of Lean.
   :::::::).toPart

  topics := #[
    { title := #[inlines!"Tactics"],
      titleString := "Tactics"
      description := #[blocks!"..."]
      tutorials := #[%doc Tutorial.VCGen, %doc Tutorial.Grind.IndexMap]
    }

  ]

open Verso.Genre.Blog Site.Syntax in
open Verso.Doc in
def leanSite : Site :=
  site home /
    "install" install
    "learn" learn
    "community" community
    "use-cases" «use-cases»
    "fro" fro
where
  placeholder title : Part Page := { title := #[.text title], titleString := title, metadata := none, content := #[], subParts := #[] }
  home : VersoDoc Page := { construct := fun _ => placeholder "Lean" }
  install : VersoDoc Page := { construct := fun _ => placeholder "Install" }
  learn : VersoDoc Page := { construct := fun _ => placeholder "Learn" }
  community : VersoDoc Page := { construct := fun _ => placeholder "Community" }
  «use-cases» : VersoDoc Page := { construct := fun _ => placeholder "Use Cases" }
  «trademark-policy» : VersoDoc Page := { construct := fun _ => placeholder "Trademark Policy" }
  privacy : VersoDoc Page := { construct := fun _ => placeholder "Privacy" }
  terms : VersoDoc Page := { construct := fun _ => placeholder "Terms" }
  logos : VersoDoc Page := { construct := fun _ => placeholder "Logos" }
  fro : VersoDoc Page := { construct := fun _ => placeholder "FRO" }
  documentation : VersoDoc Page := { construct := fun _ => placeholder "Documentation" }
  examples : VersoDoc Page :={ construct := fun _ => placeholder "Examples" }
  publications : VersoDoc Page := { construct := fun _ => placeholder "Publications" }
  links : VersoDoc Page := { construct := fun _ => placeholder "Links" }
  people : VersoDoc Page := { construct := fun _ => placeholder "People" }

-- open Verso.Output.Html in
-- def theme : Theme where
--   page content := do
--     let config := { logError := fun _ => pure () }
--     let ctxt := {
--       site := leanSite,
--       ctxt := {
--         config,
--         components := {},
--         path := #["doc", "tutorials"]
--       },
--       xref := { remoteContent := {} },
--       linkTargets := {},
--       dir := "",
--       config,
--       header := ""
--     }
--     let pageContent := {{<div class="post-center post-page"><article class="post-container"><div class="post-content">{{content.content}}</div></article></div>}}
--     let mut params : Verso.Genre.Blog.Template.Params := {}
--     params := params.insert "title" content.title
--     params := params.insert "content" pageContent
--     let ((html, st'), y) ← Verso.Genre.Blog.Template.renderMany [LeanLangOrg.theme.pageTemplate, LeanLangOrg.theme.primaryTemplate] params ctxt {} {}
--     pure html
--   topic := Theme.default.topic
--   tutorialToC := Theme.default.tutorialToC
--   cssFiles := Verso.Web.Theme.Static.allCSS.map fun (filename, contents) =>
--     { filename := s!"theme/style/{filename}", contents }


def codeColors := r#"
:root {
  --verso-code-color: var(--color-text) !important;
}
"#

def localToCStyle := r#"
nav.local-toc {
  position: fixed;
  top: calc(var(--nav-height) + 1rem + 60px);
  right: calc((100vw - var(--container-width)) / 2 - 15rem - 2rem);
  width: 15rem;
  font-size: 0.875rem;
  max-height: calc(100vh - 2rem - var(--nav-height) - 60px);
  overflow-y: auto;
}

nav.local-toc h1 {
  display: none;
}

nav.local-toc ol {
  list-style: none;
  margin: 0;
  padding: 0;
}

nav.local-toc li {
  margin: 0.5rem 0;
}

nav.local-toc a {
  color: var(--verso-text-color);
  text-decoration: none;
}

nav.local-toc a:hover {
  color: var(--color-accent);
}

/* On smaller screens, display normally */
@media (max-width: 90rem) {
  nav.local-toc {
    position: static;
    right: auto;
    width: auto;
    max-height: none;
    border-left: 3px solid var(--color-border);
    padding-left: 1rem;
    margin-bottom: 1rem;
  }
}

nav.local-toc ol ol {
  padding-left: 1rem;
  margin-top: 0.25rem;
}

nav.local-toc ol ol li {
  margin: 0.25rem 0;
}

/*******/
nav.local-toc > div:first-child {
  margin-bottom: 1rem;
}

nav.local-toc h1 {
  font-size: 1rem;
  margin: 0 0 0.5rem 0;
  font-weight: 600;
}

nav.local-toc .code-links {
  display: flex;
  gap: 0.5rem;
  flex-wrap: wrap;
}

nav.local-toc .code-link {
  font-size: 0.8125rem;
  padding: 0.25rem 0.5rem;
  border: 1px solid var(--color-border);
  border-radius: 6px;
  color: var(--verso-text-color);
  text-decoration: none;
  display: inline-block;
}

nav.local-toc .code-link:hover {
  background: var(--verso-selected-color);
  border-color: var(--color-accent);
}

nav.local-toc .code-link code {
  background: none;
  padding: 0;
  font-size: inherit;
}

nav.local-toc .code-link.live::before {
  content: "↪ ";
  margin-right: 0.25rem;
}

nav.local-toc .code-link.download::before {
  content: "📦 ";
  margin-right: 0.25rem;
}
"#


open Verso.Genre.Blog.Template in
open Verso.Output Html in
def theme :=
  { LeanLangOrg.theme with
    pageTemplate := do
      let tutorialNav : Option Html ← param? "tutorialNav"
      let content : Html ← param "content"
      let content := tutorialNav.getD .empty ++ content
      withTheReader Context (fun ρ => { ρ with params := ρ.params.insert "content" content }) LeanLangOrg.theme.pageTemplate
    cssFiles := LeanLangOrg.theme.cssFiles.push ("code-colors.css", codeColors) |>.push ("local-toc.css", localToCStyle)
  }

def main :=
  tutorialsMain tutorials (config := {destination := "_tutorial-out"}) (theme := theme) (navSite := leanSite)
