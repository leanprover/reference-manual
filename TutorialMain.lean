/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
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


def version (_content : Array (Verso.Doc.Inline g)) : Verso.Doc.Inline g := .text Lean.versionString

def manualLink (args : Array (Verso.Doc.Inline g)) : Verso.Doc.Inline g:=
  Verso.Doc.Inline.link args Lean.manualRoot

open Verso.Doc Concrete in
def tutorials : Tutorials where
  content :=
  (verso (Page) "Tutorials"
   :::::::
   These tutorials cover version {version}[] of Lean.
   While the {manualLink}[reference manual] describes the system and its features in detail, these tutorials provide focused introductions to specific tools.
   :::::::).toPart

  topics := #[
    { title := #[inlines!"Tactics"],
      titleString := "Tactics"
      description := #[blocks!"These tutorials demonstrate Lean's advanced proof automation."]
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


def codeColors := r#"
:root {
  --verso-code-color: var(--color-text) !important;
}
"#

def localToCStyle := r#"
/*
nav.local-toc {
  position: fixed;
  top: calc(var(--nav-height) + 1rem + 60px);
  right: calc((100vw - var(--container-width)) / 2 - 15rem - 2rem);
  width: 15rem;
  font-size: 0.875rem;
  max-height: calc(100vh - 2rem - var(--nav-height) - 60px);
  overflow-y: auto;
}
*/

nav.local-toc h1 {
  display: none;
}

nav.local-toc ol {
  list-style: none;
  margin: 0;
  padding: 0;
  display: none;
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
/*
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
*/

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
