/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual.Marginalia

open Verso.Genre.Manual
open Verso.Doc.Elab

namespace Manual

def sectionNote.css := r#"
.section-note .note {
  position: relative;
  padding: 0.5rem;
  border: 1px solid #98B2C0;
  border-radius: 0.5rem;
  margin-bottom: var(--verso--box-vertical-margin);
  padding: 0 var(--verso--box-padding) var(--verso--box-padding);
}

.section-note .note > h1 {
  font-size: 1.25rem;
  font-weight: bold;
  margin-top: 0;
  margin-bottom: 1rem;
}

.section-note .note > :first-child {
  margin-top: 0;
  padding-top: 0;
}

/* Wide viewport */
@media screen and (min-width: 1400px) {
  .section-note .note {
    float: right;
    clear: right;
    margin-right: -16rem;
    width: 13rem;
  }
}

/* Very wide viewport */
@media screen and (min-width: 1600px) {
  .section-note .note {
    margin-right: -19vw;
    width: 15vw;
  }
}

/* Medium viewport */
@media screen and (700px < width <= 1400px) {
  .section-note .note {
    float: right;
    clear: right;
    width: calc(50% - 2rem);
    min-width: 12rem;
    margin: 1rem 0;
    margin-left: 10%;
  }
}

/* Narrow viewport (e.g. phone) */
@media screen and (width <= 700px) {
  .section-note .note {
    float: left;
    clear: left;
    width: calc(100% - 2rem);
    margin: 1rem 0;
  }
}

"#

open Verso.Output Html in
def sectionNoteHtml (content : Html) : Html :=
  {{<div class="section-note"><div class="note">{{content}}</div></div>}}


block_extension Block.sectionNote where
  traverse _ _ _ := return none
  toTeX := none

  extraCss := [sectionNote.css]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content  => do
      sectionNoteHtml <$> content.mapM goB

@[directive]
def sectionNote : DirectiveExpanderOf Unit
  | (), inlines => do
    let content ← inlines.mapM elabBlock
    ``(Verso.Doc.Block.other Block.sectionNote #[$content,*])

open Verso.Doc.Html

block_extension Block.sectionNoteTitle where
  traverse _ _ _ := return none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ _ _ content => do
      match content with
      | #[.para xs] =>
        return {{<h1> {{← xs.mapM goI}} </h1>}}
      | _ => HtmlT.logError "Malformed section note title"; return .empty

@[directive]
def tutorials : DirectiveExpanderOf Unit
  | (), blocks => do
    let content ← blocks.mapM elabBlock
    ``(Verso.Doc.Block.other Block.sectionNote #[Verso.Doc.Block.other Block.sectionNoteTitle #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "Tutorials"]], $content,*])


@[directive]
def seeAlso : DirectiveExpanderOf Unit
  | (), blocks => do
    let content ← blocks.mapM elabBlock
    ``(Verso.Doc.Block.other Block.sectionNote #[Verso.Doc.Block.other Block.sectionNoteTitle #[Verso.Doc.Block.para #[Verso.Doc.Inline.text "See Also"]], $content,*])
