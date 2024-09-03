import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Verso.Code

namespace Manual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

def Inline.margin : Inline where
  name := `Manual.margin

@[role_expander margin]
def margin : RoleExpander
  | args, inlines => do
    ArgParse.done.run args
    let content ← inlines.mapM elabInline
    pure #[← `(Doc.Inline.other Inline.margin #[$content,*])]

@[inline_extension margin]
def margin.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  extraCss := [r#"
.marginalia .note {
  position: relative;
  padding: 0.5rem;
}
/* Wide viewport */
@media (min-width: 1400px) {
.marginalia .note {
  float: right;
  clear: right;
  margin-right: -19vw;
  width: 15vw;
  margin-top: 1rem;
}
}

.marginalia:hover, .marginalia:hover .note, .marginalia:has(.note:hover) {
  background-color: var(--lean-accent-light-blue);
}

/* Narrow viewport */
@media (max-width: 1400px) {
.marginalia .note {
  float: right;
  clear: right;
  width: 40%;
  margin: 1rem 0;
  margin-left: 5%;
}
}
body {
  counter-reset: margin-note-counter;
}
.marginalia .note {
  counter-increment: margin-note-counter;
}
.marginalia .note::before {
  content: counter(margin-note-counter) ".";
  position: absolute;
  vertical-align: baseline;
  font-size: 0.9em;
  font-weight: bold;
  left: -3rem;
  width: 3rem;
  text-align: right;
}
.marginalia::after {
  content: counter(margin-note-counter);
  vertical-align: super;
  font-size: 0.7em;
  font-weight: bold;
  margin-right: 0.5em;
}
"#]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ _ content  => do
      pure {{<span class="marginalia"><span class="note">{{← content.mapM goI}}</span></span>}}
