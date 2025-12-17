/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.Example

open Lean
set_option doc.verso true

/-
A tabbed container for MWEs in an error explanation example. Must satisfy the invariant that
`titles.size` is equal to the number of children of this block.

This is intended to be formatted with a bottom border separating it from subsequent content, and is
only intended to be used in the context of elaborated `errorExample` directives.
-/
block_extension Manual.Block.tabbedErrorReproduction (titles : Array String) where
  data := toJson titles
  traverse id _data _blocks := do
    discard <| Verso.Genre.Manual.externalTag id (← read).path "error-example"
    pure none
  toTeX := none
  extraCss := [r#"
.error-example-container:not(:last-child) {
  border-bottom: 1px solid gray;
  padding-bottom: var(--verso--box-padding);
}
.error-example-tab-list [role="tab"] {
  position: relative;
  z-index: 1;
  background: white;
  border: 0;
  padding: 0.2em;
  cursor: pointer;
}
.error-example-tab-list [role="tab"]:not(:last-child) {
  margin-right: 1rem;
}
.error-example-tab-list [role="tab"][aria-selected="true"] {
  border-bottom: 1px solid gray;
}
/* this rule and the following ensure that all tabs are the same height */
.error-example-tab-view {
  display: flex;
}
.error-example-tabpanel {
  margin-right: -100%;
  width: 100%;
  display: block;
}
.error-example-tabpanel.error-example-tabpanel-hidden {
  visibility: hidden;
}
.error-example-tabpanel .hl.lean .token {
  /* unset transition to avoid lag when switching panels */
  transition: visibility 0s;
}
  "#]
  extraJs := [r#"
window.addEventListener('DOMContentLoaded', () => {
  const tabLists = document.querySelectorAll('.error-example-tab-list')
  tabLists.forEach(tabList => {
    const tabs = tabList.querySelectorAll(':scope > [role="tab"]')

    const setActiveTab = (e) => {
      for (const tab of tabs) {
        const controllee = document.getElementById(tab.getAttribute('aria-controls'))
        if (tab === e.target) {
          tab.setAttribute('aria-selected', true)
          controllee.classList.remove('error-example-tabpanel-hidden')
        } else {
          tab.setAttribute('aria-selected', false)
          controllee.classList.add('error-example-tabpanel-hidden')
        }
      }
    }

    tabs.forEach(tab => {
      tab.addEventListener('click', setActiveTab)
    })

    let focusedIdx = 0
    tabList.addEventListener('keydown', e => {
      if (e.key === 'ArrowRight' || e.key === 'ArrowLeft') {
        tabs[focusedIdx].setAttribute('tabindex', -1)
        focusedIdx =
          e.key === 'ArrowRight'
          ? (focusedIdx + 1) % tabs.length
          : (focusedIdx - 1 + tabs.length) % tabs.length
        tabs[focusedIdx].setAttribute('tabindex', 0)
        tabs[focusedIdx].focus()
      }
    })
  })
})
  "#]
  toHtml := some fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
    let .ok titles := FromJson.fromJson? (α := Array String) info
      | HtmlT.logError "Invalid titles JSON for example block"
        pure .empty
    unless titles.size == contents.size do
      HtmlT.logError s!"Mismatched number of titles and contents for example block: \
        Found {contents.size} tab panels but {titles.size} titles."
      return .empty
    let some { htmlId, .. } := (← HtmlT.state).externalTags[id]?
      | HtmlT.logError "Could not find tag for error example"
        pure .empty
    let buttons ← titles.mapIdxM fun i (title : String) => do
      let (tabIndex, selected) := if i == 0 then ("0", "true") else ("-1", "false")
      let idxStr := toString i
      return {{
        <button type="button" role="tab"
            aria-selected={{selected}}
            tabindex={{tabIndex}}
            id={{s!"{htmlId.toString}-button-{idxStr}"}}
            aria-controls={{s!"{htmlId.toString}-panel-{idxStr}"}}>
          {{title}}
        </button>
      }}
    let panels ← contents.mapIdxM fun i b => do
      let className := "error-example-tabpanel" ++ if i == 0 then "" else " error-example-tabpanel-hidden"
      let idxStr := toString i

      -- Turn off `inlineProofStates` rendering in the context of the panel to avoid painful
      -- z-index issues
      let panelContents ← withReader (fun ctx => { ctx with codeOptions := { ctx.codeOptions with inlineProofStates := false } } )
        (goB b)
      return {{
        <div role="tabpanel"
            class={{className}}
            id={{s!"{htmlId.toString}-panel-{idxStr}"}}
            aria-labelledby={{s!"{htmlId.toString}-button-{i}"}}>
          {{ panelContents }}
        </div>
      }}
    pure {{
      <div class="error-example-container">
        <div class="error-example-tab-list" role="tablist" aria-label="Code Samples">
          {{buttons}}
        </div>
        <div class="error-example-tab-view">
          {{panels}}
        </div>
      </div>
    }}


variable [Monad m] [MonadError m]
set_option pp.rawOnError true
structure ErrorExampleConfig where
  title : String
instance : Verso.ArgParse.FromArgs ErrorExampleConfig m where
  fromArgs :=
    ErrorExampleConfig.mk <$> Verso.ArgParse.positional `title Verso.ArgParse.ValDesc.string

/--
Structured examples that show a minimum working example (MWE) of an error, as well as one or more
corrections, in a fashion suitable for error explanations. The structure is relatively rigid:

 * One code block labeled "broken" containing Lean code that generates an error
 * One code block labeled "output" that contains the plan text of (one of the) generated errors
 * One or more code blocks labeled "fixed" that contain Lean code demonstrating how the error can
   be corrected. If there is more than one block, the block must have an additional positional
   argument, a string describing the example. (A block labeled {lit}`fixed "descr"` will be
   displayed as "Fixed (descr).")

**Example**
`````
:::errorExample "Only a Dot Before the Numeral"
```broken
example := .3
```
```output
invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
```
```fixed "make it an `Nat`"
example := 3
```
```fixed "make it a `Float`"
example := 0.3
```
Some explanatory text here.
:::
`````
-/
@[directive]
def errorExample : Verso.Doc.Elab.DirectiveExpanderOf ErrorExampleConfig
  | { title }, contents => do
    let brokenStx :: restStx := contents.toList
      | throwError m!"The error example had no contents"
    let `(Lean.Doc.Syntax.codeblock|``` broken| $brokenTxt ```) := brokenStx
      | throwErrorAt brokenStx m!"First element in errorExample must be a `broken` codeblock containing the broken minimal working example"

    let errorStx :: restStx := restStx
      | throwError m!"The error example did not contain a second element"
    let `(Lean.Doc.Syntax.codeblock|``` output| $errorTxt ```) := errorStx
      | throwErrorAt errorStx m!"Second element in errorExample must be an `output` codeblock containing the generated error message"

    let brokenBlock ← brokenTxt |> Verso.Genre.Manual.InlineLean.lean
      { «show» := true, keep := false, name := `broken.lean, error := true, fresh := true }
    let errorBlock ← errorTxt |> Verso.Genre.Manual.InlineLean.leanOutput
      { «show» := true, summarize := false, name := mkIdentFrom errorStx `broken.lean, severity := .none, whitespace := .exact, normalizeMetas := true, allowDiff := 0 }
    let (fixedExamples, narrativeStx) ← partitionFixed restStx

    let fixedBlocks : List (String × Term) ← match fixedExamples with
      | [] => throwErrorAt restStx[0]! "Error examples must include one or more `fixed` codeblocks containing a fix for broken code"
      | [(_, .none, fixedTxt)] =>
        let contents ← Verso.Genre.Manual.InlineLean.lean { «show» := true, keep := false, name := none, error := false, fresh := true } fixedTxt
        pure [("Fixed", contents)]
      | [(_, .some title, _)] => throwErrorAt title m!"Error explanations with a single title don't need to name the title"
      | _ =>
        fixedExamples.mapM (fun (syn, exampleName, fixedTxt) => do
          let .some q := exampleName
            | throwErrorAt syn "Error explanations with more than one title need to name each title"
          let contents ← Verso.Genre.Manual.InlineLean.lean { «show» := true, keep := false, name := none, error := false, fresh := true } fixedTxt
          pure (s!"Fixed ({q.getString})", contents)
          )

    let narrativeBlocks ← narrativeStx.mapM Verso.Doc.Elab.elabBlock

    let tabbedContentHeaders :=
      "Original" :: fixedBlocks.map (·.1)
    let tabbedContentBlocks :=
      (← ``(Doc.Block.concat #[$brokenBlock, $errorBlock])) :: fixedBlocks.map (·.2)

    ``(Doc.Block.other (Manual.Block.example $(quote (title)) none (opened := true))
        #[Doc.Block.para #[Doc.Inline.text $(quote (title))],
          Doc.Block.other (Manual.Block.tabbedErrorReproduction $(quote tabbedContentHeaders.toArray)) #[$tabbedContentBlocks.toArray,*],
          $narrativeBlocks.toArray,*])
where
  partitionFixed (blocks: List (TSyntax `block)) : Verso.Doc.Elab.DocElabM (List (Syntax × Option StrLit × TSyntax `str) × List (TSyntax `block)) := do
  match blocks with
  | [] => pure ([], [])
  | block :: rest =>
    let `(Lean.Doc.Syntax.codeblock|``` fixed $args*| $fixedTxt ```) := block
      | return ([], blocks)
    let parsedArgs ← Verso.Doc.Elab.parseArgs args
    let arg? : Option _ ← match parsedArgs.toList with
      | [] => pure none
      | [.anon (.str title)] => pure <| some title
      | [_] => throwErrorAt args[0]! m!"String arg expected"
      | _ => throwErrorAt args[1]! m!"At most one string arg expected"
    let (fixedExamples, descrBlocks) ← partitionFixed rest
    return ((block, arg?, fixedTxt) :: fixedExamples, descrBlocks)
