/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public meta import Verso.Doc.Elab.Monad
public import VersoManual.Basic
import Verso.Doc.ArgParse
import VersoManual.Index

public section

open Verso ArgParse Doc Elab Genre.Manual Html Code
open Lean Elab
open Lean.Doc (CodeView)

namespace Manual

def Inline.executable : Inline where
  name := `Manual.executable
  data := .arr #[.null, .bool false]

/--
The name of a command-line tool.

The `+def` flag marks the definition site, which is the link target for the tool's other mentions.
-/
@[role_expander executable]
meta def executable : RoleExpander
  | args, inlines => do
    let isDef ← parseOpts.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let some { content := exeName, .. } := CodeView.of arg
      | throwErrorAt arg "Expected code literal with the executable's name"
    let e := exeName.getVersoCode

    pure #[← `(.other {Manual.Inline.executable with data := Json.arr #[.str $(quote e), .bool $(quote isDef)] } #[Inline.code $(quote e)])]
  where
    parseOpts : ArgParse DocElabM Bool := .flag `def false "If true, this is the definition site (i.e. the link target) for the executable"

def executableDomain := `Manual.executable

open Verso.Search in
private def executableDomainMapper : DomainMapper :=
  DomainMapper.withDefaultJs executableDomain "Executable" "executable-domain" |>.setFont { family := .code }

@[inline_extension executable]
def executable.descr : InlineDescr where
  init s :=
    s |>.setDomainTitle executableDomain "Executables"
      |>.addQuickJumpMapper executableDomain executableDomainMapper

  traverse id data _ := do
    let .arr #[.str exe, .bool isDef] := data
      | reportError s!"Couldn't deserialize executable info from {data}"; return none
    if isDef then
      -- Error if this executable is defined anywhere other than here.
      if let some obj := (← get).getDomainObject? executableDomain exe then
        -- To avoid spamming every traversal pass, we only check on first registration,
        -- i.e., when this ID hasn't been stored in the domain yet.
        unless obj.ids.contains id do
          let others := obj.ids.toList.filterMap ((← get).externalTags[·]?) |>.map (·.link)
          reportError s!"Executable '{exe}' is defined more than once; it is already defined at {", ".intercalate others}"
      let path ← (·.path) <$> read
      let _ ← Verso.Genre.Manual.externalTag id path exe
      Index.addEntry id {term := Inline.concat #[.code exe, .text " (executable)"]}
      modify fun s =>
        s.saveDomainObject executableDomain exe id
    return none

  toTeX := none

  extraCss := [
r#"
.executable a {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
.executable a:hover {
  text-decoration: currentcolor underline solid;
}
"#
]

  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let (exe, isDef) ←
        match data with
        | .arr #[.str exe, .bool isDef] => pure (exe, isDef)
        | _ => reportError s!"Couldn't deserialize executable info from {data}"; return .empty

      if let some dest := (← read).traverseState.getDomainObject? executableDomain exe then
        for id in dest.ids do
          if let some dest := (← read).traverseState.externalTags[id]? then
            if isDef then
              return {{<code class="executable" id={{dest.htmlId.toString}}>s!"{exe}"</code>}}
            else
              let url := dest.link
              return {{<code class="executable"><a href={{url}}>s!"{exe}"</a></code>}}

      return {{<code class="executable">s!"{exe}"</code>}}

  localContentItem _ info _ := open Verso.Output.Html in do
    if let .arr #[.str exe, .bool isDef] := info then
      if isDef then
        pure #[(exe, {{<code>{{exe}}</code>}}), (s!"{exe} (Executable)", {{<code>{{exe}}</code>" (Executable)"}})]
      else pure #[]
    else throw s!"Expected a two-element array with a string and a Boolean, got {info}"
