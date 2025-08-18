/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Verso.Code

import SubVerso.Highlighting
import SubVerso.Examples

import Manual.Meta.Basic

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

def Inline.envVar : Inline where
  name := `Manual.envVar
  data := .arr #[.null, .bool false]


@[role_expander envVar]
def envVar : RoleExpander
  | args, inlines => do
    let isDef ← parseOpts.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $varName:str )) := arg
      | throwErrorAt arg "Expected code literal with the environment variable"
    let v := varName.getString

    pure #[← `(.other {Manual.Inline.envVar with data := Json.arr #[.str $(quote v), .bool $(quote isDef)] } #[Inline.code $(quote v)])]
  where
    parseOpts : ArgParse DocElabM Bool := .flag `def false "If true, this is the definition site (i.e. the link target) for the variable"

def envVarDomain := `Manual.envVar

open Verso.Search in
def envVarDomainMapper : DomainMapper :=
  DomainMapper.withDefaultJs envVarDomain "Environment Variable" "env-var-domain" |>.setFont { family := .code }

@[inline_extension envVar]
def envVar.descr : InlineDescr where
  init s :=
    s |>.setDomainTitle envVarDomain "Environment Variables"
      |>.addQuickJumpMapper envVarDomain envVarDomainMapper

  traverse id data _ := do
    let .arr #[.str var, .bool isDef] := data
      | logError s!"Couldn't deserialize environment variable info from {data}"; return none
    if isDef then
      let path ← (·.path) <$> read
      let _ ← Verso.Genre.Manual.externalTag id path var
      Index.addEntry id {term := Doc.Inline.concat #[.code var, .text " (environment variable)"]}
      modify fun s =>
        s.saveDomainObject envVarDomain var id
    return none

  toTeX := none

  extraCss := [
r#"
.env-var a {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
.env-var a:hover {
  text-decoration: currentcolor underline solid;
}

"#
]

  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let (var, isDef) ←
        match data with
        | .arr #[.str var, .bool isDef] => pure (var, isDef)
        | _ => HtmlT.logError s!"Couldn't deserialize environment var info from {data}"; return .empty

      if let some dest := (← read).traverseState.getDomainObject? envVarDomain var then
        for id in dest.ids do
          if let some dest := (← read).traverseState.externalTags[id]? then
            if isDef then
              -- TODO find an inline permalink widget that doesn't mess up text flow
              return {{
                  <code class="env-var" id={{dest.htmlId.toString}}>s!"{var}"</code>
              }}
            else
              let url := dest.link
              return {{<code class="env-var"><a href={{url}}>s!"{var}"</a></code>}}

      return {{<code class="env-var">s!"{var}"</code>}}

  localContentItem _ info _ := open Verso.Output.Html in do
    if let .arr #[.str var, .bool isDef] := info then
      if isDef then
        pure #[(var, {{<code>{{var}}</code>}}), (s!"{var} (Environment Variable)", {{<code>{{var}}</code>" (Environment Variable)"}})]
      else pure #[]
    else throw s!"Expected a two-element array with a string and a Boolean, got {info}"
