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


open Verso.Genre.Manual

namespace Manual

def configFileDomain := `Manual.configFile

open Verso.Search in
def configFileDomainMapper : DomainMapper where
  displayName := "Configuration File"
  className := "config-file-domain"
  dataToSearchables :=
  "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => ({
    searchKey: key,
    address: `${value[0].address}#${value[0].id}`,
    domainId: 'Manual.configFile',
    ref: value,
  }))"

inline_extension Inline.configFile (filename : String) where
  init st := st
    |>.setDomainTitle configFileDomain "Configuration Files"
    |>.setDomainDescription configFileDomain "Descriptions of files used to configure Lean and its associated tooling"
    |>.addQuickJumpMapper configFileDomain (configFileDomainMapper.setFont { family := .code })
  data := .str filename
  traverse id data _ := do
    let .str filename := data
      | logError s!"Failed to deserialize {data} as a string for the filename"
        pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path filename
    modify fun st => st.saveDomainObject configFileDomain filename id
    pure none

  toHtml :=
    open Verso.Output.Html in
    open Verso.Doc.Html in
    some fun _ id data _ => do
      let .str filename := data
        | HtmlT.logError s!"Failed to deserialize {data} as a string for the filename"
          pure .empty
      let xref ← HtmlT.state
      let idAttr := xref.htmlId id
      return {{<code {{idAttr}}>{{filename}}</code>}}

  toTeX := none

open Verso.Doc.Elab
open Lean.Doc.Syntax
open Lean

@[role]
def configFile : RoleExpanderOf Unit
  | (), inlines => do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $cmdName:str )) := arg
      | throwErrorAt arg "Expected code literal with the config file's name"
    let filename := cmdName.getString

    `(show Verso.Doc.Inline Verso.Genre.Manual from
      .other (Manual.Inline.configFile $(quote filename)) #[.code $(quote filename)])
