/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mac Malone
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
import Manual.Meta.ExpectString

import Lake.Load.Manifest

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

private def parseJson (str : StrLit) : DocElabM Json := do
  let json ←
    match Json.parse str.getString with
    | .ok json => pure json
    | .error e => throwError m!"Block contains invalid JSON: {e}"
  match json.getObjValAs? Lake.StdVer "version" with
  | .ok ver =>
    unless ver == Lake.Manifest.version do
      throwError m!"Block uses out-of-date manifest format. Expected version {Lake.Manifest.version}."
  | .error e => throwError m!"Block has invalid schema version: {e}"
  return json

def Block.json : Block where
  name := `Manual.Block.json
  data := Json.null -- TODO

@[block_extension json]
def Block.json.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some <| fun _goI goB _ _ content =>
    content.mapM goB -- TODO

/--
Check that contents of the block is a valid manifest file.
-/
@[code_block_expander lakeManifest]
def lakeManifest : CodeBlockExpander
  | _, str => do
    let json ← parseJson str
    match Lake.Manifest.decodeEntries json with
    | .ok _ => pure ()
    | .error e => throwError m!"Block is not a valid manifest: {e}"
    Array.singleton <$> ``(
      Verso.Doc.Block.other Block.json #[Verso.Doc.Block.code $str]
    )

/--
Check that contents of the block is a valid package overrides file.
-/
@[code_block_expander lakePackageOverrides]
def lakePackageOverrides : CodeBlockExpander
  | _, str => do
    let json ← parseJson str
    match fromJson? json with
    | .ok (_ : Lake.Manifest) => pure ()
    | .error e => throwError m!"Block is not a valid package overrides file: {e}"
    Array.singleton <$> ``(
      Verso.Doc.Block.other Block.json #[Verso.Doc.Block.code $str]
    )
