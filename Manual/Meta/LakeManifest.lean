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
import Manual.Meta.LexedText

import Lake.Load.Manifest

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

open Lean.Parser in
open Verso.Parser in
open LexedText in
def jsonHl : Highlighter where
  name := "json"
  lexer :=
    token `brace (chFn '{' <|> chFn '}') <|>
    token `arr (chFn '[' <|> chFn ']') <|>
    token `delim (chFn ',' <|> chFn ':') <|>
    token `bool (strFn "true" <|> strFn "false") >> notFollowedByFn (satisfyFn Char.isAlphanum) "number or letter" <|>
    token `null (strFn "null" <|> strFn "false") <|>
    token `num (many1Fn (satisfyFn Char.isDigit) >> optionalFn (chFn '.' >> many1Fn (satisfyFn Char.isDigit))) <|>
    token `str (chFn '"' >> manyFn (satisfyEscFn (· != '"')) >> chFn '"') <|>
    token `ident (many1Fn (satisfyFn (· ∉ "() \t\n".toList)))
  tokenClass := fun s => some (toString s.getKind)


private def parseJson (str : StrLit) : DocElabM (Json × LexedText) := do
  let s := str.getString
  let json ←
    match Json.parse s with
    | .ok json => pure json
    | .error e => throwError m!"Block contains invalid JSON: {e}"
  match json.getObjValAs? Lake.StdVer "version" with
  | .ok ver =>
    unless ver == Lake.Manifest.version do
      throwError m!"Block uses out-of-date manifest format. Expected version {Lake.Manifest.version}."
  | .error e => throwError m!"Block has invalid schema version: {e}"
  let lexed ← LexedText.highlight jsonHl s
  return (json, lexed)

private def json.css := "
.json {
  font-family: var(--verso-code-font-family);
}

pre.json {
  margin: 0.5rem .75rem;
  padding: 0.1rem 0;
}

.json .bool, .json .null {
  font-weight: 600;
}

.json .bool {
  color: #107090;
}

.json .str {
  color: #0a5020;
}

.json .num {
  color: #3030c0;
}

"

block_extension Block.json (value : LexedText) where
  data := toJson value
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [json.css]
  toHtml := some <| fun _ _ _ info _ => open Verso.Output.Html in do
    let .ok (v : LexedText) := fromJson? info
      | HtmlT.logError s!"Failed to deserialize {info} as lexer-enhanced text"; pure .empty
    pure {{<pre class="json">{{v.toHtml}}</pre>}}

/--
Check that contents of the block is a valid manifest file.
-/
@[code_block]
def lakeManifest : CodeBlockExpanderOf Unit
  | (), str => do
    let (json, toks) ← parseJson str
    match Lake.Manifest.decodeEntries json with
    | .ok _ => pure ()
    | .error e => throwError m!"Block is not a valid manifest: {e}"
    ``(Verso.Doc.Block.other (Block.json $(quote toks)) #[Verso.Doc.Block.code $str])

/--
Check that contents of the block is a valid package overrides file.
-/
@[code_block]
def lakePackageOverrides : CodeBlockExpanderOf Unit
  | (), str => do
    let (json, toks) ← parseJson str
    match fromJson? json with
    | .ok (_ : Lake.Manifest) => pure ()
    | .error e => throwError m!"Block is not a valid package overrides file: {e}"
    ``(Verso.Doc.Block.other (Block.json $(quote toks)) #[Verso.Doc.Block.code $str])
