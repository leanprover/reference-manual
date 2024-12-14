/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Term
import Lean.Elab.Tactic

import Verso.Code.Highlighted
import Verso.Doc.ArgParse
import Verso.Doc.Suggestion
import SubVerso.Highlighting.Code
import VersoManual

import Manual.Meta.Basic
import Manual.Meta.PPrint
import Manual.Meta.Lean
import Manual.Meta.Lean.Scopes

namespace Manual

open Lean Elab Term Tactic
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open Manual.Meta.Lean.Scopes
open SubVerso.Highlighting

def parserAliasDomain := `Manual.parserAlias

def Block.parserAlias (name : Name) (declName : Name) («show» : Option String) (stackSz? : Option Nat) (autoGroupArgs : Bool) (docs? : Option String) (argCount : Nat) : Block where
  name := `Manual.Block.parserAlias
  -- These are represented as an array, rather than using the ToJson instance for a tuple, because
  -- the traversal pass only needs two fields and it's wasteful to deserialize the whole thing.
  data := Json.arr #[
    ToJson.toJson name,
    ToJson.toJson declName,
    ToJson.toJson «show»,
    ToJson.toJson stackSz?,
    ToJson.toJson autoGroupArgs,
    ToJson.toJson docs?,
    ToJson.toJson argCount
  ]

structure ParserAliasOptions where
  name : Name
  «show» : Option String

def ParserAliasOptions.parse [Monad m] [MonadError m] : ArgParse m ParserAliasOptions :=
  ParserAliasOptions.mk <$> .positional `name .name <*> .named `show .string true



@[directive_expander parserAlias]
def parserAlias : DirectiveExpander
  | args, more => do
    let opts ← ParserAliasOptions.parse.run args
    let {declName, stackSz?, autoGroupArgs} ← Parser.getParserAliasInfo opts.name
    let docs? ← findDocString? (← getEnv) declName

    let some mdAst := MD4Lean.parse (docs?.getD "")
      | throwError "Failed to parse docstring as Markdown"
    let contents ← mdAst.blocks.mapM (Markdown.blockFromMarkdown · Markdown.strongEmphHeaders)
    let userContents ← more.mapM elabBlock

    let argCount :=
      match (← Lean.Parser.getAlias Lean.Parser.parserAliasesRef opts.name) with
      | some (.unary ..) => 1
      | some (.binary ..) => 2
      | _ => 0

    pure #[← ``(Verso.Doc.Block.other (Block.parserAlias $(quote opts.name) $(quote declName) $(quote opts.show) $(quote stackSz?) $(quote autoGroupArgs) $(quote docs?) $(quote argCount)) #[$(contents ++ userContents),*])]

@[inline]
private def getFromJson {α} [Inhabited α] [FromJson α] (v : Json) : HtmlT Genre.Manual (ReaderT ExtensionImpls IO) α:=
  match FromJson.fromJson? (α := α) v with
  | .error e => do
    Verso.Doc.Html.HtmlT.logError
      s!"Failed to deserialize parser alias data while generating HTML for a parser alias docstring.\nError: {e}\nJSON: {v}\n\n"
    pure default
  | .ok v => pure v

open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension Block.parserAlias]
def parserAlias.descr : BlockDescr where
  init st := st
    |>.setDomainTitle parserAliasDomain "Parser Alias Documentation"
    |>.setDomainDescription parserAliasDomain "Detailed descriptions of parser aliases"

  traverse id info _ := do
    let Json.arr #[ name, _, «show», _, _, _, _] := info
      | do logError s!"Failed to deserialize docstring data while traversing a parser alias, expected array but got {info}"; pure none
    let .ok (name, «show») := do return (← FromJson.fromJson? (α := Name) name, ← FromJson.fromJson? (α := Option String) «show»)
      | do logError "Failed to deserialize docstring data while traversing a parser alias"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| show.getD name.toString
    Index.addEntry id {term := Doc.Inline.code <| show.getD name.toString}
    modify fun st => st.saveDomainObject parserAliasDomain name.toString id
    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let Json.arr #[ name, declName, «show», stackSz?, autoGroupArgs, docs?, argCount] := info
        | do Verso.Doc.Html.HtmlT.logError s!"Failed to deserialize docstring data while making HTML for parser alias, expected array but got {info}"; pure .empty

      let name ← getFromJson (α := Name) name
      let declName ← getFromJson (α := Name) declName
      let «show» ← getFromJson (α := Option String) «show»
      let stackSz? ← getFromJson (α := Option Nat) stackSz?
      let autoGroupArgs ← getFromJson (α := Bool) autoGroupArgs
      let docs? ← getFromJson (α := Option String) docs?
      let argCount ← getFromJson (α := Nat) argCount

      let x : Highlighted := .token ⟨.keyword declName none docs?, show.getD name.toString⟩
      let args : Highlighted :=
        match argCount with
        | 1 => .seq <|
          #[.token ⟨.unknown, "("⟩, .token ⟨.unknown, "p"⟩, .token ⟨.unknown, ")"⟩]
        | 2 => .seq <|
          #[.token ⟨.unknown, "("⟩, .token ⟨.unknown, "p1"⟩, .token ⟨.unknown, ", "⟩, .token ⟨.unknown, "p2"⟩, .token ⟨.unknown, ")"⟩]
        | _ => .empty

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      let arity : Html :=
        match stackSz? with
        | some n => {{s!"Arity: {n}"}}
        | none => {{"Arity is sum of arguments' arities"}}
      let grp :=
        if autoGroupArgs then
          some {{"Automatically wraps arguments in a " <code>"null"</code> " node unless there's exactly one"}}
        else none
      let meta :=
        match grp with
        | none => {{<p>{{arity}}</p>}}
        | some g => {{<ul><li>{{arity}}</li><li>{{g}}</li></ul>}}

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"parser alias"</span>
          <pre class="signature hl lean block">{{← (Highlighted.seq #[x, args]).toHtml}}</pre>
          <div class="text">
            {{meta}}
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := none
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]
