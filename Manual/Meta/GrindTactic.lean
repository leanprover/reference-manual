/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Term
import Lean.Elab.Tactic
import Lean.Meta.Hint

import Verso.Code.Highlighted
import Verso.Doc.ArgParse
import SubVerso.Highlighting.Code
import VersoManual

import Manual.Meta.Basic

open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open Lean Elab Term Parser Tactic Doc
open SubVerso.Highlighting Highlighted
open scoped Lean.Doc.Syntax

namespace Manual

/--
The domain of `grind` interactive tactics, used for cross-references and search.
-/
def grindTacticDomain : Name := `Manual.tactic.grind

/--
Heuristically maps the syntax kinds in the `grind` interactive tactic category to their leading
tokens by inspecting the category's Pratt parsing tables.

This replicates `Lean.Elab.Tactic.Doc.firstTacticTokens`, which only scans the `tactic` syntax
category and so does not cover the `grind` category.
-/
def firstGrindTokens [Monad m] [MonadEnv m] : m (Lean.NameMap String) := do
  let env ← getEnv
  let some cat := parserExtension.getState env |>.categories.find? `grind
    | return {}
  let mut firstTokens : Lean.NameMap String := {}
  firstTokens := addFirstTokens cat cat.tables.leadingTable firstTokens
  firstTokens := addFirstTokens cat cat.tables.trailingTable firstTokens
  return firstTokens
where
  addFirstTokens cat table firsts : Lean.NameMap String := Id.run do
    let mut firsts := firsts
    for (tok, ps) in table do
      -- Skip antiquotes
      if tok == `«$» then continue
      for (p, _) in ps do
        for (k, ()) in p.info.collectKinds {} do
          if cat.kinds.contains k then
            let tok := tok.toString (escape := false)
            firsts := firsts.alter k (·.getD tok)
    return firsts

structure GrindTacticDoc where
  name : Name
  «show» : String
  docs? : Option String

/--
Builds a hint whose code actions replace the ambiguous reference at `span` with an unambiguous
syntax kind, one suggestion per candidate. Each kind is unresolved in the current scope, so the
suggestion uses the shortest name that refers to it here.
-/
def grindDisambiguationHint (span : Syntax) (kinds : List Name) : TermElabM MessageData := do
  let suggestions ← kinds.toArray.mapM fun k => do
    let n ← unresolveNameGlobal k
    return ({ suggestion := .tsyntax (mkIdent n), span? := some span } : Lean.Meta.Hint.Suggestion)
  m!"Name the intended syntax kind.".hint suggestions (ref? := span)

/--
Resolves a `grind` interactive tactic, either by its leading token (a string literal) or by its
syntax kind (an identifier matched as a suffix). Returns the resolved kind, its leading token, and
its docstring. Ambiguity is an error.
-/
def getGrindTactic (name : StrLit ⊕ Ident) (allowMissing : Option Bool) : TermElabM GrindTacticDoc :=
  withOptions (allowMissing.map (fun b opts => verso.docstring.allowMissing.set opts b) |>.getD id) do
    let env ← getEnv
    let parserState := parserExtension.getState env
    let some cat := parserState.categories.find? `grind
      | throwError "Couldn't find grind tactic list"
    let firsts ← firstGrindTokens
    let mk (k : Name) (tok : String) : TermElabM GrindTacticDoc :=
      return ⟨k, tok, ← getDocString? env k⟩
    match name with
    | .inr kind =>
      let mut cands : Array Name := #[]
      for (k, ()) in cat.kinds do
        if kind.getId.isSuffixOf k then cands := cands.push k
      match cands.toList with
      | [] => throwErrorAt kind m!"Grind tactic not found: {kind}"
      | [k] => mk k (firsts.find? k |>.getD k.toString)
      | ks => throwErrorAt kind (m!"Ambiguous grind tactic kind {kind}; it matches {ks}." ++ (← grindDisambiguationHint kind ks))
    | .inl surface =>
      let s := surface.getString
      let mut cands : Array Name := #[]
      for (k, tok) in firsts do
        if tok == s then cands := cands.push k
      match cands.toList with
      | [] => throwErrorAt surface m!"Grind tactic not found: {s}"
      | [k] => mk k s
      | ks => throwErrorAt surface (m!"The token \"{s}\" is shared by {ks}." ++ (← grindDisambiguationHint surface ks))

def Block.grindTactic (name : Name) («show» : String) (docs? : Option String) : Block where
  data := ToJson.toJson (name, «show», docs?)

@[directive]
def grindTactic : DirectiveExpanderOf TacticDocsOptions
  | opts, more => do
    let tactic ← getGrindTactic opts.name opts.allowMissing
    Doc.PointOfInterest.save (← getRef) tactic.name.toString
    let contents ←
      if opts.replace then pure #[]
      else if let some d := tactic.docs? then
        let some mdAst := MD4Lean.parse d
          | throwError "Failed to parse docstring as Markdown"
        mdAst.blocks.mapM (blockFromMarkdownWithLean [])
      else pure #[]
    let userContents ← more.mapM elabBlock
    let toShow := opts.show.getD tactic.show
    ``(Verso.Doc.Block.other (Block.grindTactic $(quote tactic.name) $(quote toShow) $(quote tactic.docs?)) #[$(contents ++ userContents),*])

open Verso.Search in
def grindTacticDomainMapper : DomainMapper := {
  className := "grind-tactic-domain",
  displayName := "Grind Tactic",
  dataToSearchables :=
    "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => ({
    searchKey: value[0].data.userName,
    address: `${value[0].address}#${value[0].id}`,
    domainId: 'Manual.tactic.grind',
    ref: value,
  }))"
  : DomainMapper }.setFont { family := .code, weight := .bold }

open Verso.Genre.Manual.Markdown in
@[block_extension Block.grindTactic]
def grindTactic.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle grindTacticDomain "Grind Interactive Tactics"
    |>.setDomainDescription grindTacticDomain "Tactics for steering `grind` interactively"
    |>.addQuickJumpMapper grindTacticDomain grindTacticDomainMapper

  traverse id info _ := do
    let .ok (name, «show», _docs?) := FromJson.fromJson? (α := Name × String × Option String) info
      | do reportError "Failed to deserialize grind tactic data"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {term := Verso.Doc.Inline.code «show»}

    modify fun st => st.saveDomainObject grindTacticDomain name.toString id
    modify fun st => st.saveDomainObjectData grindTacticDomain name.toString (json%{"userName": $«show»})

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, «show», docs?) := FromJson.fromJson? (α := Name × String × Option String) info
        | do reportError "Failed to deserialize grind tactic data"; pure .empty
      let x : Highlighted := .token ⟨.keyword (some name) none docs?, «show»⟩

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">"grind tactic"</span>
          <pre class="signature hl lean block">{{← x.toHtml (g := Verso.Genre.Manual)}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let (_name, «show», _docs?) ← FromJson.fromJson? (α := Name × String × Option String) info
    pure #[(«show», {{<code class="tactic-name">{{«show»}}</code>}})]

  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [docstringStyle]
}

def Inline.grindTactic : Inline where
  name := `Manual.Inline.grindTactic

/--
Arguments to the {grindTactic}`skip` role: an optional syntax kind that disambiguates a leading
token shared by several grind tactics.
-/
structure GrindTacticInlineArgs where
  kind? : Option Ident

def GrindTacticInlineArgs.parse [Monad m] [MonadError m] : ArgParse m GrindTacticInlineArgs :=
  GrindTacticInlineArgs.mk <$> ((some <$> .positional `kind .ident) <|> pure none)

instance [Monad m] [MonadError m] : FromArgs GrindTacticInlineArgs m where
  fromArgs := GrindTacticInlineArgs.parse

@[role grindTactic]
def grindTacticInline : RoleExpanderOf GrindTacticInlineArgs
  | {kind?}, inlines => do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $tac:str )) := arg
      | throwErrorAt arg "Expected code literal with the grind tactic name"
    let name : StrLit ⊕ Ident := match kind? with
      | some k => .inr k
      | none => .inl tac
    let tacDoc ← getGrindTactic name none
    let hl : Highlighted := .token ⟨.keyword (some tacDoc.name) none tacDoc.docs?, tac.getString⟩
    `(show Verso.Doc.Inline Verso.Genre.Manual from .other {Manual.Inline.grindTactic with data := $(quote (ToJson.toJson hl))} #[Verso.Doc.Inline.code $(quote tac.getString)])

@[inline_extension Inline.grindTactic]
def grindTacticInline.descr : InlineDescr := withHighlighting {
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [docstringStyle]
  toHtml :=
    open Verso.Output.Html Verso.Doc.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        reportError <| "Couldn't deserialize grind tactic code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml (g := Verso.Genre.Manual) "examples"
}
