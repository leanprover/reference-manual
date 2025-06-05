/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Verso.Code.Highlighted
import VersoManual.InlineLean

import Manual.Meta.Basic
import Manual.Meta.PPrint

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Verso.Code (highlightingJs)
open Verso.Code.Highlighted.WebAssets

open Verso.Genre.Manual.InlineLean.Scopes (getScopes)

open Lean Elab Parser
open Lean.Widget (TaggedText)

namespace Manual

set_option guard_msgs.diff true


@[role_expander evalPrio]
def evalPrio : RoleExpander
  | args, inlines => do
    ArgParse.done.run args
    let #[inl] := inlines
      | throwError "Expected a single code argument"
    let `(inline|code( $s:str )) := inl
      | throwErrorAt inl "Expected code literal with the priority"
    let altStr ← parserInputString s
    match runParser (← getEnv) (← getOptions) (andthen ⟨{}, whitespace⟩ priorityParser) altStr (← getFileName) with
    | .ok stx =>
      let n ← liftMacroM (Lean.evalPrio stx)
      pure #[← `(Verso.Doc.Inline.text $(quote s!"{n}"))]
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
      throwError s!"Failed to parse priority from '{s.getString}'"

@[role_expander evalPrec]
def evalPrec : RoleExpander
  | args, inlines => do
    ArgParse.done.run args
    let #[inl] := inlines
      | throwError "Expected a single code argument"
    let `(inline|code( $s:str )) := inl
      | throwErrorAt inl "Expected code literal with the precedence"
    let altStr ← parserInputString s
    match runParser (← getEnv) (← getOptions) (andthen ⟨{}, whitespace⟩ (categoryParser `prec 1024)) altStr (← getFileName) with
    | .ok stx =>
      let n ← liftMacroM (Lean.evalPrec stx)
      pure #[← `(Verso.Doc.Inline.text $(quote s!"{n}"))]
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
      throwError s!"Failed to parse precedence from '{s.getString}'"

def Block.syntax : Block where
  name := `Manual.syntax

def Block.grammar : Block where
  name := `Manual.grammar

def Inline.keywordOf : Inline where
  name := `Manual.keywordOf

def Inline.keyword : Inline where
  name := `Manual.keyword

structure FreeSyntaxConfig where
  name : Name
  «open» : Bool := true
  label : Option String := none
  title : (FileMap × TSyntaxArray `inline)

def FreeSyntaxConfig.getLabel (config : FreeSyntaxConfig) : String :=
  config.label.getD <|
    match config.name with
    | `attr => "attribute"
    | _ => "syntax"

structure SyntaxConfig extends FreeSyntaxConfig where
  namespaces : List Name := []
  aliases : List Name := []

def SyntaxConfig.getLabel (config : SyntaxConfig) : String :=
  config.toFreeSyntaxConfig.getLabel

structure KeywordOfConfig where
  ofSyntax : Ident
  parser : Option Ident

def KeywordOfConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m KeywordOfConfig :=
    KeywordOfConfig.mk <$> .positional `ofSyntax .ident <*> .named `parser .ident true

@[role_expander keywordOf]
def keywordOf : RoleExpander
  | args, inlines => do
    let ⟨kind, parser⟩ ← KeywordOfConfig.parse.run args
    let #[inl] := inlines
      | throwError "Expected a single code argument"
    let `(inline|code( $kw:str )) := inl
      | throwErrorAt inl "Expected code literal with the keyword"
    let kindName := kind.getId
    let parserName ← parser.mapM (realizeGlobalConstNoOverloadWithInfo ·)
    let env ← getEnv
    let mut catName := none
    for (cat, contents) in (Lean.Parser.parserExtension.getState env).categories do
      for (k, ()) in contents.kinds do
        if kindName == k then catName := some cat; break
      if let some _ := catName then break
    let kindDoc ← findDocString? (← getEnv) kindName
    return #[← `(Doc.Inline.other {Inline.keywordOf with data := ToJson.toJson (α := (String × Option Name × Name × Option String)) $(quote (kw.getString, catName, parserName.getD kindName, kindDoc))} #[Doc.Inline.code $kw])]

@[inline_extension keywordOf]
def keywordOf.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some <| fun goI _ info content => do
      match FromJson.fromJson? (α := (String × Option Name × Name × Option String)) info with
      | .ok (kw, cat, kind, kindDoc) =>
        -- TODO: use the presentation of the syntax in the manual to show the kind, rather than
        -- leaking the kind name here, which is often horrible. But we need more data to test this
        -- with first! Also TODO: we need docs for syntax categories, with human-readable names to
        -- show here. Use tactic index data for inspiration.
        -- For now, here's the underlying data so we don't have to fill in xrefs later and can debug.
        let tgt := (← read).linkTargets.keyword kind
        let addLink (html : Html) : Html :=
          match tgt with
          | none => html
          | some href =>
            {{<a href={{href}}>{{html}}</a>}}
        pure {{
          <span class="hl lean keyword-of">
            <code class="hover-info">
              <code>{{kind.toString}} {{cat.map (" : " ++ toString ·) |>.getD ""}}</code>
              {{if let some doc := kindDoc then
                  {{ <span class="sep"/> <code class="docstring">{{doc}}</code>}}
                else
                  .empty
              }}
            </code>
            {{addLink {{<code class="kw">{{kw}}</code>}} }}
          </span>
        }}
      | .error e =>
        Html.HtmlT.logError s!"Couldn't deserialized keywordOf data: {e}"
        content.mapM goI
  extraCss := [
r#".keyword-of .kw {
  font-weight: 500;
}
.keyword-of .hover-info {
  display: none;
}
.keyword-of .kw:hover {
  background-color: #eee;
  border-radius: 2px;
}
"#
  ]
  extraJs := [
    highlightingJs,
r#"
window.addEventListener("load", () => {
  tippy('.keyword-of.hl.lean', {
    allowHtml: true,
    /* DEBUG -- remove the space: * /
    onHide(any) { return false; },
    trigger: "click",
    // */
    maxWidth: "none",

    theme: "lean",
    placement: 'bottom-start',
    content (tgt) {
      const content = document.createElement("span");
      const state = tgt.querySelector(".hover-info").cloneNode(true);
      state.style.display = "block";
      content.appendChild(state);
      /* Render docstrings - TODO server-side */
      if ('undefined' !== typeof marked) {
          for (const d of content.querySelectorAll("code.docstring, pre.docstring")) {
              const str = d.innerText;
              const html = marked.parse(str);
              const rendered = document.createElement("div");
              rendered.classList.add("docstring");
              rendered.innerHTML = html;
              d.parentNode.replaceChild(rendered, d);
          }
      }
      content.style.display = "block";
      content.className = "hl lean popup";
      return content;
    }
  });
});
"#
  ]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]

@[role_expander keyword]
def keyword : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[inl] := inlines
      | throwError "Expected a single code argument"
    let `(inline|code( $kw:str )) := inl
      | throwErrorAt inl "Expected code literal with the keyword"

    return #[← `(Doc.Inline.other {Inline.keyword with data := Lean.Json.str $(quote kw.getString)} #[Doc.Inline.code $kw])]

@[inline_extension keyword]
def keyword.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some <| fun goI _ info content => do
      let .str kw := info
        | Html.HtmlT.logError s!"Expected a JSON string for a plain keyword, got {info}"; content.mapM goI
      pure {{<code class="plain-keyword">{{kw}}</code>}}

  extraCss := [
r#".plain-keyword {
  font-weight: 500;
}
"#
  ]


partial def many [Inhabited (f (List α))] [Applicative f] [Alternative f] (x : f α) : f (List α) :=
  ((· :: ·) <$> x <*> many x) <|> pure []

def FreeSyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m FreeSyntaxConfig :=
  FreeSyntaxConfig.mk <$>
    .positional `name .name <*>
    .namedD `open .bool true <*>
    .named `label .string true <*>
    .named `title .inlinesString false

def SyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m SyntaxConfig :=
  SyntaxConfig.mk <$> FreeSyntaxConfig.parse <*> (many (.named `namespace .name false)) <*> (many (.named `alias .resolvedName false) <* .done)

inductive GrammarTag where
  | lhs
  | rhs
  | keyword
  | literalIdent
  | nonterminal (name : Name) (docstring? : Option String)
  | fromNonterminal (name : Name) (docstring? : Option String)
  | error
  | bnf
  | comment
  | localName (name : Name) (which : Nat) (category : Name) (docstring? : Option String)
deriving Repr, FromJson, ToJson, Inhabited

open Lean.Syntax in
open GrammarTag in
instance : Quote GrammarTag where
  quote
    | .lhs => mkCApp ``GrammarTag.lhs #[]
    | .rhs => mkCApp ``GrammarTag.rhs #[]
    | .keyword => mkCApp ``GrammarTag.keyword #[]
    | .literalIdent => mkCApp ``GrammarTag.literalIdent #[]
    | nonterminal x d => mkCApp ``nonterminal #[quote x, quote d]
    | fromNonterminal x d => mkCApp ``fromNonterminal #[quote x, quote d]
    | GrammarTag.error => mkCApp ``GrammarTag.error #[]
    | bnf => mkCApp ``bnf #[]
    | comment => mkCApp ``comment #[]
    | localName name which cat d => mkCApp ``localName #[quote name, quote which, quote cat, quote d]

structure GrammarConfig where
  of : Option Name
  prec : Nat := 0

def GrammarConfig.parse [Monad m] [MonadInfoTree m] [MonadEnv m] [MonadError m] : ArgParse m GrammarConfig :=
  GrammarConfig.mk <$>
    .named `of .name true <*>
    ((·.getD 0) <$> .named `prec .nat true)


namespace FreeSyntax
declare_syntax_cat free_syntax_item
scoped syntax (name := strItem) str : free_syntax_item
scoped syntax (name := docCommentItem) docComment : free_syntax_item
scoped syntax (name := identItem) ident : free_syntax_item
scoped syntax (name := namedIdentItem) ident noWs ":" noWs ident : free_syntax_item
scoped syntax (name := antiquoteItem) "$" noWs (ident <|> "_") noWs ":" noWs ident ("?" <|> "*" <|> "+")? : free_syntax_item
scoped syntax (name := modItem) "(" free_syntax_item+ ")" noWs ("?" <|> "*" <|> "+") : free_syntax_item
scoped syntax (name := checked) Term.dynamicQuot : free_syntax_item

declare_syntax_cat free_syntax
scoped syntax (name := rule) free_syntax_item* : free_syntax

scoped syntax (name := embed) "free{" free_syntax_item* "}" : term

declare_syntax_cat syntax_sep

open Lean Elab Command in
run_cmd do
  for i in [5:40] do
    let sep := Syntax.mkStrLit <| String.mk (List.replicate i '*')
    let cmd ← `(scoped syntax (name := $(mkIdent s!"sep{i}".toName)) $sep:str : syntax_sep)
    elabCommand cmd
  pure ()

declare_syntax_cat free_syntaxes
scoped syntax (name := done) free_syntax : free_syntaxes
scoped syntax (name := more) free_syntax syntax_sep free_syntaxes : free_syntaxes

/-- Translate freely specified syntax into what the output of the Lean parser would have been -/
partial def decodeMany (stx : Syntax) : List Syntax :=
  match stx.getKind with
  | ``done => [stx[0]]
  | ``more => stx[0] :: decodeMany stx[2]
  | _ => [stx]

mutual
  /-- Translate freely specified syntax into what the output of the Lean parser would have been -/
  partial def decode (stx : Syntax) : Syntax :=
    (Syntax.copyHeadTailInfoFrom · stx) <|
    Id.run <| stx.rewriteBottomUp fun stx' =>
      match stx'.getKind with
      | ``strItem =>
        .atom .none (⟨stx'[0]⟩ : StrLit).getString
      | ``embed =>
        stx'[1]
      | ``checked =>
        let quote := stx'[0]
        -- 0: `( ; 1: parser ; 2: | ; 3: content ; 4: )
        quote[3]
      | _ => stx'

  /-- Find instances of freely specified syntax in the result of parsing checked syntax, and decode them -/
  partial def decodeIn (stx : Syntax) : Syntax :=
    Id.run <| stx.rewriteBottomUp fun
      | `(term|free{$stxs*}) => .node .none `null (stxs.map decode)
      | other => other
end


end FreeSyntax

namespace Meta.PPrint.Grammar
def antiquoteOf : Name → Option Name
  | .str n "antiquot" => pure n
  | _ => none

def nonTerm : Name → String
  | .str x "pseudo" => nonTerm x
  | .str _ x => x
  | x => x.toString

def empty : Syntax → Bool
  | .node _ _ #[] => true
  | _ => false

def isEmpty : Format → Bool
  | .nil => true
  | .tag _ f => isEmpty f
  | .append f1 f2 => isEmpty f1 && isEmpty f2
  | .line => false
  | .group f _ => isEmpty f
  | .nest _ f => isEmpty f
  | .align .. => false
  | .text str => str.isEmpty

def isCompound [Monad m] (f : Format) : TagFormatT GrammarTag m Bool := do
  if (← beginsWithBnfParen f <&&> endsWithBnfParen f) then return false
  match f with
  | .nil => pure false
  | .tag _ f => isCompound f
  | .append f1 f2 =>
    isCompound f1 <||> isCompound f2
  | .line => pure true
  | .group f _ => isCompound f
  | .nest _ f => isCompound f
  | .align .. => pure false
  | .text str =>
    pure <| str.any fun c => c.isWhitespace || c ∈ ['"', ':', '+', '*', ',', '\'', '(', ')', '[', ']']
where
  beginsWithBnfParen : Format → TagFormatT GrammarTag m Bool
    | .nil => pure false
    | .tag k (.text s) => do
      if (← get).tags.find? k matches some .bnf then
        return "(".isPrefixOf s
      else pure false
    | .tag _ f => beginsWithBnfParen f
    | .append f1 f2 =>
      if isEmpty f1 then beginsWithBnfParen f2 else beginsWithBnfParen f1
    | .line => pure false
    | .group f _ => beginsWithBnfParen f
    | .nest _ f => beginsWithBnfParen f
    | .align _ => pure false
    | .text .. => pure false

  endsWithBnfParen : Format → TagFormatT GrammarTag m Bool
    | .nil => pure false
    | .tag k (.text s) => do
      if (← get).tags.find? k matches some .bnf then
        return ")".isPrefixOf s
      else pure false
    | .tag _ f => endsWithBnfParen f
    | .append f1 f2 =>
      if isEmpty f2 then endsWithBnfParen f1 else endsWithBnfParen f2
    | .line => pure false
    | .group f _ => endsWithBnfParen f
    | .nest _ f => endsWithBnfParen f
    | .align _ => pure false
    | .text .. => pure false

partial def kleeneLike (mod : String) (f : Format) : TagFormatT GrammarTag DocElabM Format := do
  if (← isCompound f) then return (← tag .bnf "(") ++ f ++ (← tag .bnf s!"){mod}")
  else return f ++ (← tag .bnf mod)


def kleene := kleeneLike "*"

def perhaps := kleeneLike "?"

def lined (ws : String) : Format :=
  Format.line.joinSep (ws.splitOn "\n")

def noTrailing (info : SourceInfo) : Option SourceInfo :=
  match info with
  | .original leading p1 _ p2 => some <| .original leading p1 "".toSubstring p2
  | .synthetic .. => some info
  | .none => none

def removeTrailing? : Syntax → Option Syntax
  | .node .none k children => do
    for h : i in [0:children.size] do
      have : children.size > 0 := by
        let ⟨_, _, _⟩ := h
        simp_all +zetaDelta
        omega
      if let some child' := removeTrailing? children[children.size - i - 1] then
        return .node .none k (children.set (children.size - i - 1) child')
    failure
  | .node info k children =>
    noTrailing info |>.map (.node · k children)
  | .atom info str => noTrailing info |>.map (.atom · str)
  | .ident info str x pre => noTrailing info |>.map (.ident · str x pre)
  | .missing => failure

def removeTrailing (stx : Syntax) : Syntax := removeTrailing? stx |>.getD stx

def infoWrap (info : SourceInfo) (doc : Format) : Format :=
  if let .original leading _ trailing _ := info then
    lined leading.toString ++ doc ++ lined trailing.toString
  else doc

def infoWrapTrailing (info : SourceInfo) (doc : Format) : Format :=
  if let .original _ _ trailing _ := info then
    doc ++ lined trailing.toString
  else doc

def infoWrap2 (info1 : SourceInfo) (info2 : SourceInfo) (doc : Format) : Format :=
  let pre := if let .original leading _ _ _ := info1 then lined leading.toString else .nil
  let post := if let .original _ _ trailing _ := info2 then lined trailing.toString else .nil
  pre ++ doc ++ post

def longestSuffix (strs : Array String) : String := Id.run do
  if h : strs.size = 0 then ""
  else
    let mut suff := strs[0]

    repeat
      if suff == "" then return ""
      let suff' := suff
      for s in strs do
        unless s.dropSuffix? suff |>.isSome do
          suff := suff.drop 1
      if suff' == suff then return suff'
    return ""

/-- info: "abc" -/
#guard_msgs in
#eval longestSuffix #["abc", "abc"]
/-- info: "bc" -/
#guard_msgs in
#eval longestSuffix #["abc", "bc"]
/-- info: "abc" -/
#guard_msgs in
#eval longestSuffix #["abc"]
/-- info: "" -/
#guard_msgs in
#eval longestSuffix #[]
/-- info: "" -/
#guard_msgs in
#eval longestSuffix #["abc", "def"]
/-- info: "" -/
#guard_msgs in
#eval longestSuffix #["abc", "def", "abc"]

def longestPrefix (strs : Array String) : String := Id.run do
  if h : strs.size = 0 then ""
  else
    let mut pref := strs[0]

    repeat
      if pref == "" then return ""
      let pref' := pref
      for s in strs do
        unless s.dropPrefix? pref |>.isSome do
          pref := pref.dropRight 1
      if pref' == pref then return pref'
    return ""

/-- info: "abc" -/
#guard_msgs in
#eval longestPrefix #["abc", "abc"]
/-- info: "" -/
#guard_msgs in
#eval longestPrefix #["abc", "bc"]
/-- info: "ab" -/
#guard_msgs in
#eval longestPrefix #["abc", "ab"]
/-- info: "abc" -/
#guard_msgs in
#eval longestPrefix #["abc"]
/-- info: "" -/
#guard_msgs in
#eval longestPrefix #[]
/-- info: "" -/
#guard_msgs in
#eval longestPrefix #["abc", "def"]
/-- info: "" -/
#guard_msgs in
#eval longestPrefix #["abc", "def", "abc"]
/-- info: "a" -/
#guard_msgs in
#eval longestPrefix #["abc", "aaa"]

/-- Does this syntax take up zero source code? -/
partial def isEmptySyntax : Syntax → Bool
  | .node info _ args => isEmptyInfo info && args.all isEmptySyntax
  | .atom info s => isEmptyInfo info && s.isEmpty
  | .ident .. => false
  | .missing => false
where
  isEmptyInfo
    | .original leading _ trailing _ => leading.isEmpty && trailing.isEmpty
    | _ => true

def removeLeadingString (string : String) : Syntax → Syntax
  | .missing => .missing
  | .atom info str => .atom (remove info).2 str
  | .ident info x raw pre => .ident (remove info).2 x raw pre
  | .node info k args => Id.run do
    let (string', info') := remove info
    let mut args' := #[]
    for h : i in [0 : args.size] do

      if isEmptySyntax args[i] then
        args' := args'.push args[i]
      else
        let this := removeLeadingString string' args[i]
        args' := args'.push this
        args' := args' ++ args.extract (i + 1) args.size
        break

    .node info' k args'
where
  remove : SourceInfo → String × SourceInfo
  | .original leading pos trailing pos' =>
    (string.take leading.toString.length, .original (leading.drop string.length) pos trailing pos')
  | other => (string, other)

partial def removeTrailingString (string : String) : Syntax → Syntax :=
  fun stx =>
  if string.isEmpty then stx else
  match stx with

  | .missing => .missing
  | .atom info str => .atom (remove info).2 str
  | .ident info x raw pre => .ident (remove info).2 x raw pre
  | .node info k args => Id.run do
    let (string', info') := remove info
    let mut args' := #[]
    for h : i in [0 : args.size] do
      let j := args.size - (i + 1)
      have : i < args.size := by get_elem_tactic
      have : j < args.size := by omega
      if isEmptySyntax args[j] then
        -- The parser doesn't presently put source info here, so it's expedient to not check for
        -- whitespace on this source info. If this ever changes, update this code.
        args' := args'.push args[j]
      else
        let this := removeTrailingString string' args[j]
        args' := args'.push this
        args' := args.extract 0 j ++ args'.reverse
        break
    .node info' k args'
where
  remove : SourceInfo → String × SourceInfo
  | .original leading pos trailing pos' =>
    (string.dropRight trailing.toString.length, .original leading pos (trailing.dropRight string.length) pos')
  | other => (string, other)

/--
Extracts the common leading and trailing whitespaces from an array of syntaxes.

This is to be used when rendering choice nodes in a grammar, so they don't have redundant whitespace.
-/
def commonWs (stxs : Array Syntax) : String × Array Syntax × String :=
  let allLeading := stxs.map Syntax.getHeadInfo |>.map fun
    | .none => ""
    | .synthetic .. => ""
    | .original leading _ _ _ => leading.toString

  let allTrailing := stxs.map Syntax.getTailInfo |>.map fun
    | .none => ""
    | .synthetic .. => ""
    | .original _ _ trailing _ => trailing.toString

  let pref := longestPrefix allLeading
  let suff := longestSuffix allTrailing
  let stxs := stxs.map fun stx =>
    removeLeadingString pref (removeTrailingString suff stx)


  (pref, stxs, suff)

open Lean.Parser.Command in
/--
A set of parsers that exist to wrap only a single keyword and should be rendered as the keyword
itself.
-/
-- TODO make this extensible in the manual itself
def keywordParsers : List (Name × String) :=
  [(``«private», "private"), (``«protected», "protected"), (``«partial», "partial"), (``«nonrec», "nonrec")]

open StateT (lift) in
partial def production (which : Nat) (stx : Syntax) : StateT (NameMap (Name × Option String)) (TagFormatT GrammarTag DocElabM) Format := do
  match stx with
  | .atom info str => infoWrap info <$> lift (tag GrammarTag.keyword str)
  | .missing => lift <| tag GrammarTag.error "<missing>"
  | .ident info _ x _ =>
    -- If the identifier is the name of something that works like a syntax category, then treat it as a nonterminal
    if x ∈ [`ident, `atom, `num] || (Lean.Parser.parserExtension.getState (← getEnv)).categories.contains x then
      let d? ← findDocString? (← getEnv) x
      -- TODO render markdown
      let tok ←
        lift <| tag (.nonterminal x d?) <|
          match x with
          | .str x' "pseudo" => x'.toString
          | _ => x.toString
      return infoWrap info tok
    else
      -- If it's not a syntax category, treat it as the literal identifier (e.g. `config` before `:=` in tactic configurations)
      let tok ←
        lift <| tag .literalIdent x.toString
      return infoWrap info tok
  | .node info k args => do
    infoWrap info <$>
    match k, antiquoteOf k, args with
    | `many.antiquot_suffix_splice, _, #[starred, star] =>
      infoWrap2 starred.getHeadInfo star.getTailInfo <$> (production which starred >>= lift ∘ kleene)
    | `optional.antiquot_suffix_splice, _, #[questioned, star] => -- See also the case for antiquoted identifiers below
      infoWrap2 questioned.getHeadInfo star.getTailInfo <$> (production which questioned >>= lift ∘ perhaps)
    | `sepBy.antiquot_suffix_splice, _, #[starred, star] =>
      let starStr :=
        match star with
        | .atom _ s => s
        | _ => ",*"
      infoWrap2 starred.getHeadInfo star.getTailInfo <$> (production which starred >>= lift ∘ kleeneLike starStr)
    | `many.antiquot_scope, _, #[dollar, _null, _brack, contents, _brack2, .atom info star] =>
      infoWrap2 dollar.getHeadInfo info <$> (production which contents >>= lift ∘ kleene)
    | `optional.antiquot_scope, _, #[dollar, _null, _brack, contents, _brack2, .atom info _star] =>
      infoWrap2 dollar.getHeadInfo info <$> (production which contents >>= lift ∘ perhaps)
    | `sepBy.antiquot_scope, _, #[dollar, _null, _brack, contents, _brack2, .atom info star] =>
      infoWrap2 dollar.getHeadInfo info <$> (production which contents >>= lift ∘ kleeneLike star)
    | `choice, _, opts => do
      -- Extract the common whitespace here. Otherwise, something like `∀ $_ $_*, $_` might render as
      -- `∀ (binder  | thing )(binder  | thing )*, term`
      -- instead of
      -- `∀ (binder | thing) (binder | thing)* , term`
      let (pre, opts, post) := commonWs opts
      return pre ++
        (← lift <| tag .bnf "(") ++ (" " ++ (← lift <| tag .bnf "|") ++ " ").joinSep
          (← opts.toList.mapM (production which)) ++ (← lift <| tag .bnf ")") ++
        post
    | ``Attr.simple, _, #[.ident kinfo _ name _, other] => do
      return infoWrap info (infoWrap kinfo (← lift <| tag .keyword name.toString) ++ (← production which other))
    | ``FreeSyntax.docCommentItem, _, _ =>
      match stx[0][1] with
      | .atom _ val => do
        let mut str := val.extract 0 (val.endPos - ⟨2⟩)
        let mut contents : Format := .nil
        let mut inVar : Bool := false
        while !str.isEmpty do
          if inVar then
            let pre := str.takeWhile (· != '}')
            str := str.drop (pre.length + 1)
            let x := pre.trim.toName
            if let some (c, d?) := (← get).find? x then
              contents := contents ++ (← lift <| tag (.localName x which c d?) x.toString)
            else
              contents := contents ++ x.toString
            inVar := false
          else
            let pre := str.takeWhile (· != '{')
            str := str.drop (pre.length + 1)
            contents := contents ++ pre
            inVar := true

        lift <| tag .comment contents
      | _ => lift <| tag .comment "error extracting comment..."
    | ``FreeSyntax.identItem, _, _ => do
      let cat := stx[0]
      if let .ident info' _ c _ := cat then
        let d? ← findDocString? (← getEnv) c
        -- TODO render markdown
        let tok ←
          lift <| tag (.nonterminal c d?) <|
            match c with
            | .str c' "pseudo" => c'.toString
            | _ => c.toString
        return infoWrap info <| infoWrap info' tok
      return "_" ++ (← lift <| tag .bnf ":") ++ (← production which cat)
    | ``FreeSyntax.namedIdentItem, _, _ => do
      let name := stx[0]
      let cat := stx[2]
      if let .ident info _ x _ := name then
        if let .ident info' _ c _ := cat then
          let d? ← findDocString? (← getEnv) c
          modify (·.insert x (c, d?))
          return (← lift <| tag (.localName x which c d?) x.toString) ++ (← lift <| tag .bnf ":") ++ (← production which cat)
      return "_" ++ (← lift <| tag .bnf ":") ++ (← production which cat)
    | ``FreeSyntax.antiquoteItem, _, _ => do
      let _name := stx[1]
      let cat := stx[3]
      let qual := stx[4].getOptional?
      let content ← production which cat
      match qual with
      | some (.atom info op)
      -- The parser creates token.«+» (etc) nodes for these, which should ideally be looked through
      | some (.node _ _ #[.atom info op]) => infoWrapTrailing info <$> lift (kleeneLike op content)
      | _ => pure content
    | ``FreeSyntax.modItem, _, _ => do
      let stxs := stx[1]
      let mod := stx[3]
      let content ← production which stxs
      match mod with
      | .atom info op
      -- The parser creates token.«+» (etc) nodes for these, which should ideally be looked through
      | .node _ _ #[.atom info op] => infoWrapTrailing info <$> lift (kleeneLike op content)
      | _ => pure content
    | _, some k', #[a, b, c, d] => do
      --
      let doc? ← findDocString? (← getEnv) k'
      let last :=
        if let .node _ _ #[] := d then c else d

      if let some kw := keywordParsers.lookup k' then
        return infoWrap2 a.getHeadInfo last.getTailInfo (← lift (tag .keyword kw))

      -- Optional quasiquotes $NAME? where kind FOO is expected look like this:
      --   k := FOO.antiquot
      --   k' := FOO
      --   args := #["$", [], `NAME?, []]
      if let (.atom _ "$", .node _ nullKind #[], .ident _ _ x _) := (a, b, c) then
        if x.toString.back == '?' then
          return infoWrap2 a.getHeadInfo last.getTailInfo ((← lift <| tag (.nonterminal k' doc?) (nonTerm k')) ++ (← lift <| tag .bnf "?"))

      infoWrap2 a.getHeadInfo last.getTailInfo <$> lift (tag (.nonterminal k' doc?) (nonTerm k'))
    | _, _, _ => do
      let mut out := Format.nil
      for a in args do
        out := out ++ (← production which a)
      let doc? ← findDocString? (← getEnv) k
      lift <| tag (.fromNonterminal k doc?) out

end Meta.PPrint.Grammar

def categoryOf (env : Environment) (kind : Name) : Option Name := do
  for (catName, contents) in (Lean.Parser.parserExtension.getState env).categories do
    for (k, ()) in contents.kinds do
      if kind == k then return catName
  failure

open Manual.Meta.PPrint Grammar in
def getBnf (config : FreeSyntaxConfig) (isFirst : Bool) (stxs : List Syntax) : DocElabM (TaggedText GrammarTag) := do
    let bnf ← TagFormatT.run <| do
      let lhs ← renderLhs config isFirst
      let prods ←
        match stxs with
        | [] => pure []
        | [p] => pure [(← renderProd config isFirst 0 p)]
        | p::ps =>
          let hd := indentIfNotOpen config.open (← renderProd config isFirst 0 p)
          let tl ← ps.mapIdxM fun i s => renderProd config false i s
          pure <| hd :: tl
      pure <| lhs ++ (← tag .rhs (Format.nest 4 (.join (prods.map (.line ++ ·)))))
    return bnf.render (w := 5)
where
  indentIfNotOpen (isOpen : Bool) (f : Format) : Format :=
    if isOpen then f else "  " ++ f

  renderLhs (config : FreeSyntaxConfig) (isFirst : Bool) : TagFormatT GrammarTag DocElabM Format := do
    let cat := (categoryOf (← getEnv) config.name).getD config.name
    let d? ← findDocString? (← getEnv) cat
    let mut bnf : Format := (← tag (.nonterminal cat d?) s!"{nonTerm cat}") ++ " " ++ (← tag .bnf "::=")
    if config.open || (!config.open && !isFirst) then
      bnf := bnf ++ (" ..." : Format)
    tag .lhs bnf

  renderProd (config : FreeSyntaxConfig) (isFirst : Bool) (which : Nat) (stx : Syntax) : TagFormatT GrammarTag DocElabM Format := do
    let stx := removeTrailing stx
    let bar := (← tag .bnf "|") ++ " "
    if !config.open && isFirst then
      production which stx |>.run' {}
    else
      return bar ++ .nest 2 (← production which stx |>.run' {})

def testGetBnf (config : FreeSyntaxConfig) (isFirst : Bool) (stxs : List Syntax) : TermElabM String := do
  let (tagged, _) ← getBnf config isFirst stxs |>.run (← ``(Manual)) (.const ``Manual []) {} {partContext := ⟨⟨default, default, default, default, default⟩, default⟩}
  pure tagged.stripTags

namespace Tests
open FreeSyntax

def selectedParser : Parser := leading_parser
  ident >> "| " >> incQuotDepth (parserOfStack 1)


elab "#test_syntax" arg:selectedParser : command => do
  let bnf ← Command.liftTermElabM (testGetBnf {name := (TSyntax.mk arg.raw[0]).getId, title := (FileMap.ofString "", #[])} true [arg.raw[2]])
  logInfo bnf

/--
info: term ::= ...
    | term < term
-/
#guard_msgs in
#test_syntax term | $x < $y

/--
info: term ::= ...
    | term term*
-/
#guard_msgs in
#test_syntax term | $e $e*

/--
info: term ::= ...
    | term [(term term),*]
-/
#guard_msgs in
#test_syntax term | $e [$[$e $e],*]


elab "#test_free_syntax" x:ident arg:free_syntaxes : command => do
  let bnf ← Command.liftTermElabM (testGetBnf {name := x.getId, title := (FileMap.ofString "", #[])} true (FreeSyntax.decodeMany arg |>.map FreeSyntax.decode))
  logInfo bnf

/--
info: go ::= ...
    | thing term
    | foo
-/
#guard_msgs in
#test_free_syntax go
  "thing" term
  *****
  "foo"

example := () -- Keep it from eating the next doc comment

/--
info: antiquot ::= ...
    | $ident(:ident)?suffix?
    | $( term )(:ident)?suffix?
-/
#guard_msgs in
#test_free_syntax antiquot
  "$"ident(":"ident)?(suffix)?
  *******
  "$(" term ")"(":"ident)?(suffix)?


end Tests

instance : MonadWithReaderOf Core.Context DocElabM := inferInstanceAs (MonadWithReaderOf Core.Context (ReaderT DocElabContext (ReaderT PartElabM.State (StateT DocElabM.State TermElabM))))

def withOpenedNamespace (ns : Name) (act : DocElabM α) : DocElabM α :=
  try
    pushScope
    let mut openDecls := (← readThe Core.Context).openDecls
    for n in (← resolveNamespaceCore ns) do
      openDecls := .simple n [] :: openDecls
      activateScoped n
    withTheReader Core.Context ({· with openDecls := openDecls}) act
  finally
    popScope

def withOpenedNamespaces (nss : List Name) (act : DocElabM α) : DocElabM α :=
  (nss.foldl (init := id) fun acc ns => withOpenedNamespace ns ∘ acc) act


inductive SearchableTag where
  | metavar
  | keyword
  | literalIdent
  | ws
deriving DecidableEq, Ord, Repr

open Lean.Syntax in
instance : Quote SearchableTag where
  quote
    | .metavar => mkCApp ``SearchableTag.metavar #[]
    | .keyword => mkCApp ``SearchableTag.keyword #[]
    | .literalIdent => mkCApp ``SearchableTag.literalIdent #[]
    | .ws => mkCApp ``SearchableTag.ws #[]

def SearchableTag.toKey : SearchableTag → String
  | .metavar => "meta"
  | .keyword => "keyword"
  | .literalIdent => "literalIdent"
  | .ws => "ws"

def SearchableTag.toJson : SearchableTag → Json := Json.str ∘ SearchableTag.toKey

instance : ToJson SearchableTag where
  toJson := SearchableTag.toJson

def SearchableTag.fromJson? : Json → Except String SearchableTag
  | .str "meta" => pure .metavar
  | .str "keyword" => pure .keyword
  | .str "literalIdent" => pure .literalIdent
  | .str "ws" => pure .ws
  | other =>
    let s :=
      match other with
      | .str s => s.quote
      | .arr .. => "array"
      | .obj .. => "object"
      | .num .. => "number"
      | .bool b => toString b
      | .null => "null"
    throw s!"Expected 'meta', 'keyword', 'literalIdent', or 'ws', got {s}"

instance : FromJson SearchableTag where
  fromJson? := SearchableTag.fromJson?


def searchableJson (ss : Array (SearchableTag × String)) : Json :=
  .arr <| ss.map fun (tag, str) =>
    json%{"kind": $tag.toKey, "string": $str}

partial def searchable (cat : Name) (txt : TaggedText GrammarTag) : Array (SearchableTag × String) :=
  (go txt *> get).run' #[] |> fixup
where
  dots : SearchableTag × String := (.metavar, "…")
  go : TaggedText GrammarTag → StateM (Array (SearchableTag × String)) String
    | .text s => do
      ws s
      pure s
    | .append xs => do
      for ⟨x, _⟩ in xs.attach do
        discard <| go x
      pure ""
    | .tag .keyword x => do
      let x' ← go x
      modify (·.push (.keyword, x'))
      pure x'
    | .tag .lhs _ => pure ""
    | .tag (.nonterminal (.str (.str .anonymous "token") _) _) (.text txt) => do
      let txt := txt.trim
      modify (·.push (.keyword, txt))
      pure txt
    | .tag (.nonterminal ``Lean.Parser.Attr.simple ..) txt => do
      let kw := txt.stripTags.trim
      modify (·.push (.keyword, kw))
      pure kw
    | .tag (.nonterminal ..) _ => do
      ellipsis
      pure dots.2
    | .tag .literalIdent (.text s) => do
      modify (·.push (.literalIdent, s))
      return s
    | .tag .bnf (.text s) => do
      let s := s.trim
      modify fun st => Id.run do
        match s with
        -- Suppress leading |
        | "|" => if st.isEmpty then return st
        -- Don't add repetition modifiers after ... or to an empty output
        | "*" | "?" | ",*" =>
          if let some _ := suffixMatches #[(· == dots)] st then return st
          if st.isEmpty then return st
        -- Don't parenthesize just "..."
        | ")" | ")?" | ")*" =>
          if let some st' := suffixMatches #[(· == (.metavar, "(")) , (· == dots)] st then return st'.push dots
        | _ => pure ()
        return st.push (.metavar, s)
      pure s
    | .tag other txt => do
      go txt
  fixup (s : Array (SearchableTag × String)) : Array (SearchableTag × String) :=
    let s := s.popWhile (·.1 == .ws) -- Remove trailing whitespace
    match cat with
    | `command => Id.run do
      -- Drop leading ellipses from commands
      for h : i in [0:s.size] do
        if s[i] ∉ [dots, (.metavar, "?"), (.ws, " ")] then return s.extract i s.size
      return s
    | _ => s
  ws (s : String) : StateM (Array (SearchableTag × String)) Unit := do
    if !s.isEmpty && s.all (·.isWhitespace) then
      modify fun st =>
        if st.isEmpty then st
        else if st.back?.map (·.1 == .ws) |>.getD true then st
        else st.push (.ws, " ")

  suffixMatches (suffix : Array (SearchableTag × String → Bool)) (st : (Array (SearchableTag × String))) : Option (Array (SearchableTag × String)) := do
    let mut suffix := suffix
    for h : i in [0 : st.size] do
      match suffix.back? with
      | none => return st.extract 0 (st.size - i)
      | some p =>
        have : st.size > 0 := by
          let ⟨_, h, _⟩ := h
          simp_all +zetaDelta
          omega
        let curr := st[st.size - (i + 1)]
        if curr.1 matches .ws then continue
        if p curr then
          suffix := suffix.pop
        else throw ()
    if suffix.isEmpty then some #[] else none

  ellipsis : StateM (Array (SearchableTag × String)) Unit := do
    modify fun st =>
      -- Don't push ellipsis onto ellipsis
      if let some _ := suffixMatches #[(· == dots)] st then st
      -- Don't alternate ellipses
      else if let some st' := suffixMatches #[(· == dots), (· == (.metavar, "|"))] st then st'.push dots
      else st.push dots


/-- info: some #[] -/
#guard_msgs in
#eval searchable.suffixMatches #[] #[]

/-- info: some #[(Manual.SearchableTag.keyword, "aaa")] -/
#guard_msgs in
#eval searchable.suffixMatches #[(· == (.metavar, "(")), (· == searchable.dots)] #[(.keyword, "aaa"),(.metavar, "("), (.ws, " "),(.metavar, "…")]

/-- info: some #[(Manual.SearchableTag.keyword, "aaa")] -/
#guard_msgs in
#eval searchable.suffixMatches #[(· == searchable.dots)] #[(.keyword, "aaa"),(.metavar, "…"), (.ws, " ")]

/-- info: some #[] -/
#guard_msgs in
#eval searchable.suffixMatches #[(· == searchable.dots)] #[(.metavar, "…"), (.ws, " ")]

/-- info: some #[] -/
#guard_msgs in
#eval searchable.suffixMatches #[(· == searchable.dots)] #[(.metavar, "…")]

open Manual.Meta.PPrint Grammar in
/--
Display actual Lean syntax, validated by the parser.
-/
@[directive_expander «syntax»]
def «syntax» : DirectiveExpander
  | args, blocks => do
    let config ← SyntaxConfig.parse.run args

    let title ← do
      let (fm, t) := config.title
      DocElabM.withFileMap fm <| t.mapM elabInline

    let env ← getEnv
    let titleString := inlinesToString env (config.title.snd)

    let mut content := #[]
    let mut firstGrammar := true
    for b in blocks do
      match isGrammar? b with
      | some (nameStx, argsStx, contents) =>
        let grm ← elabGrammar nameStx config firstGrammar argsStx contents
        content := content.push grm
        firstGrammar := false
      | _ =>
        content := content.push <| ← elabBlock b

    Doc.PointOfInterest.save (← getRef) titleString
      (selectionRange := (← getRef)[0])

    pure #[← `(Doc.Block.other {Block.syntax with data := ToJson.toJson (α := Option String × Name × String × Option Tag × Array Name) ($(quote titleString), $(quote config.name), $(quote config.getLabel), none, $(quote config.aliases.toArray))} #[Block.para #[$(title),*], $content,*])]
where
  isGrammar? : Syntax → Option (Syntax × Array Syntax × StrLit)
  | `(block|``` $nameStx:ident $argsStx* | $contents ```) =>
    if nameStx.getId == `grammar then some (nameStx, argsStx, contents) else none
  | _ => none

  elabGrammar nameStx config isFirst (argsStx : Array Syntax) (str : TSyntax `str) := do
    let args ← parseArgs <| argsStx.map (⟨·⟩)
    let {of, prec} ← GrammarConfig.parse.run args
    let config : SyntaxConfig :=
      if let some n := of then
        {name := n, «open» := false, title := config.title}
      else config
    let altStr ← parserInputString str
    let p := andthen ⟨{}, whitespace⟩ <| andthen {fn := (fun _ => (·.pushSyntax (mkIdent config.name)))} (parserOfStack 0)
    let scope := (← Verso.Genre.Manual.InlineLean.Scopes.getScopes).head!

    withOpenedNamespace `Manual.FreeSyntax <| withOpenedNamespaces config.namespaces <| do
      match runParser (← getEnv) (← getOptions) p altStr (← getFileName) (prec := prec) (openDecls := scope.openDecls) with
      | .ok stx =>
        Doc.PointOfInterest.save stx stx.getKind.toString
        let bnf ← getBnf config.toFreeSyntaxConfig isFirst [FreeSyntax.decode stx]
        let searchTarget := searchable config.name bnf

        Hover.addCustomHover nameStx s!"Kind: {stx.getKind}\n\n````````\n{bnf.stripTags}\n````````"


        let blockStx ← `(Block.other {Block.grammar with data := ToJson.toJson (($(quote stx.getKind), $(quote bnf), searchableJson $(quote searchTarget)) : Name × TaggedText GrammarTag × Json)} #[])
        pure (blockStx)
      | .error es =>
        for (pos, msg) in es do
          log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
        throwError "Parse errors prevented grammar from being processed."

open Manual.Meta.PPrint Grammar in
/--
Display free-form syntax that isn't validated by Lean's parser.

Here, the name is simply for reference, and should not exist as a syntax kind.

The grammar of free-form syntax items is:
 * strings - atoms
 * doc_comments - inline comments
 * ident - instance of nonterminal
 * $ident:ident('?'|'*'|'+')? - named quasiquote (the name is rendered, and can be referred to later)
 * '(' ITEM+ ')'('?'|'*'|'+')? - grouped sequence (potentially modified/repeated)
 * ` `( `ident|...) - embedding parsed Lean that matches the specified parser

They can be separated by a row of `**************`
-/
@[directive_expander freeSyntax]
def freeSyntax : DirectiveExpander
  | args, blocks => do
    let config ← FreeSyntaxConfig.parse.run args

    let title ← do
      let (fm, t) := config.title
      DocElabM.withFileMap fm <| t.mapM elabInline
    let env ← getEnv
    let titleString := inlinesToString env config.title.snd

    let mut content := #[]
    let mut firstGrammar := true
    for b in blocks do
      match isGrammar? b with
      | some (nameStx, argsStx, contents) =>
        let grm ← elabGrammar nameStx config firstGrammar argsStx contents
        content := content.push grm
        firstGrammar := false
      | _ =>
        content := content.push <| ← elabBlock b
    pure #[← `(Doc.Block.other {Block.syntax with data := ToJson.toJson (α := Option String × Name × String × Option Tag × Array Name) ($(quote titleString), $(quote config.name), $(quote config.getLabel), none, #[])} #[Doc.Block.para #[$(title),*], $content,*])]
where
  isGrammar? : Syntax → Option (Syntax × Array Syntax × StrLit)
  | `(block|```$nameStx:ident $argsStx* | $contents:str ```) =>
    if nameStx.getId == `grammar then some (nameStx, argsStx, contents) else none
  | _ => none

  elabGrammar nameStx config isFirst (argsStx : Array Syntax) (str : TSyntax `str) := do
    let args ← parseArgs <| argsStx.map (⟨·⟩)
    let () ← ArgParse.done.run args
    let altStr ← parserInputString str
    let p := andthen ⟨{}, whitespace⟩ <| categoryParser `free_syntaxes 0
    withOpenedNamespace `Manual.FreeSyntax do
      match runParser (← getEnv) (← getOptions) p altStr (← getFileName) (prec := 0) with
      | .ok stx =>
        let bnf ← getBnf config isFirst (FreeSyntax.decodeMany stx |>.map FreeSyntax.decode)
        Hover.addCustomHover nameStx s!"Kind: {stx.getKind}\n\n````````\n{bnf.stripTags}\n````````"
        -- TODO: searchable instead of Json.arr #[]
        `(Block.other {Block.grammar with data := ToJson.toJson (($(quote stx.getKind), $(quote bnf), Json.arr #[]) : Name × TaggedText GrammarTag × Json)} #[])
      | .error es =>
        for (pos, msg) in es do
          log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
        throwError "Parse errors prevented grammar from being processed."


@[block_extension «syntax»]
def syntax.descr : BlockDescr where
  traverse id data contents := do
    if let .ok (title, kind, label, tag, aliases) := FromJson.fromJson? (α := Option String × Name × String × Option Tag × Array Name) data then
      if tag.isSome then
        pure none
      else
        let path := (← read).path
        let tag ← Verso.Genre.Manual.externalTag id path kind.toString
        pure <| some <| Block.other {Block.syntax with id := some id, data := toJson (title, kind, label, some tag, aliases)} contents
    else
      logError "Couldn't deserialize kind name for syntax block"
      pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html Verso.Doc.Html in
    some <| fun goI goB id data content => do
      let (titleString, label) ←
        match FromJson.fromJson? (α := Option String × Name × String × Option Tag × Array Name) data with
        | .ok (titleString, _, label, _, _) => pure (titleString, label)
        | .error e =>
          HtmlT.logError s!"Failed to deserialize syntax docs: {e} from {data}"
          pure (none, "syntax")
      let xref ← HtmlT.state
      let attrs := xref.htmlId id
      let (descr, content) ←
        if let some (Block.para titleInlines) := content[0]? then
          pure (titleInlines, content.drop 1)
        else
          HtmlT.logError s!"Didn't get a paragraph for the title inlines in syntax description {titleString}"
          pure (#[], content)

      let titleHtml ←  descr.mapM goI
      let titleHtml := if titleHtml.isEmpty then .empty else {{<span class="title">{{titleHtml}}</span>}}

      pure {{
        <div class="namedocs" {{attrs}}>
          <span class="label">{{label}}</span>
          {{titleHtml}}
          <div class="text">
            {{← content.mapM goB}}
          </div>
        </div>
      }}
  extraCss := [
r#"
.namedocs .title {
  font-family: var(--verso-structure-font-family);
  font-size: 1.1rem;
  margin-top: 0;
  margin-left: 1rem;
  margin-right: 1.5rem;
  margin-bottom: 0.75rem;
  display: inline-block;
}
"#
]

def grammar := ()

def grammarCss :=
r#".grammar .keyword {
  font-weight: 500 !important;
}

.grammar {
  padding-top: 0.25rem;
  padding-bottom: 0.25rem;
}

.grammar .comment {
  font-style: italic;
  font-family: var(--verso-text-font-family);
  /* TODO add background and text colors to Verso theme, then compute a background here */
  background-color: #fafafa;
  border: 1px solid #f0f0f0;
}

.grammar .local-name {
  font-family: var(--verso-code-font-family);
  font-style: italic;
}

.grammar .nonterminal {
  font-style: italic;
}
.grammar .nonterminal > .hover-info, .grammar .from-nonterminal > .hover-info, .grammar .local-name > .hover-info {
  display: none;
}
.grammar .active {
  background-color: #eee;
  border-radius: 2px;
}
.grammar a {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
"#

def grammarJs :=
r#"
window.addEventListener("load", () => {
  const innerProps = {
    onShow(inst) { console.log(inst); },
    onHide(inst) { console.log(inst); },
    content(tgt) {
      const content = document.createElement("span");
      const state = tgt.querySelector(".hover-info").cloneNode(true);
      state.style.display = "block";
      content.appendChild(state);
      /* Render docstrings - TODO server-side */
      if ('undefined' !== typeof marked) {
          for (const d of content.querySelectorAll("code.docstring, pre.docstring")) {
              const str = d.innerText;
              const html = marked.parse(str);
              const rendered = document.createElement("div");
              rendered.classList.add("docstring");
              rendered.innerHTML = html;
              d.parentNode.replaceChild(rendered, d);
          }
      }
      content.style.display = "block";
      content.className = "hl lean popup";
      return content;
    }
  };
  const outerProps = {
    allowHtml: true,
    theme: "lean",
    placement: 'bottom-start',
    maxWidth: "none",
    delay: 100,
    moveTransition: 'transform 0.2s ease-out',
    onTrigger(inst, event) {
      const ref = event.currentTarget;
      const block = ref.closest('.hl.lean');
      block.querySelectorAll('.active').forEach((i) => i.classList.remove('active'));
      ref.classList.add("active");
    },
    onUntrigger(inst, event) {
      const ref = event.currentTarget;
      const block = ref.closest('.hl.lean');
      block.querySelectorAll('.active').forEach((i) => i.classList.remove('active'));
    }
  };
  tippy.createSingleton(tippy('pre.grammar.hl.lean .nonterminal.documented, pre.grammar.hl.lean .from-nonterminal.documented, pre.grammar.hl.lean .local-name.documented', innerProps), outerProps);
});
"#

open Verso.Output Html HtmlT in
private def nonTermHtmlOf (kind : Name) (doc? : Option String) (rendered : Html) : HtmlT Manual (ReaderT ExtensionImpls IO) Html := do
  let xref ← match (← state).resolveDomainObject syntaxKindDomain kind.toString with
    | .error _ =>
      pure none
    | .ok (path, id) =>
      pure (some s!"{String.join <| path.toList.map (s!"/{·}")}#{id}")
  let addXref := fun html =>
    match xref with
    | none => html
    | some tgt => {{<a href={{tgt}}>{{html}}</a>}}

  return addXref <|
    match doc? with
    | some doc => {{
        <span class="nonterminal documented" {{#[("data-kind", kind.toString)]}}>
          <code class="hover-info"><code class="docstring">{{doc}}</code></code>
          {{rendered}}
        </span>
      }}
    | none => {{
        <span class="nonterminal" {{#[("data-kind", kind.toString)]}}>
          {{rendered}}
        </span>
      }}


structure GrammarHtmlContext where
  skipKinds : NameSet := NameSet.empty.insert nullKind
  lookingAt : Option Name := none

namespace GrammarHtmlContext

def default : GrammarHtmlContext := {}

def skip (k : Name) (ctx : GrammarHtmlContext) : GrammarHtmlContext :=
  {ctx with skipKinds := ctx.skipKinds.insert k}

def look (k : Name) (ctx : GrammarHtmlContext) : GrammarHtmlContext :=
  if ctx.skipKinds.contains k then ctx else {ctx with lookingAt := some k}

def noLook (ctx : GrammarHtmlContext) : GrammarHtmlContext :=
  {ctx with lookingAt := none}

end GrammarHtmlContext

open Verso.Output Html in
abbrev GrammarHtmlM := ReaderT GrammarHtmlContext (HtmlT Manual (ReaderT ExtensionImpls IO))

private def lookingAt (k : Name) : GrammarHtmlM α → GrammarHtmlM α := withReader (·.look k)

private def notLooking : GrammarHtmlM α → GrammarHtmlM α := withReader (·.noLook)

def productionDomain : Name := `Manual.Syntax.production

open Verso.Output Html in
@[block_extension grammar]
partial def grammar.descr : BlockDescr where
  traverse id info _ := do
    if let .ok (k, _, searchable) := FromJson.fromJson? (α := Name × TaggedText GrammarTag × Json) info then
      let path ← (·.path) <$> read
      let _ ← Verso.Genre.Manual.externalTag id path k.toString
      modify fun st => st.saveDomainObject syntaxKindDomain k.toString id

      let prodName := s!"{k} {searchable}"
      modify fun st => st.saveDomainObject productionDomain prodName id
      modify fun st => st.saveDomainObjectData productionDomain prodName (json%{"category": null, "kind": $k.toString, "forms": $searchable})
    else
      logError "Couldn't deserialize grammar info during traversal"
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI _goB id info _ => do
      match FromJson.fromJson? (α := Name × TaggedText GrammarTag × Json) info with
      | .ok (kind, bnf, _searchable) =>
        let t ← match (← read).traverseState.externalTags.get? id with
          | some (_, t) => pure t.toString
          | _ => Html.HtmlT.logError s!"Couldn't get HTML ID for grammar of {kind}" *> pure ""
        pure {{
          <pre class="grammar hl lean" data-lean-context="--grammar" id={{t}}>
            {{← bnfHtml bnf |>.run (GrammarHtmlContext.default.skip kind) }}
          </pre>
        }}
      | .error e =>
        Html.HtmlT.logError s!"Couldn't deserialize BNF: {e}"
        pure .empty
  extraCss := [grammarCss, "#toc .split-toc > ol .syntax .keyword { font-family: var(--verso-code-font-family); font-weight: 600; }"]
  extraJs := [highlightingJs, grammarJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  localContentItem _ json _ := open Verso.Output.Html in do
    if let .arr #[_, .arr #[_, .arr toks]] := json then
      let toks ← toks.mapM fun v => do
          let Json.str str ← v.getObjVal? "string"
            | throw "Not a string"
          let .str k ← v.getObjVal? "kind"
            | throw "Not a string"
          pure (str, {{<span class={{k}}>{{str}}</span>}})
      let (strs, toks) := toks.unzip
      if strs == #["…"] || strs == #["..."] then
        -- Dont' add the item if it'd be useless for navigating the page
        pure #[]
      else
        pure #[(String.join strs.toList, {{<span class="syntax">{{toks}}</span>}})]
    else throw s!"Expected a Json array shaped like [_, [_, [tok, ...]]], got {json}"
where

  bnfHtml : TaggedText GrammarTag → GrammarHtmlM Html
  | .text str => pure <| .text true str
  | .tag t txt => tagHtml t (bnfHtml txt)
  | .append txts => .seq <$> txts.mapM bnfHtml


  tagHtml (t : GrammarTag) (go : GrammarHtmlM Html) : GrammarHtmlM Html :=
    match t with
    | .lhs | .rhs => go
    | .bnf => ({{<span class="bnf">{{·}}</span>}}) <$> notLooking go
    | .comment => ({{<span class="comment">{{·}}</span>}}) <$> notLooking go
    | .error => ({{<span class="err">{{·}}</span>}}) <$> notLooking go
    | .literalIdent => ({{<span class="literal-ident">{{·}}</span>}}) <$> notLooking go
    | .keyword => do
      let inner ← go
      if let some k := (← read).lookingAt then
        unless k == nullKind do
          if let some tgt := (← HtmlT.state (genre := Manual) (m := ReaderT ExtensionImpls IO)).linkTargets.keyword k then
            return {{<a href={{tgt}}><span class="keyword">{{inner}}</span></a>}}
      return {{<span class="keyword">{{inner}}</span>}}
    | .nonterminal k doc? => do
      let inner ← notLooking go
      nonTermHtmlOf k doc? inner
    | .fromNonterminal k none => do
      let inner ← lookingAt k go
      return {{<span class="from-nonterminal" {{#[("data-kind", k.toString)]}}>{{inner}}</span>}}
    | .fromNonterminal k (some doc) => do
      let inner ← lookingAt k go
      return {{
        <span class="from-nonterminal documented" {{#[("data-kind", k.toString)]}}>
          <code class="hover-info"><code class="docstring">{{doc}}</code></code>
          {{inner}}
        </span>
      }}
    | .localName x n cat doc? => do
      let doc :=
        match doc? with
        | none => .empty
        | some d => {{<span class="sep"/><code class="docstring">{{d}}</code>}}
      let inner ← notLooking go
      -- The "token" class below triggers binding highlighting
      return {{
        <span class="local-name token documented" {{#[("data-kind", cat.toString)]}} data-binding=s!"grammar-var-{n}-{x}">
          <code class="hover-info"><code>{{x.toString}} " : " {{cat.toString}}</code>{{doc}}</code>
          {{inner}}
        </span>
      }}


def Inline.syntaxKind : Inline where
  name := `Manual.syntaxKind

@[role_expander syntaxKind]
def syntaxKind : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $syntaxKindName:str )) := arg
      | throwErrorAt arg "Expected code literal with the syntax kind name"
    let kName := syntaxKindName.getString.toName
    let id : Ident := mkIdentFrom syntaxKindName kName
    let k ← try realizeGlobalConstNoOverloadWithInfo id catch _ => pure kName
    let doc? ← findDocString? (← getEnv) k
    return #[← `(Doc.Inline.other {Inline.syntaxKind with data := ToJson.toJson (α := Name × String × Option String) ($(quote k), $(quote syntaxKindName.getString), $(quote doc?))} #[Doc.Inline.code $(quote k.toString)])]


@[inline_extension syntaxKind]
def syntaxKind.inlinedescr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [grammarCss]
  extraJs := [highlightingJs, grammarJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ data inls => do
      match FromJson.fromJson? (α := Name × String × Option String) data with
      | .error e =>
        Html.HtmlT.logError s!"Couldn't deserialize syntax kind name: {e}"
        return {{<code>{{← inls.mapM goI}}</code>}}
      | .ok (k, showAs, doc?) =>
        return {{
          <code class="grammar">
            {{← nonTermHtmlOf k doc? showAs}}
          </code>
        }}
