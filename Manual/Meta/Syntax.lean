/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Verso.Code.Highlighted

import Manual.Meta.Basic
import Manual.Meta.PPrint

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Verso.Code (highlightingJs)
open Verso.Code.Highlighted.WebAssets


open Lean Elab Parser
open Lean.Widget (TaggedText)

namespace Manual

set_option guard_msgs.diff true

-- run_elab do
--   let xs := _
--   let stx ← `(command|universe $xs*)
--   dbg_trace stx

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

structure FreeSyntaxConfig where
  name : Name
  «open» : Bool := true
  label : String := "syntax"
  title : Option String := none

structure SyntaxConfig extends FreeSyntaxConfig where
  aliases : List Name := []

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
    let some c := catName
      | throwErrorAt kind s!"Unknown syntax kind {kindName}"
    let kindDoc ← findDocString? (← getEnv) kindName
    return #[← `(Doc.Inline.other {Inline.keywordOf with data := ToJson.toJson (α := (String × Name × Name × Option String)) $(quote (kw.getString, c, parserName.getD kindName, kindDoc))} #[Doc.Inline.code $kw])]

@[inline_extension keywordOf]
def keywordOf.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some <| fun goI _ info content => do
      match FromJson.fromJson? (α := (String × Name × Name × Option String)) info with
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
              <code>{{kind.toString}} " : " {{cat.toString}}</code>
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

partial def many [Inhabited (f (List α))] [Applicative f] [Alternative f] (x : f α) : f (List α) :=
  ((· :: ·) <$> x <*> many x) <|> pure []

def FreeSyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m FreeSyntaxConfig :=
  FreeSyntaxConfig.mk <$>
    .positional `name .name <*>
    ((·.getD true) <$> (.named `open .bool true)) <*>
    ((·.getD "syntax") <$> .named `label .string true) <*>
    .named `title .string true

def SyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SyntaxConfig :=
  SyntaxConfig.mk <$> FreeSyntaxConfig.parse <*> (many (.named `alias .resolvedName false) <* .done)

inductive GrammarTag where
  | keyword
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
    | keyword => mkCApp ``keyword #[]
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

def isCompound : Format → Bool
  | .nil => false
  | .tag _ f => isCompound f
  | .append f1 f2 =>
    isCompound f1 || isCompound f2
  | .line => true
  | .group f _ => isCompound f
  | .nest _ f => isCompound f
  | .align .. => false
  | .text str =>
    str.any fun c => c.isWhitespace || c ∈ ['"', ':', '+', '*', ',', '\'', '(', ')', '[', ']']

partial def kleeneLike (mod : String) (f : Format) : TagFormatT GrammarTag DocElabM Format := do
  if isCompound f then return (← tag .bnf "(") ++ f ++ (← tag .bnf s!"){mod}")
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
        let ⟨_, _, _⟩ := h; simp_all +zetaDelta; omega
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

open StateT (lift) in
partial def production (which : Nat) (stx : Syntax) : StateT (NameMap (Name × Option String)) (TagFormatT GrammarTag DocElabM) Format := do
  match stx with
  | .atom info str => infoWrap info <$> lift (tag GrammarTag.keyword str)
  | .missing => lift <| tag GrammarTag.error "<missing>"
  | .ident info _ x _ =>
    let d? ← findDocString? (← getEnv) x
    -- TODO render markdown
    let tok ←
      lift <| tag (.nonterminal x d?) <|
        match x with
        | .str x' "pseudo" => x'.toString
        | _ => x.toString
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
      return (← lift <| tag .bnf "(") ++ (" " ++ (← lift <| tag .bnf "|") ++ " ").joinSep (← opts.toList.mapM (production which)) ++ (← lift <| tag .bnf ")")
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
          let tl ← ps.enum.mapM fun (i, s) => renderProd config false i s
          pure <| hd :: tl
      pure <| lhs ++ Format.nest 4 (.join (prods.map (.line ++ ·)))
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
    return bnf

  renderProd (config : FreeSyntaxConfig) (isFirst : Bool) (which : Nat) (stx : Syntax) : TagFormatT GrammarTag DocElabM Format := do
    let stx := removeTrailing stx
    let bar := (← tag .bnf "|") ++ " "
    if !config.open && isFirst then
      production which stx |>.run' {}
    else
      return bar ++ .nest 2 (← production which stx |>.run' {})

def testGetBnf (config : FreeSyntaxConfig) (isFirst : Bool) (stxs : List Syntax) : TermElabM String := do
  let (tagged, _) ← getBnf config isFirst stxs |>.run {} {partContext := ⟨⟨default, default, default, default, default⟩, default⟩}
  pure tagged.stripTags

namespace Tests
open FreeSyntax

def selectedParser : Parser := leading_parser
  ident >> "| " >> incQuotDepth (parserOfStack 1)


elab "#test_syntax" arg:selectedParser : command => do
  let bnf ← Command.liftTermElabM (testGetBnf {name := (TSyntax.mk arg.raw[0]).getId} true [arg.raw[2]])
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
  let bnf ← Command.liftTermElabM (testGetBnf {name := x.getId} true (FreeSyntax.decodeMany arg |>.map FreeSyntax.decode))
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

instance : MonadWithReaderOf Core.Context DocElabM := inferInstanceAs (MonadWithReaderOf Core.Context (ReaderT PartElabM.State (StateT DocElabM.State TermElabM)))

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


open Manual.Meta.PPrint Grammar in
/--
Display actual Lean syntax, validated by the parser.
-/
@[directive_expander «syntax»]
def «syntax» : DirectiveExpander
  | args, blocks => do
    let config ← SyntaxConfig.parse.run args

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

    Doc.PointOfInterest.save (← getRef) (config.title.getD config.name.toString)
      (selectionRange := (← getRef)[0])

    pure #[← `(Doc.Block.other {Block.syntax with data := ToJson.toJson (α := Option String × Name × String × Option Tag × Array Name) ($(quote config.title), $(quote config.name), $(quote config.label), none, $(quote config.aliases.toArray))} #[$content,*])]
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
        {name := n, «open» := false}
      else config
    let altStr ← parserInputString str
    let p := andthen ⟨{}, whitespace⟩ <| andthen {fn := (fun _ => (·.pushSyntax (mkIdent config.name)))} (parserOfStack 0)
    withOpenedNamespace `Manual.FreeSyntax do
      match runParser (← getEnv) (← getOptions) p altStr (← getFileName) (prec := prec) with
      | .ok stx =>
        Doc.PointOfInterest.save stx stx.getKind.toString
        let bnf ← getBnf config.toFreeSyntaxConfig isFirst [FreeSyntax.decode stx]
        Hover.addCustomHover nameStx s!"Kind: {stx.getKind}\n\n````````\n{bnf.stripTags}\n````````"

        `(Block.other {Block.grammar with data := ToJson.toJson (($(quote stx.getKind), $(quote bnf)) : Name × TaggedText GrammarTag)} #[])
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
    pure #[← `(Doc.Block.other {Block.syntax with data := ToJson.toJson (α := Option String × Name × String × Option Tag × Array Name) ($(quote config.title), $(quote config.name), $(quote config.label), none, #[])} #[$content,*])]
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
        `(Block.other {Block.grammar with data := ToJson.toJson (($(quote stx.getKind), $(quote bnf)) : Name × TaggedText GrammarTag)} #[])
      | .error es =>
        for (pos, msg) in es do
          log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
        throwError "Parse errors prevented grammar from being processed."


@[block_extension «syntax»]
def syntax.descr : BlockDescr where
  traverse id data contents := do
    if let .ok (title, kind, label, tag, aliases) := FromJson.fromJson? (α := Option String × Name × String × Option Tag × Array Name) data then
      modify fun st => st.saveDomainObject syntaxKindDomain kind.toString id
      for a in aliases do
        modify fun st => st.saveDomainObject syntaxKindDomain a.toString id
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
    some <| fun _ goB id data content => do
      let (title, label) ←
        match FromJson.fromJson? (α := Option String × Name × String × Option Tag × Array Name) data with
        | .ok (title, _, label, _, _) => pure (title, label)
        | .error e =>
          HtmlT.logError s!"Failed to deserialize syntax docs: {e} from {data}"
          pure (none, "syntax")
      let xref ← HtmlT.state
      let attrs := xref.htmlId id
      pure {{
        <div class="namedocs" {{attrs}}>
          <span class="label">{{label}}</span>
          {{if let some t := title then {{<span class="title">{{t}}</span>}} else .empty}}
          <div class="text">
            {{← content.mapM goB}}
          </div>
        </div>
      }}
  extraCss := [
r#"
.namedocs .title {
  font-family: var(--verso-structure-font-family);
  font-size: larger;
  margin-top: 0;
  margin-left: 1.5em;
  margin-right: 1.5em;
  margin-bottom: 0.5em;
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

open Verso.Output Html in
@[block_extension grammar]
partial def grammar.descr : BlockDescr where
  traverse id info _ := do
    if let .ok (k, _) := FromJson.fromJson? (α := Name × TaggedText GrammarTag) info then
      let path ← (·.path) <$> read
      let _ ← Verso.Genre.Manual.externalTag id path k.toString
      modify fun st => st.saveDomainObject syntaxKindDomain k.toString id
    else
      logError "Couldn't deserialize grammar info during traversal"
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI _goB id info _ => do
      match FromJson.fromJson? (α := Name × TaggedText GrammarTag) info with
      | .ok bnf =>
        let t ← match (← read).traverseState.externalTags.get? id with
          | some (_, t) => pure t.toString
          | _ => Html.HtmlT.logError s!"Couldn't get HTML ID for grammar of {bnf.1}" *> pure ""
        pure {{
          <pre class="grammar hl lean" data-lean-context="--grammar" id={{t}}>
            {{← bnfHtml bnf.2 |>.run (GrammarHtmlContext.default.skip bnf.1) }}
          </pre>
        }}
      | .error e =>
        Html.HtmlT.logError s!"Couldn't deserialize BNF: {e}"
        pure .empty
  extraCss := [grammarCss]
  extraJs := [highlightingJs, grammarJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
where

  bnfHtml : TaggedText GrammarTag → GrammarHtmlM Html
  | .text str => pure <| .text true str
  | .tag t txt => tagHtml t (bnfHtml txt)
  | .append txts => .seq <$> txts.mapM bnfHtml


  tagHtml (t : GrammarTag) (go : GrammarHtmlM Html) : GrammarHtmlM Html :=
    match t with
    | .bnf => ({{<span class="bnf">{{·}}</span>}}) <$> notLooking go
    | .comment => ({{<span class="comment">{{·}}</span>}}) <$> notLooking go
    | .error => ({{<span class="err">{{·}}</span>}}) <$> notLooking go
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
