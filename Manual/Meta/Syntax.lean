/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public meta import Manual.Meta.Basic
public import Manual.Meta.Syntax.Grammar
public meta import Manual.Meta.Syntax.Grammar
public meta import Verso.Doc.Elab.Block
public meta import Verso.Doc.Elab.Inline
public meta import Verso.Doc.PointOfInterest
public import VersoManual.Basic
import Verso.Doc.Elab
import VersoManual.HighlightedCode
meta import VersoManual.InlineLean.Scopes
public import Verso.Doc.Elab
public meta import VersoManual.InlineLean.Scopes
import VersoManual.InlineLean -- shake: keep

public section

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open Verso.Code (highlightingJs)
open Verso.Code.Highlighted.WebAssets
open Lean.Doc.Syntax

open Verso.Genre.Manual.InlineLean.Scopes (getScopes)

open Lean Elab Parser
open Lean.Widget (TaggedText)

namespace Manual

set_option guard_msgs.diff true


@[role_expander evalPrio]
meta def evalPrio : RoleExpander
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
meta def evalPrec : RoleExpander
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

structure KeywordOfConfig where
  ofSyntax : Ident
  parser : Option Ident

meta def KeywordOfConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m KeywordOfConfig :=
    KeywordOfConfig.mk <$> .positional `ofSyntax .ident <*> .named `parser .ident true

@[role_expander keywordOf]
meta def keywordOf : RoleExpander
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
    return #[← `(Inline.other {Inline.keywordOf with data := ToJson.toJson (α := (String × Option Name × Name × Option String)) $(quote (kw.getString, catName, parserName.getD kindName, kindDoc))} #[Inline.code $kw])]

@[inline_extension keywordOf]
def keywordOf.descr : InlineDescr := withHighlighting {
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
        let tgt := (← read).linkTargets.keyword kind none
        let addLink (html : Html) : Html :=
          match tgt[0]? with
          | none => html
          | some l =>
            {{<a href={{l.href}}>{{html}}</a>}}
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
        reportError s!"Couldn't deserialized keywordOf data: {e}"
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
}

@[role_expander keyword]
meta def keyword : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[inl] := inlines
      | throwError "Expected a single code argument"
    let `(inline|code( $kw:str )) := inl
      | throwErrorAt inl "Expected code literal with the keyword"

    return #[← `(Inline.other {Inline.keyword with data := Lean.Json.str $(quote kw.getString)} #[Inline.code $kw])]

@[inline_extension keyword]
def keyword.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output Html in
    some <| fun goI _ info content => do
      let .str kw := info
        | reportError s!"Expected a JSON string for a plain keyword, got {info}"; content.mapM goI
      pure {{<code class="plain-keyword">{{kw}}</code>}}

  extraCss := [
r#".plain-keyword {
  font-weight: 500;
}
"#
  ]


meta section

partial def many [Inhabited (f (List α))] [Applicative f] [Alternative f] (x : f α) : f (List α) :=
  ((· :: ·) <$> x <*> many x) <|> pure []

def FreeSyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m FreeSyntaxConfig :=
  FreeSyntaxConfig.mk <$>
    .positional `name .name <*>
    .flag `open true <*>
    .named `label .string true <*>
    .named `title .inlinesString false

def SyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m SyntaxConfig :=
  SyntaxConfig.mk <$> FreeSyntaxConfig.parse <*> (many (.named `namespace .name false)) <*> (many (.named `alias .resolvedName false) <* .done)

end

structure GrammarConfig where
  of : Option Name
  prec : Nat := 0

meta def GrammarConfig.parse [Monad m] [MonadInfoTree m] [MonadEnv m] [MonadError m] : ArgParse m GrammarConfig :=
  GrammarConfig.mk <$>
    .named `of .name true <*>
    ((·.getD 0) <$> .named `prec .nat true)

namespace Tests
open FreeSyntax

meta def selectedParser : Parser := leading_parser
  ident >> "| " >> incQuotDepth (parserOfStack 1)


elab "#test_syntax" arg:selectedParser : command => do
  let bnf ← Command.liftTermElabM (testGetBnf { name := (TSyntax.mk arg.raw[0]).getId, title := #[] } true [arg.raw[2]])
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
  let bnf ← Command.liftTermElabM (testGetBnf { name := x.getId, title := #[] } true (FreeSyntax.decodeMany arg |>.map FreeSyntax.decode))
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
open Manual.Meta.PPrint Grammar in
/--
Display actual Lean syntax, validated by the parser.
-/
@[directive_expander «syntax»]
meta def «syntax» : DirectiveExpander
  | args, blocks => do
    let config ← SyntaxConfig.parse.run args

    let title ← config.title.mapM elabInline

    let env ← getEnv
    let titleString := inlinesToString env (config.title)

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

    Doc.PointOfInterest.save (← getRef) titleString (selectionSyntax? := some (← getRef)[0])

    pure #[← `(Block.other {Block.syntax with data := ToJson.toJson (α := Option String × Name × String × Option Tag × Array Name) ($(quote titleString), $(quote config.name), $(quote config.getLabel), none, $(quote config.aliases.toArray))} #[Block.para #[$(title),*], $content,*])]
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
meta def freeSyntax : DirectiveExpander
  | args, blocks => do
    let config ← FreeSyntaxConfig.parse.run args

    let title ← config.title.mapM elabInline
    let env ← getEnv
    let titleString := inlinesToString env config.title

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
    pure #[← `(Block.other {Block.syntax with data := ToJson.toJson (α := Option String × Name × String × Option Tag × Array Name) ($(quote titleString), $(quote config.name), $(quote config.getLabel), none, #[])} #[Block.para #[$(title),*], $content,*])]
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
      reportError "Couldn't deserialize kind name for syntax block"
      pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html Verso.Doc.Html in
    some <| fun goI goB id data content => do
      let (titleString, label) ←
        match FromJson.fromJson? (α := Option String × Name × String × Option Tag × Array Name) data with
        | .ok (titleString, _, label, _, _) => pure (titleString, label)
        | .error e =>
          reportError s!"Failed to deserialize syntax docs: {e} from {data}"
          pure (none, "syntax")
      let xref ← HtmlT.state
      let attrs := xref.htmlId id
      let (descr, content) ←
        if let some (Block.para titleInlines) := content[0]? then
          pure (titleInlines, content.drop 1)
        else
          reportError s!"Didn't get a paragraph for the title inlines in syntax description {titleString}"
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
private def nonTermHtmlOf (kind : Name) (doc? : Option String) (rendered : Html) : HtmlT Manual (ReaderT Multi.AllRemotes (ReaderT ExtensionImpls (BuildLogT IO))) Html := do
  let xref ← match (← state).resolveDomainObject syntaxKindDomain kind.toString with
    | .error _ =>
      pure none
    | .ok dest =>
      pure (some dest.link)
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
abbrev GrammarHtmlM := ReaderT GrammarHtmlContext (HtmlT Manual (ReaderT Multi.AllRemotes (ReaderT ExtensionImpls (BuildLogT IO))))

private def lookingAt (k : Name) : GrammarHtmlM α → GrammarHtmlM α := withReader (·.look k)

private def notLooking : GrammarHtmlM α → GrammarHtmlM α := withReader (·.noLook)

def productionDomain : Name := `Manual.Syntax.production

open Verso.Search in
private def productionDomainMapper : DomainMapper where
  displayName := "Syntax"
  className := "syntax-domain"
  dataToSearchables :=
  "(domainData) =>
  Object.entries(domainData.contents).map(([key, value]) => ({
    // TODO find a way to not include the “meta” parts of the string
    // in the search key here, but still display them
    searchKey: value[0].data.forms.map(v => v.string).join(''),
    address: `${value[0].address}#${value[0].id}`,
    domainId: 'Manual.Syntax.production',
    ref: value,
  }))"

open Verso.Output Html in
@[block_extension grammar]
partial def grammar.descr : BlockDescr := withHighlighting {
  init s := s.addQuickJumpMapper productionDomain (productionDomainMapper.setFont { family := .code })

  traverse id info _ := do
    if let .ok (k, _, searchable) := FromJson.fromJson? (α := Name × TaggedText GrammarTag × Json) info then
      let path ← (·.path) <$> read
      let _ ← Verso.Genre.Manual.externalTag id path k.toString
      modify fun st => st.saveDomainObject syntaxKindDomain k.toString id

      let prodName := s!"{k} {searchable}"
      modify fun st => st.saveDomainObject productionDomain prodName id
      modify fun st => st.saveDomainObjectData productionDomain prodName (json%{"category": null, "kind": $k.toString, "forms": $searchable})
    else
      reportError "Couldn't deserialize grammar info during traversal"
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _goI _goB id info _ => do
      match FromJson.fromJson? (α := Name × TaggedText GrammarTag × Json) info with
      | .ok (kind, bnf, _searchable) =>
        let t ← match (← read).traverseState.externalTags.get? id with
          | some dest => pure dest.htmlId.toString
          | _ => reportError s!"Couldn't get HTML ID for grammar of {kind}" *> pure ""
        pure {{
          <pre class="grammar hl lean" data-lean-context="--grammar" id={{t}}>
            {{← bnfHtml bnf |>.run (GrammarHtmlContext.default.skip kind) }}
          </pre>
        }}
      | .error e =>
        reportError s!"Couldn't deserialize BNF: {e}"
        pure .empty
  extraCss := [grammarCss, "#toc .split-toc > ol .syntax .keyword { font-family: var(--verso-code-font-family); font-weight: 600; }"]
  extraJs := [grammarJs]
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
        -- Don't add the item if it'd be useless for navigating the page
        pure #[]
      else
        pure #[(String.join strs.toList, {{<span class="syntax">{{toks}}</span>}})]
    else throw s!"Expected a Json array shaped like [_, [_, [tok, ...]]], got {json}"
}
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
          if let some tgt := ((← HtmlT.state (genre := Manual) (m := ReaderT Multi.AllRemotes (ReaderT ExtensionImpls (BuildLogT IO)))).localTargets.keyword k none)[0]? then
            return {{<a href={{tgt.href}}><span class="keyword">{{inner}}</span></a>}}
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
meta def syntaxKind : RoleExpander
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
    return #[← `(Inline.other {Inline.syntaxKind with data := ToJson.toJson (α := Name × String × Option String) ($(quote k), $(quote syntaxKindName.getString), $(quote doc?))} #[Inline.code $(quote k.toString)])]


@[inline_extension syntaxKind]
def syntaxKind.inlinedescr : InlineDescr := withHighlighting {
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [grammarCss]
  extraJs := [grammarJs]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ data inls => do
      match FromJson.fromJson? (α := Name × String × Option String) data with
      | .error e =>
        reportError s!"Couldn't deserialize syntax kind name: {e}"
        return {{<code>{{← inls.mapM goI}}</code>}}
      | .ok (k, showAs, doc?) =>
        return {{
          <code class="grammar">
            {{← nonTermHtmlOf k doc? showAs}}
          </code>
        }}
}
