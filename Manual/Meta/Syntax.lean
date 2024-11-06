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

-- run_elab do
--   let xs := _
--   let stx ← `(command|universe $xs*)
--   dbg_trace stx

-- TODO upstream this to enable cross-reference generation the usual Verso way
def syntaxKindDomain := `Manual.syntaxKind

@[role_expander evalPrio]
def evalPrio : RoleExpander
  | args, inlines => do
    ArgParse.done.run args
    let #[inl] := inlines
      | throwError "Expected a single code argument"
    let `(inline|code{ $s:str }) := inl
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

def Block.syntax : Block where
  name := `Manual.syntax

def Block.grammar : Block where
  name := `Manual.grammar

def Inline.keywordOf : Inline where
  name := `Manual.keywordOf

structure SyntaxConfig where
  name : Name
  «open» : Bool := true
  label : String := "syntax"
  title : Option String := none
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
    let `(inline|code{ $kw:str }) := inl
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
    open Verso.Output.Html in
    some <| fun goI _ info content => do
      match FromJson.fromJson? (α := (String × Name × Name × Option String)) info with
      | .ok (kw, cat, kind, kindDoc) =>
        -- TODO: use the presentation of the syntax in the manual to show the kind, rather than
        -- leaking the kind name here, which is often horrible. But we need more data to test this
        -- with first! Also TODO: we need docs for syntax categories, with human-readable names to
        -- show here. Use tactic index data for inspiration.
        -- For now, here's the underlying data so we don't have to fill in xrefs later and can debug.
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
            <code class="kw">{{kw}}</code>
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

def SyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SyntaxConfig :=
  SyntaxConfig.mk <$>
    .positional `name .name <*>
    ((·.getD true) <$> (.named `open .bool true)) <*>
    ((·.getD "syntax") <$> .named `label .string true) <*>
    .named `title .string true <*>
    (many (.named `alias .resolvedName false) <* .done)

inductive GrammarTag where
  | keyword
  | nonterminal (name : Name) (docstring? : Option String)
  | fromNonterminal (name : Name) (docstring? : Option String)
  | error
  | bnf
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

structure GrammarConfig where
  of : Option Name
  prec : Nat := 0

def GrammarConfig.parse [Monad m] [MonadInfoTree m] [MonadEnv m] [MonadError m] : ArgParse m GrammarConfig :=
  GrammarConfig.mk <$>
    .named `of .name true <*>
    ((·.getD 0) <$> .named `prec .nat true)


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

partial def kleeneLike (mod : String) : Syntax → Format → TagFormatT GrammarTag DocElabM Format
  | .atom .., f
  | .ident .., f
  | .missing, f => do return f ++ (← tag .bnf mod)
  | .node _ _ args, f => do
    let nonempty := args.filter (!empty ·)
    if h : nonempty.size = 1 then
      kleeneLike mod nonempty[0] f
    else
      return (← tag .bnf "(") ++ f ++ (← tag .bnf s!"){mod}")

def kleene := kleeneLike "*"

def perhaps := kleeneLike "?"

def lined (ws : String) : Format :=
  Format.line.joinSep (ws.splitOn "\n")


def infoWrap (info : SourceInfo) (doc : Format) : Format :=
  if let .original leading _ trailing _ := info then
    lined leading.toString ++ doc ++ lined trailing.toString
  else doc

def infoWrap2 (info1 : SourceInfo) (info2 : SourceInfo) (doc : Format) : Format :=
  let pre := if let .original leading _ _ _ := info1 then lined leading.toString else .nil
  let post := if let .original _ _ trailing _ := info2 then lined trailing.toString else .nil
  pre ++ doc ++ post

partial def production (stx : Syntax) : TagFormatT GrammarTag DocElabM Format := do
  match stx with
  | .atom info str => infoWrap info <$> tag .keyword str
  | .missing => tag .error "<missing>"
  | .ident info _ x _ =>
    let d? ← findDocString? (← getEnv) x
    -- TODO render markdown
    let tok ←
      tag (.nonterminal x d?) <|
        match x with
        | .str x' "pseudo" => x'.toString
        | _ => x.toString
    return infoWrap info tok
  | .node info k args => do
    infoWrap info <$>
    match k, antiquoteOf k, args with
    | `many.antiquot_suffix_splice, _, #[starred, star] =>
      infoWrap2 starred.getHeadInfo star.getTailInfo <$> (production starred >>= kleene starred)
    | `optional.antiquot_suffix_splice, _, #[questioned, star] => -- See also the case for antiquoted identifiers below
      infoWrap2 questioned.getHeadInfo star.getTailInfo <$> (production questioned >>= perhaps questioned)
    | `sepBy.antiquot_suffix_splice, _, #[starred, star] =>
      infoWrap2 starred.getHeadInfo star.getTailInfo <$> (production starred >>= kleeneLike ",*" starred)
    | `many.antiquot_scope, _, #[dollar, _null, _brack, contents, _brack2, .atom info star] =>
      infoWrap2 dollar.getHeadInfo info <$> (production contents >>= kleene contents)
    | `optional.antiquot_scope, _, #[dollar, _null, _brack, contents, _brack2, .atom info _star] =>
      infoWrap2 dollar.getHeadInfo info <$> (production contents >>= perhaps contents)
    | `sepBy.antiquot_scope, _, #[dollar, _null, _brack, contents, _brack2, .atom info _star] =>
      infoWrap2 dollar.getHeadInfo info <$> (production contents >>= kleeneLike ",*" contents)
    | `choice, _, opts => do
      return (← tag .bnf "(") ++ (" " ++ (← tag .bnf "|") ++ " ").joinSep (← opts.toList.mapM production) ++ (← tag .bnf ")")
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
          return infoWrap2 a.getHeadInfo last.getTailInfo ((← tag (.nonterminal k' doc?) (nonTerm k')) ++ (← tag .bnf "?"))

      infoWrap2 a.getHeadInfo last.getTailInfo <$> tag (.nonterminal k' doc?) (nonTerm k')
    | _, _, _ => do -- return ((← args.mapM production) |>.toList |> (Format.joinSep · " "))
      let mut out := Format.nil
      for a in args do
        out := out ++ (← production a)
      let doc? ← findDocString? (← getEnv) k
      tag (.fromNonterminal k doc?) out

end Meta.PPrint.Grammar


open Manual.Meta.PPrint Grammar in
@[directive_expander «syntax»]
partial def «syntax» : DirectiveExpander
  | args, blocks => do
    let config ← SyntaxConfig.parse.run args
    let mut content := #[]
    let mut firstGrammar := true
    let productionCount := blocks.filterMap isGrammar? |>.size
    for b in blocks do
      match isGrammar? b with
      | some (argsStx, contents, info, col, «open», i, close) =>
        let grm ← elabGrammar config firstGrammar productionCount argsStx (Syntax.mkStrLit contents info) col «open» i info close
        content := content.push grm
        firstGrammar := false
      | _ =>
        content := content.push <| ← elabBlock b
    pure #[← `(Doc.Block.other {Block.syntax with data := ToJson.toJson (α := Option String × Name × String × Option Tag × Array Name) ($(quote config.title), $(quote config.name), $(quote config.label), none, $(quote config.aliases.toArray))} #[$content,*])]
where
  isGrammar? : Syntax → Option (Array Syntax × String × SourceInfo × Syntax × Syntax × SourceInfo × Syntax)
  | `<low|(Verso.Syntax.codeblock (column ~col@(.atom _ _col)) ~«open» ~(.node i `null #[nameStx, .node _ `null argsStx]) ~str@(.atom info contents) ~close )> =>
    if nameStx.getId == `grammar then some (argsStx, contents, info, col, «open», i, close) else none
  | _ => none

  categoryOf (env : Environment) (kind : Name) : Option Name := do
    for (catName, contents) in (Lean.Parser.parserExtension.getState env).categories do
      for (k, ()) in contents.kinds do
        if kind == k then return catName
    failure

  elabGrammar config isFirst howMany (argsStx : Array Syntax) (str : TSyntax `str) col «open» i info close := do
    let args ← parseArgs <| argsStx.map (⟨·⟩)
    let {of, prec} ← GrammarConfig.parse.run args
    let config : SyntaxConfig :=
      if let some n := of then
        {name := n, «open» := false}
      else config
    let altStr ← parserInputString str
    let p := andthen ⟨{}, whitespace⟩ <| andthen {fn := (fun _ => (·.pushSyntax (mkIdent config.name)))} (parserOfStack 0)
    match runParser (← getEnv) (← getOptions) p altStr (← getFileName) (prec := prec) with
    | .ok stx =>
      let bnf ← getBnf config isFirst howMany stx
      `(Block.other {Block.grammar with data := ToJson.toJson ($(quote bnf) : TaggedText GrammarTag)} #[])
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
      throwError "Parse errors prevented grammar from being processed."

  getBnf config isFirst howMany (stx : Syntax) : DocElabM (TaggedText GrammarTag) := do
    return (← renderBnf config isFirst howMany stx |>.run).render (w := 5)

  renderBnf config isFirst howMany (stx : Syntax) : TagFormatT GrammarTag DocElabM Format := do
    let cat := (categoryOf (← getEnv) config.name).getD config.name
    let d? ← findDocString? (← getEnv) cat
    let mut bnf : Format := (← tag (.nonterminal cat d?) s!"{nonTerm cat}") ++ " " ++ (← tag .bnf "::=")
    if config.open || (!config.open && !isFirst) then
      bnf := bnf ++ (" ..." : Format)
    bnf := bnf ++ .line
    let bar := (← tag .bnf "|") ++ " "
    bnf := bnf ++ (← if !config.open && isFirst then production stx else do return bar ++ .nest 2 (← production stx))
    return .nest 4 bnf -- ++ .line ++ repr stx


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
.grammar .nonterminal {
  font-style: italic;
}
.grammar .nonterminal > .hover-info, .grammar .from-nonterminal > .hover-info {
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
  tippy.createSingleton(tippy('pre.grammar.hl.lean .nonterminal.documented, pre.grammar.hl.lean .from-nonterminal.documented', innerProps), outerProps);
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


open Verso.Output Html in
@[block_extension grammar]
partial def grammar.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ info _ => do
      match FromJson.fromJson? (α := TaggedText GrammarTag) info with
      | .ok bnf => pure {{
          <pre class="grammar hl lean">
            {{← bnfHtml bnf }}
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
  bnfHtml : TaggedText GrammarTag → HtmlT Manual (ReaderT ExtensionImpls IO) Html
  | .text str => pure <| .text true str
  | .tag t txt => bnfHtml txt >>= tagHtml t
  | .append txts => .seq <$> txts.mapM bnfHtml

  tagHtml (t : GrammarTag) : Verso.Output.Html → HtmlT Manual (ReaderT ExtensionImpls IO) Html :=
    open Verso.Output.Html in
    match t with
    | .bnf => (pure {{<span class="bnf">{{·}}</span>}})
    | .error => (pure {{<span class="err">{{·}}</span>}})
    | .keyword => (pure {{<span class="keyword">{{·}}</span>}})
    | .nonterminal k doc? => nonTermHtmlOf k doc?
    | .fromNonterminal k none => (pure {{<span class="from-nonterminal" {{#[("data-kind", k.toString)]}}>{{·}}</span>}})
    | .fromNonterminal k (some doc) => (pure {{
        <span class="from-nonterminal documented" {{#[("data-kind", k.toString)]}}>
          <code class="hover-info"><code class="docstring">{{doc}}</code></code>
          {{·}}
        </span>
      }})

def Inline.syntaxKind : Inline where
  name := `Manual.syntaxKind

@[role_expander syntaxKind]
def syntaxKind : RoleExpander
  | args, inlines => do
    let config ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $syntaxKindName:str }) := arg
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
