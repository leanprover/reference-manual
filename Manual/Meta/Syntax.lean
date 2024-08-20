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

def Block.syntax : Block where
  name := `Manual.syntax

def Block.grammar : Block where
  name := `Manual.grammar

structure SyntaxConfig where
  name : Name
  «open» : Bool := true
  aliases : List Name


partial def many [Inhabited (f (List α))] [Applicative f] [Alternative f] (x : f α) : f (List α) :=
  ((· :: ·) <$> x <*> many x) <|> pure []

def SyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SyntaxConfig :=
  SyntaxConfig.mk <$>
    .positional `name .name <*>
    ((·.getD true) <$> (.named `open .bool true)) <*>
    (many (.named `alias .name false) <* .done)

inductive GrammarTag where
  | keyword
  | nonterminal (name : Name) (docstring? : Option String)
  | error
  | bnf
deriving Repr, FromJson, ToJson, Inhabited

open Lean.Syntax in
open GrammarTag in
instance : Quote GrammarTag where
  quote
    | keyword => mkCApp ``keyword #[]
    | nonterminal x d => mkCApp ``nonterminal #[quote x, quote d]
    | GrammarTag.error => mkCApp ``GrammarTag.error #[]
    | bnf => mkCApp ``bnf #[]

open Manual.Meta.PPrint in
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
    pure #[← `(Doc.Block.other Block.syntax #[$content,*])]
where
  isGrammar? : Syntax → Option (Array Syntax × String × SourceInfo × Syntax × Syntax × SourceInfo × Syntax)
  | `<low|(Verso.Syntax.codeblock (column ~col@(.atom _ _col)) ~«open» ~(.node i `null #[nameStx, .node _ `null argsStx]) ~str@(.atom info contents) ~close )> =>
    if nameStx.getId == `grammar then some (argsStx, contents, info, col, «open», i, close) else none
  | _ => none

  antiquoteOf : Name → Option Name
  | .str n "antiquot" => pure n
  | _ => none

  nonTerm : Name → String
  | .str x "pseudo" => nonTerm x
  | .str _ x => s!"⟨{x}⟩"
  | x => s!"⟨{x.toString}⟩"

  empty : Syntax → Bool
  | .node _ _ #[] => true
  | _ => false

  kleeneLike (mod : String) : Syntax → Format → TagFormatT GrammarTag DocElabM Format
  | .atom .., f
  | .ident .., f
  | .missing, f => do return f ++ (← tag .bnf mod)
  | .node _ _ args, f => do
    let nonempty := args.filter (!empty ·)
    if h : nonempty.size = 1 then
      kleeneLike mod nonempty[0] f
    else
      return (← tag .bnf "(") ++ f ++ (← tag .bnf s!"){mod}")

  kleene := kleeneLike "*"

  perhaps := kleeneLike "?"


  production (stx : Syntax) : TagFormatT GrammarTag DocElabM Format := do
    match stx with
    | .atom info str => do
      return (← tag .keyword s!"{str}") ++
        if let .original _ _ trailing _ := info then
          if trailing.any (· == '\n') then .line else .nil
        else .nil
    | .missing => tag .error "<missing>"
    | .ident info _ x _ =>
      let d? ← findDocString? (← getEnv) x
      -- TODO render markdown
      let tok ←
        tag (.nonterminal x d?) <|
          match x with
          | .str x' "pseudo" => x'.toString
          | _ => x.toString
      return tok ++
        if let .original _ _ trailing _ := info then
          if trailing.any (· == '\n') then .line else .nil
        else .nil
    | .node info k args => do
      .group <$>
      match k, antiquoteOf k, args with
      | `many.antiquot_suffix_splice, _, #[starred, star] => production starred >>= kleene starred
      | `optional.antiquot_suffix_splice, _, #[starred, star] => production starred >>= perhaps starred
      | `sepBy.antiquot_suffix_splice, _, #[starred, star] => production starred >>= kleeneLike ",*" starred
      | `many.antiquot_scope, _, #[_dollar, _null, _brack, contents, _brack2, .atom info _star] => do
        let doc ← production contents >>= kleene contents
        return doc ++
          if let .original _ _ trailing _ := info then
            if trailing.any (· == '\n') then .line else .nil
          else .nil
      | `optional.antiquot_scope, _, #[_dollar, _null, _brack, contents, _brack2, .atom info _star] => do
        let doc ← production contents >>= perhaps contents
        return doc ++
          if let .original _ _ trailing _ := info then
            if trailing.any (· == '\n') then .line else .nil
          else .nil
      | `sepBy.antiquot_scope, _, #[_dollar, _null, _brack, contents, _brack2, .atom info _star] => do
        let doc ← production contents >>= kleeneLike ",*" contents
        return doc ++
          if let .original _ _ trailing _ := info then
            if trailing.any (· == '\n') then .line else .nil
          else .nil
      | _, some k', #[a, b, c, d] => do
        let d? ← findDocString? (← getEnv) k'
        let doc ← tag (.nonterminal k' d?) (nonTerm k')
        return doc ++
          if let some (.original _ _ trailing _) := stx.getTailInfo? then
            if trailing.any (· == '\n') then .line else .nil
          else .nil
      | _, _, _ => do -- return ((← args.mapM production) |>.toList |> (Format.joinSep · " "))
        let mut out := Format.nil
        for a in args do
          out := out ++ (← production a)
          unless empty a do
            if let some (.original _ _ trailing _) := a.getTailInfo? then
              if trailing.any (· == '\n') then
                --out := out ++ .line
                continue
            out := out ++ " "
        pure out

  categoryOf (env : Environment) (kind : Name) : Option Name := do
    for (catName, contents) in (Lean.Parser.parserExtension.getState env).categories do
      for (k, ()) in contents.kinds do
        if kind == k then return catName
    failure

  elabGrammar config isFirst howMany (argsStx : Array Syntax) (str : TSyntax `str) col «open» i info close := do
    let args ← parseArgs <| argsStx.map (⟨·⟩)
    let #[] := args
      | throwErrorAt str "Expected 0 arguments"
    let altStr ← parserInputString str
    let p := andthen ⟨{}, whitespace⟩ <| andthen {fn := (fun _ => (·.pushSyntax (mkIdent config.name)))} (parserOfStack 0)
    match runParser (← getEnv) (← getOptions) p altStr (← getFileName) with
    | .ok stx =>
      let bnf ← getBnf config isFirst howMany stx
      `(Block.other {Block.grammar with data := ToJson.toJson ($(quote bnf) : TaggedText GrammarTag)} #[])
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
      `(asldfkj)

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


def grammar := ()

@[block_extension «syntax»]
def syntax.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{
        <div class="namedocs">
          <span class="label">"syntax"</span>
          {{← content.mapM goB}}
        </div>
      }}

@[block_extension grammar]
partial def grammar.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ info _ => do
      match FromJson.fromJson? (α := TaggedText GrammarTag) info with
      | .ok bnf =>
        pure {{
          <pre class="grammar hl lean">
            {{ bnfHtml bnf }}
          </pre>
        }}
      | .error e =>
        Html.HtmlT.logError s!"Couldn't deserialize BNF: {e}"
        pure .empty
  extraCss := [
r#"pre.grammar .keyword {
  font-weight: bold;
}
pre.grammar .keyword::before {
  content: '“';
  font-weight: normal;
}
pre.grammar .keyword::after {
  content: '”';
  font-weight: normal;
}
pre.grammar .nonterminal {
  font-style: italic;
}
pre.grammar .nonterminal > .hover-info {
  display: none;
}
pre.grammar .nonterminal.documented:hover {
  background-color: #eee;
  border-radius: 2px;
}
"#
  ]
  extraJs := [
    highlightingJs,
r#"
window.addEventListener("load", () => {
  tippy('pre.grammar.hl.lean .nonterminal.documented', {
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
where
  bnfHtml : TaggedText GrammarTag → Verso.Output.Html
  | .text str => .text true str
  | .tag t txt => tagHtml t (bnfHtml txt)
  | .append txts => .seq (txts.map bnfHtml)
  tagHtml (t : GrammarTag) : Verso.Output.Html → Verso.Output.Html :=
    open Verso.Output.Html in
    match t with
    | .bnf => ({{<span class="bnf">{{·}}</span>}})
    | .error => ({{<span class="err">{{·}}</span>}})
    | .keyword => ({{<span class="keyword">{{·}}</span>}})
    | .nonterminal k none => ({{<span class="nonterminal" {{#[("data-kind", k.toString)]}}>{{·}}</span>}})
    | .nonterminal k (some doc) => ({{
        <span class="nonterminal documented" {{#[("data-kind", k.toString)]}}>
          <code class="hover-info"><code class="docstring">{{doc}}</code></code>
          {{·}}
        </span>
      }})
