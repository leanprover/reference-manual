import VersoManual

import Manual.Meta.Basic
import Manual.Meta.PPrint

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

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
  | .str _ x => s!"⟨{x.toUpper}⟩"
  | x => s!"⟨{x.toString.toUpper}⟩"

  production : Syntax → TagFormatT Unit DocElabM Format
  | .atom _ str => tag () s!"“{str}”"
  | .missing => tag () "<missing>"
  | .ident _ _ x _ =>
    tag () <|
    match x with
    | .str x' "pseudo" => x'.toString
    | _ => x.toString
  | .node _ k args => do
    match k, antiquoteOf k, args with
    | `many.antiquot_suffix_splice, _, #[stx, star] => return ("{" : Format) ++ (← production stx) ++ "}"
    | _, some k', #[a, b, c, d] =>
      tag () (nonTerm k')
    | _, _, _ => do return (← args.mapM production) |>.toList |> (Format.joinSep · " ")

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
      let _ : Quote Unit := ⟨fun _ => Lean.Syntax.mkCApp ``PUnit.unit #[]⟩ -- TODO real metadata

      `(Block.other {Block.grammar with data := ToJson.toJson ($(quote bnf) : TaggedText Unit)} #[])
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
      `(asldfkj)

  getBnf config isFirst howMany (stx : Syntax) : DocElabM (TaggedText Unit) := do
    pure (← renderBnf config isFirst howMany stx |>.run).render

  renderBnf config isFirst howMany (stx : Syntax) : TagFormatT Unit DocElabM Format := do
    let mut bnf : Format := (← tag () s!"{nonTerm ((categoryOf (← getEnv) config.name).getD config.name)}") ++ " " ++ (← tag () "::=")
    if config.open || (!config.open && !isFirst) then
      bnf := bnf ++ ("..." : Format)
    bnf := bnf ++ .line
    let bar := (← tag () "|") ++ " "
    bnf := bnf ++ (if !config.open && isFirst then ("" : Format) else bar) ++ (← production stx)
    return .nest 4 bnf

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
def grammar.descr : BlockDescr where
  traverse _ _ _ := do
    pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ info _ => do
      match FromJson.fromJson? (α := TaggedText Unit) info with
      | .ok bnf =>
        pure {{
          <pre class="grammar">
            {{ bnf.stripTags }}
          </pre>
        }}
      | .error e =>
        Html.HtmlT.logError s!"Couldn't deserialize BNF: {e}"
        pure .empty
