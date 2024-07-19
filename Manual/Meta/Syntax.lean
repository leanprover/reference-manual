import Verso.Genre.Manual

import Manual.Meta.Basic

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab Parser

namespace Manual

-- run_elab do
--   let xs := _
--   let stx ← `(command|universe $xs*)
--   dbg_trace stx

def Block.syntax : Block where
  name := `Manual.syntax

structure SyntaxConfig where
  name : Name
  aliases : List Name

partial def many [Inhabited (f (List α))] [Applicative f] [Alternative f] (x : f α) : f (List α) :=
  ((· :: ·) <$> x <*> many x) <|> pure []

def SyntaxConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SyntaxConfig :=
  SyntaxConfig.mk <$> .positional `name .name <*> (many (.named `alias .name false) <* .done)

@[directive_expander «syntax»]
partial def «syntax» : DirectiveExpander
  | args, blocks => do
    let config ← SyntaxConfig.parse.run args
    let content ← blocks.mapM fun b => do
      match b with
      | `<low|(Verso.Syntax.codeblock (column ~col@(.atom _ _col)) ~«open» ~(.node i `null #[nameStx, .node _ `null argsStx]) ~str@(.atom info contents) ~close )> =>
        if nameStx.getId == `grammar then elabGrammar config.name argsStx (Syntax.mkStrLit contents info) col «open» i info close
        else elabBlock b
      | _ => elabBlock b
    pure #[← `(Doc.Block.other Block.syntax #[$content,*])]
where
  antiquoteOf : Name → Option Name
  | .str n "antiquot" => pure n
  | _ => none

  nonTerm (x : Name) : String := s!"⟨{x.toString.toUpper}⟩"

  production : Syntax → String
  | .atom _ str => s!"“{str}”"
  | .missing => "<missing>"
  | .ident _ _ x _ => x.toString
  | .node _ k args =>
    match k, antiquoteOf k, args with
    | `many.antiquot_suffix_splice, _, #[stx, star] => "{" ++ production stx ++ "}"
    | _, some k', #[a, b, c, d] =>
      nonTerm k'
    | _, _, _ => args.map production |>.toList |> String.intercalate " "

  categoryOf (env : Environment) (kind : Name) : Option Name := do
    for (catName, contents) in (Lean.Parser.parserExtension.getState env).categories do
      for (k, ()) in contents.kinds do
        if kind == k then return catName
    failure

  elabGrammar name (argsStx : Array Syntax) (str : TSyntax `str) col «open» i info close := do
    let args ← parseArgs <| argsStx.map (⟨·⟩)
    let #[] := args
      | throwErrorAt str "Expected 0 arguments"
    let altStr ← parserInputString str
    let p := andthen ⟨{}, whitespace⟩ <| andthen {fn := (fun _ => (·.pushSyntax (mkIdent name)))} (parserOfStack 0)
    match runParser (← getEnv) (← getOptions) p altStr (← getFileName) with
    | .ok stx =>
      let mut bnf := s!"{nonTerm ((categoryOf (← getEnv) name).getD name)} ::="
      bnf := bnf ++ " ...\n"
      bnf := bnf ++ "  | " ++ production stx

      elabBlock `<low|(Verso.Syntax.codeblock (column ~col) ~«open» ~(.node i `null #[]) ~(.atom info bnf) ~close)>
    | .error es =>
      dbg_trace es.length
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<example>" pos msg)
      `(asldfkj)

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
