/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import VersoManual

-- TODO generalize upstream - this is based on the one in the blog genre.
namespace Manual

abbrev LexedText.Highlighted := Array (Option String × String)

structure LexedText where
  name : String
  content : LexedText.Highlighted
deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToJson, Lean.FromJson

open Lean in
instance : Quote LexedText where
  quote
    | LexedText.mk n c => Syntax.mkCApp ``LexedText.mk #[quote n, quote c]

namespace LexedText

open Lean Parser

open Verso.Parser (ignoreFn)

-- In the absence of a proper regexp engine, abuse ParserFn here
structure Highlighter where
  name : String
  lexer : ParserFn
  tokenClass : Syntax → Option String

def highlight (hl : Highlighter) (str : String) : IO LexedText := do
  let mut out : Highlighted := #[]
  let mut unHl : Option String := none
  let env ← mkEmptyEnvironment
  let ictx := mkInputContext str "<input>"
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let mut s := mkParserState str
  repeat
    if str.atEnd s.pos then
      if let some txt := unHl then
        out := out.push (none, txt)
      break
    let s' := hl.lexer.run ictx pmctx {} s
    if s'.hasError then
      let c := str.get! s.pos
      unHl := unHl.getD "" |>.push c
      s := {s with pos := s.pos + c}
    else
      let stk := s'.stxStack.extract 0 s'.stxStack.size
      if stk.size ≠ 1 then
        unHl := unHl.getD "" ++ str.extract s.pos s'.pos
        s := s'.restore 0 s'.pos
      else
        let stx := stk[0]!
        match hl.tokenClass stx with
        | none => unHl := unHl.getD "" ++ str.extract s.pos s'.pos
        | some tok =>
          if let some ws := unHl then
            out := out.push (none, ws)
            unHl := none
          out := out.push (some tok, str.extract s.pos s'.pos)
        s := s'.restore 0 s'.pos
  pure ⟨hl.name, out⟩

def token (kind : Name) (p : ParserFn) : ParserFn :=
  nodeFn kind <| ignoreFn p

open Verso.Output Html

def toHtml (text : LexedText) : Html :=
  text.content.map fun
    | (none, txt) => (txt : Html)
    | (some cls, txt) => {{ <span class={{cls}}>{{txt}}</span>}}

--- Manual-specific parts

end LexedText

open Lean
open Verso.Genre.Manual
open Verso.Doc Elab
open Verso.ArgParse


section
open LexedText
open Verso.Parser
open Lean.Parser

def hlC : Highlighter where
  name := "C"
  lexer :=
    token `type (andthenFn type (notFollowedByFn (satisfyFn (·.isAlphanum)) "")) <|>
    token `kw (andthenFn kw (notFollowedByFn (satisfyFn (·.isAlphanum)) "")) <|>
    token `comment comment <|>
    token `name name <|>
    token `op op <|>
    token `brack brack
  tokenClass stx := pure (toString stx.getKind)
where
  kw := kws.foldl (init := strFn "if") (· <|> strFn ·)
  kws := ["then", "else", "extern", "struct", "typedef", "return"]
  type := andthenFn (types.foldl (init := strFn "void") (· <|> strFn ·))
            (optionalFn (atomicFn (andthenFn (manyFn (chFn ' ')) (chFn '*'))))
  types := ["lean_object", "lean_ctor_object", "lean_obj_arg", "b_lean_obj_arg", "size_t", "float", "double", "int", "char"] ++ sizes.map (s!"uint{·}_t")
  sizes := [8, 16, 32, 64]
  comment : ParserFn := andthenFn (strFn "//") (manyFn (satisfyFn (· ≠ '\n')))
  name := atomicFn (andthenFn (satisfyFn (fun c => c.isAlpha || c == '_')) (manyFn (satisfyFn (fun c => c.isAlphanum || c == '_'))))
  op := ops.foldl (init := strFn "++") (· <|> strFn ·)
  ops := ["+", "*", "/", "--", "-"]
  brack := chFn '{' <|> chFn '}' <|> chFn '[' <|> chFn ']' <|> chFn '(' <|> chFn ')'
end

private def c.css : String :=
r##"
.c .type { font-weight: 600; }
.c .kw { font-weight: 600; }
.c .comment { font-style: italic; }
"##

def Block.c (value : LexedText) : Block where
  name := `Manual.c
  data := toJson value

def Inline.c (value : LexedText) : Inline where
  name := `Manual.c
  data := toJson value

def lexedText := ()

@[code_block]
def c : CodeBlockExpanderOf Unit
  | (), str => do
    let codeStr := str.getString
    let toks ← LexedText.highlight hlC codeStr
    ``(Block.other (Block.c $(quote toks)) #[Block.code $(quote codeStr)])

open Verso.Output Html in
open Verso.Doc.Html in
@[block_extension c]
def c.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some <| fun _ _ _ info _ => do
    let .ok (v : LexedText) := fromJson? info
      | HtmlT.logError s!"Failed to deserialize {info} as lexer-enhanced text"; pure .empty
    pure {{<pre class="c">{{v.toHtml}}</pre>}}
  extraCss := [c.css]

open Verso.Output Html in
open Verso.Doc.Html in
@[inline_extension c]
def c.idescr : InlineDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some <| fun _ _ info _ => do
    let .ok (v : LexedText) := fromJson? info
      | HtmlT.logError s!"Failed to deserialize {info} as lexer-enhanced text"; pure .empty
    pure {{<code class="c">{{v.toHtml}}</code>}}
  extraCss := [c.css]

@[role c]
def cInline : RoleExpanderOf Unit
  | (), contents => do
    let #[x] := contents
      | throwError "Expected exactly one parameter"
    let `(inline|code($str)) := x
      | throwError "Expected exactly one code item"
    let codeStr := str.getString
    let toks ← LexedText.highlight hlC codeStr
    ``(Inline.other (Inline.c $(quote toks)) #[Inline.code $(quote codeStr)])
