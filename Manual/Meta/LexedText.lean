/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Manual.Meta.LexedText.Basic
public meta import Manual.Meta.LexedText.Basic
public meta import Verso.Doc.Elab.Monad
public meta import Verso.Parser
public import VersoManual.Basic
import Verso.Doc.Elab.Monad

public section

namespace Manual
open Verso
open Lean.Doc (CodeView)

open Lean
open Verso.Genre.Manual
open Verso.Doc Elab
open Verso.ArgParse


section
open LexedText
open Verso.Parser
open Lean.Parser

meta def hlC : Highlighter where
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
  data := toJson value

def Inline.c (value : LexedText) : Inline where
  data := toJson value

def lexedText := ()

@[code_block]
meta def C : CodeBlockExpanderOf Unit
  | (), str => do
    let codeStr := str.getVersoCodeBlock
    let toks ← LexedText.highlight hlC codeStr
    ``(Block.other (Block.c $(quote toks)) #[Block.code $(quote codeStr)])

open Verso.Output Html in
open Verso.Doc.Html in
@[block_extension Block.c]
def c.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some <| fun _ _ _ info _ => do
    let .ok (v : LexedText) := fromJson? info
      | reportError s!"Failed to deserialize {info} as lexer-enhanced text"; pure .empty
    pure {{<pre class="c">{{v.toHtml}}</pre>}}
  extraCss := [c.css]

open Verso.Output Html in
open Verso.Doc.Html in
@[inline_extension Inline.c]
def c.idescr : InlineDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml := some <| fun _ _ info _ => do
    let .ok (v : LexedText) := fromJson? info
      | reportError s!"Failed to deserialize {info} as lexer-enhanced text"; pure .empty
    pure {{<code class="c">{{v.toHtml}}</code>}}
  extraCss := [c.css]

@[role C]
meta def cInline : RoleExpanderOf Unit
  | (), contents => do
    let #[x] := contents
      | throwError "Expected exactly one parameter"
    let some { content := str, .. } := CodeView.of x
      | throwError "Expected exactly one code item"
    let codeStr := str.getVersoCode
    let toks ← LexedText.highlight hlC codeStr
    ``(Inline.other (Inline.c $(quote toks)) #[Inline.code $(quote codeStr)])
