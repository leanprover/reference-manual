/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Manual.Meta.PPrint
public import Verso.Doc.Elab.Monad
import Lean.DocString

public section


open Verso Doc Elab
open Manual
open Verso.ArgParse
open Lean.Doc.Syntax


open Lean Elab Parser
open Lean.Widget (TaggedText)

namespace Manual

structure FreeSyntaxConfig where
  name : Name
  «open» : Bool := true
  label : Option String := none
  title : TSyntaxArray `inline

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
deriving Repr, FromJson, ToJson, Inhabited, BEq

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
    let sep := Syntax.mkStrLit <| String.ofList (List.replicate i '*')
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
private def antiquoteOf : Name → Option Name
  | .str n "antiquot" => pure n
  | _ => none

private def nonTerm : Name → String
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

private def isCompound [Monad m] (f : Format) : TagFormatT GrammarTag m Bool := do
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
      if (← get).tags[k]?.isEqSome .bnf then
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
      if (← get).tags[k]?.isEqSome .bnf then
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

private partial def kleeneLike (mod : String) (f : Format) : TagFormatT GrammarTag DocElabM Format := do
  if (← isCompound f) then return (← tag .bnf "(") ++ f ++ (← tag .bnf s!"){mod}")
  else return f ++ (← tag .bnf mod)


private def kleene := kleeneLike "*"

def perhaps := kleeneLike "?"

private def lined (ws : String) : Format :=
  Format.line.joinSep (ws.splitOn "\n")

private def noTrailing (info : SourceInfo) : Option SourceInfo :=
  match info with
  | .original leading p1 _ p2 => some <| .original leading p1 "".toRawSubstring p2
  | .synthetic .. => some info
  | .none => none

private def removeTrailing? : Syntax → Option Syntax
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

private def removeTrailing (stx : Syntax) : Syntax := removeTrailing? stx |>.getD stx

private def infoWrap (info : SourceInfo) (doc : Format) : Format :=
  if let .original leading _ trailing _ := info then
    lined leading.toString ++ doc ++ lined trailing.toString
  else doc

private def infoWrapTrailing (info : SourceInfo) (doc : Format) : Format :=
  if let .original _ _ trailing _ := info then
    doc ++ lined trailing.toString
  else doc

private def infoWrap2 (info1 : SourceInfo) (info2 : SourceInfo) (doc : Format) : Format :=
  let pre := if let .original leading _ _ _ := info1 then lined leading.toString else .nil
  let post := if let .original _ _ trailing _ := info2 then lined trailing.toString else .nil
  pre ++ doc ++ post

private def longestSuffix (strs : Array String) : String := Id.run do
  if h : strs.size = 0 then ""
  else
    let mut suff := strs[0].toSlice

    repeat
      if suff.isEmpty then return ""
      let suff' := suff
      for s in strs do
        unless s.dropSuffix? suff |>.isSome do
          suff := suff.drop 1
      if suff' == suff then return suff'.copy
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

private def longestPrefix (strs : Array String) : String := Id.run do
  if h : strs.size = 0 then ""
  else
    let mut pref := strs[0].toSlice

    repeat
      if pref.isEmpty then return ""
      let pref' := pref
      for s in strs do
        unless s.dropPrefix? pref |>.isSome do
          pref := pref.dropEnd 1
      if pref' == pref then return pref'.copy
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
private partial def isEmptySyntax : Syntax → Bool
  | .node info _ args => isEmptyInfo info && args.all isEmptySyntax
  | .atom info s => isEmptyInfo info && s.isEmpty
  | .ident .. => false
  | .missing => false
where
  isEmptyInfo
    | .original leading _ trailing _ => leading.isEmpty && trailing.isEmpty
    | _ => true

private def removeLeadingString (string : String) : Syntax → Syntax
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
    (string.take leading.toString.length |>.copy, .original (leading.drop string.length) pos trailing pos')
  | other => (string, other)

private partial def removeTrailingString (string : String) : Syntax → Syntax :=
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
    (string.dropEnd trailing.toString.length |>.copy, .original leading pos (trailing.dropRight string.length) pos')
  | other => (string, other)

/--
Extracts the common leading and trailing whitespaces from an array of syntaxes.

This is to be used when rendering choice nodes in a grammar, so they don't have redundant whitespace.
-/
private def commonWs (stxs : Array Syntax) : String × Array Syntax × String :=
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
private def keywordParsers : List (Name × String) :=
  [(``«private», "private"), (``«protected», "protected"), (``«partial», "partial"), (``«nonrec», "nonrec")]

open StateT (lift) in
partial def production (which : Nat) (stx : Syntax) : StateT (Lean.NameMap (Name × Option String)) (TagFormatT GrammarTag DocElabM) Format := do
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
        -- TODO: use a slice here. As of nightly-2025-10-20, the code panicked (reported)
        let mut str := val.dropEnd 2
        let mut contents : Format := .nil
        let mut inVar : Bool := false
        while !str.isEmpty do
          if inVar then
            let pre := str.takeWhile (· != '}')
            str := str.dropPrefix pre |>.drop 1
            let x := pre.trimAscii.toName
            if let some (c, d?) := (← get).find? x then
              contents := contents ++ (← lift <| tag (.localName x which c d?) x.toString)
            else
              contents := contents ++ x.toString
            inVar := false
          else
            let pre := str.takeWhile (· != '{')
            str := str.dropPrefix pre |>.drop 1
            contents := contents ++ pre.copy
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

private def categoryOf (env : Environment) (kind : Name) : Option Name := do
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
  let (tagged, _) ← getBnf config isFirst stxs |>.run ⟨default, default, default, default⟩ {} {partContext := ⟨⟨default, default, default, default, default, default⟩, default⟩}
  pure tagged.stripTags


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
      let txt := txt.trimAscii.copy
      modify (·.push (.keyword, txt))
      pure txt
    | .tag (.nonterminal ``Lean.Parser.Attr.simple ..) txt => do
      let kw := txt.stripTags.trimAscii.copy
      modify (·.push (.keyword, kw))
      pure kw
    | .tag (.nonterminal ..) _ => do
      ellipsis
      pure dots.2
    | .tag .literalIdent (.text s) => do
      modify (·.push (.literalIdent, s))
      return s
    | .tag .bnf (.text s) => do
      let s := s.trimAscii.copy
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
    if !s.isEmpty && s.all Char.isWhitespace then
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
        if curr.1 == .ws then continue
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

