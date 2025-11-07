/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import Verso

import Manual.Meta.Attribute
import Manual.Meta.Basic
import Manual.Meta.CustomStyle

open scoped Lean.Doc.Syntax

open Verso Doc Elab Manual
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean (constTok)
open SubVerso.Highlighting Highlighted
open Lean Meta Elab

namespace Manual

/--
A table for monotonicity lemmas. Likely some of this logic can be extracted to a helper
in `Manual/Meta/Table.lean`.
-/
private def mkInlineTable (rows : Array (Array Term)) (tag : Option String := none) : TermElabM Name := do
  if h : rows.size = 0 then
    throwError "Expected at least one row"
  else
    let columns := rows[0].size
    if columns = 0 then
      throwError "Expected at least one column"
    if rows.any (·.size != columns) then
      throwError s!"Expected all rows to have same number of columns, but got {rows.map (·.size)}"

    let blocks : Array Term :=
      #[ ← ``(Inline.text "Theorem"), ← ``(Inline.text "Pattern") ] ++
      rows.flatten

    dbg_trace blocks.size

    -- The new compiler has a stack overflow when compiling the table unless we split it up. This
    -- section is an elaborator to get good control over which parts of the table end up in their
    -- own defs.
    let arr1 ← mkFreshUserName `monoBlocks1
    let arr2 ← mkFreshUserName `monoBlocks2
    let blockName ← mkFreshUserName `block

    let blockType : Expr := .app (.const ``Verso.Doc.Block []) (.const ``Verso.Genre.Manual [])
    let listItemBlockType : Expr := .app (.const ``Verso.Doc.ListItem [0]) blockType
    let inlineType : Expr := .app (.const ``Verso.Doc.Inline []) (.const ``Verso.Genre.Manual [])
    let listItemInlineType : Expr := .app (.const ``Verso.Doc.ListItem [0]) inlineType
    let arrListItemBlockType : Expr := .app (.const ``Array [0]) listItemBlockType

    let elabCell (blk : Syntax) : TermElabM Expr := do
      let blk ← Term.elabTerm blk (some inlineType)
      let blk := mkApp2 (.const ``Verso.Doc.Block.para [])  (.const ``Verso.Genre.Manual []) (← mkArrayLit inlineType [blk])
      let blk := mkApp2 (.const ``Verso.Doc.ListItem.mk [0]) blockType (← mkArrayLit blockType [blk])
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars blk

    let blks1 ← blocks.take 70 |>.mapM elabCell
    let blks2 ← blocks.drop 70 |>.mapM elabCell

    let v1 ← mkArrayLit listItemBlockType blks1.toList
    addAndCompile <| .defnDecl {
      name := arr1, levelParams := [], type := arrListItemBlockType, value := v1, hints := .opaque, safety := .safe
    }

    let v1' ← mkArrayLit listItemBlockType blks2.toList
    addAndCompile <| .defnDecl {
      name := arr2, levelParams := [], type := arrListItemBlockType, value := v1', hints := .opaque, safety := .safe
    }

    -- The tag down here is relying on the coercion from `String` to `Tag`
    let stx ← ``(Block.other (Block.table $(quote columns) (header := true) Option.none Option.none (tag := $(quote tag)))
        #[Block.ul ($(mkIdent arr1) ++ $(mkIdent arr2))])
    let v2 ← Term.elabTerm stx (some blockType)
    Term.synthesizeSyntheticMVarsNoPostponing
    let v2 ← instantiateMVars v2

    addAndCompile <| .defnDecl {
      name := blockName, levelParams := [], type := blockType, value := v2, hints := .opaque, safety := .safe
    }

    return blockName




section delabhelpers

/-!
To format the monotonicity lemma patterns, I’d like to clearly mark the monotone arguments from
the other arguments. So I define two gadgets with custom delaborators.
-/

def monoArg := @id
def otherArg := @id

open PrettyPrinter.Delaborator

@[app_delab monoArg] def delabMonoArg : Delab :=
  PrettyPrinter.Delaborator.withOverApp 2 `(·)
@[app_delab otherArg] def delabOtherArg : Delab :=
  PrettyPrinter.Delaborator.withOverApp 2 `(_)

end delabhelpers

section debug
open SubVerso

/--
Finds the appropriate token kind for a token whose meaning is the expression `expr`.
-/
def exprKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m] [Alternative m]
    (ci : ContextInfo) (lctx : LocalContext) (stx? : Option Syntax) (expr : Expr)
    (allowUnknownTyped : Bool := false) :
    ReaderT Highlighting.Context m (Option Token.Kind) := do
  let runMeta {α} (act : MetaM α) (env := ci.env) (lctx := lctx) : m α := {ci with env := env}.runMetaM lctx act
  -- Print the signature in an empty local context to avoid local auxiliary definitions from
  -- elaboration, which may otherwise shadow in recursive occurrences, leading to spurious `_root_.`
  -- qualifiers
  let ppSig (x : Name) (env := ci.env) : ReaderT Highlighting.Context m String := do
    -- let sig ← runMeta (env := env) (lctx := {}) (PrettyPrinter.ppSignature x)
    -- return toString (← stripNamespaces sig)
    return "sig"

  let rec findKind e := do
    match e with
    | Expr.fvar id =>
      return none
      -- if let some y := (← read).ids[(← Compat.mkRefIdentFVar id)]? then
      --   Compat.refIdentCase y
      --     (onFVar := fun x => do
      --       let tyStr ← runMeta do
      --         try -- Needed for robustness in the face of tactics that create strange contexts
      --           let ty ← instantiateMVars (← Meta.inferType expr)
      --           ToString.toString <$> Meta.ppExpr ty
      --         catch | _ => pure ""
      --       if let some localDecl := lctx.find? x then
      --         if localDecl.isAuxDecl then
      --           let e ← runMeta <| Meta.ppExpr expr
      --           -- FIXME the mkSimple is a bit of a kludge
      --           return some <| .const (.mkSimple (toString e)) tyStr none false
      --       return some <| .var x tyStr)
      --     (onConst := fun x => do
      --       -- This is a bit of a hack. The environment in the ContextInfo may not have some
      --       -- helper constants from where blocks yet, so we retry in the final environment if the
      --       -- first one fails.
      --       let sig ← ppSig x <|> ppSig (env := (← getEnv)) x
      --       let docs ← findDocString? (← getEnv) x
      --       return some <| .const x sig docs false)
      -- else
      --   let tyStr ← runMeta do
      --     try -- Needed for robustness in the face of tactics that create strange contexts
      --       let ty ← instantiateMVars (← Meta.inferType expr)
      --       ToString.toString <$> Meta.ppExpr ty
      --     catch | _ => pure ""
      --   return some <| .var id tyStr
    | Expr.const name _ =>
      return none
      -- let docs ← findDocString? (← getEnv) name
      -- let sig ← ppSig name
      -- return some <| .const name sig docs false
    | Expr.sort _ =>
      return none
      -- if let some stx := stx? then
      --   let k := stx.getKind
      --   let docs? ← findDocString? (← getEnv) k
      --   return some (.sort docs?)
      -- else return some (.sort none)
    | Expr.lit (.strVal s) => return none --some <| .str s
    | Expr.mdata _ e => return none
      --findKind e
    | other =>
      return none
      -- if allowUnknownTyped then
      --   runMeta do
      --     try
      --       let t ← Meta.inferType other >>= instantiateMVars >>= Meta.ppExpr
      --       return some <| .withType <| toString t
      --     catch _ =>
      --       return none
      -- else
      --   return none

  findKind expr --(← instantiateMVars expr)

def termInfoKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m] [MonadFileMap m] [Alternative m]
    (ci : ContextInfo) (termInfo : TermInfo) (allowUnknownTyped : Bool := false) :
    ReaderT Highlighting.Context m (Option Token.Kind) := do
  exprKind ci termInfo.lctx termInfo.stx termInfo.expr (allowUnknownTyped := allowUnknownTyped)

def infoKind [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m] [MonadFileMap m] [Alternative m]
    (ci : ContextInfo) (info : Info) (allowUnknownTyped : Bool := false) :
    ReaderT Highlighting.Context m (Option Token.Kind) := do
  return none
  -- match info with
  --   | .ofTermInfo termInfo => termInfoKind ci termInfo (allowUnknownTyped := allowUnknownTyped)
  --   | _ =>
  --     pure none


end debug

inductive TokenState where
  | start
  | ws (pos : String.Iterator)
  | alphaNum (pos : String.Iterator)
  | other (pos : String.Iterator)

nonrec def tokenize (s : String) (outer : Option Token.Kind) : Highlighted := Id.run do
  let mut out := .empty
  let mut state := TokenState.start
  let mut iter := s.iter
  while iter.hasNext do
    let c := iter.curr
    match state, c.isWhitespace, c.isAlphanum with
    | .start, true, _ =>
      state := .ws iter
    | .start, false, true =>
      state := .alphaNum iter
    | .start, false, false =>
      state := .other iter
    | .ws _, true, _ =>
      pure ()
    | .ws pos, false, isA =>
      out := out ++ .text (pos.extract iter)
      state := if isA then .alphaNum iter else .other iter
    | .alphaNum _, _, true =>
      pure ()
    | .alphaNum pos, isWs, false =>
      let tok := pos.extract iter
      if tok ∈ kws then
        out := out ++ .token ⟨.keyword none none none, tok⟩
      else
        out := out ++ .token ⟨outer.getD .unknown, tok⟩
      state := if isWs then .ws iter else .other iter
    | .other pos, true, _ =>
      out := out ++ .token ⟨outer.getD .unknown, pos.extract iter⟩
      state := .ws iter
    | .other pos, _, true =>
      out := out ++ .token ⟨outer.getD .unknown, pos.extract iter⟩
      state := .alphaNum iter
    | .other .., _, _ =>
      pure ()
    iter := iter.next
  match state with
  | .start =>
    out := out ++ .text s
  | .ws pos =>
    out := out ++ .text (pos.extract iter)
  | .alphaNum pos =>
    let tok := pos.extract iter
    if tok ∈ kws then
      out := out ++ .token ⟨.keyword none none none, tok⟩
    else
      out := out ++ .token ⟨outer.getD .unknown, tok⟩
  | .other pos =>
    let tok := pos.extract iter
    out := out ++ .token ⟨outer.getD .unknown, tok⟩
  return out
where
  kws := ["let", "fun", "do", "match", "with", "if", "then", "else", "break", "continue", "for", "in", "mut"]

nonrec def renderTagged [Monad m] [MonadLiftT IO m] [MonadMCtx m] [MonadEnv m] [MonadFileMap m] [Alternative m]
    (outer : Option Token.Kind) (doc : Widget.CodeWithInfos) :
    ReaderT SubVerso.Highlighting.Context m Highlighted := do
  let mut out : Highlighted := .empty
  let mut todo : List (Widget.CodeWithInfos ⊕ Option Token.Kind):= [.inl doc]
  let mut outer := outer
  repeat
    match todo with
    | [] => return out
    | .inr outer' :: todo' =>
      todo := todo'
      outer := outer'
    | .inl d :: todo' =>
      todo := todo'
      match d with
      | .text txt =>
        out := out ++ tokenize txt outer
      | .tag t doc' =>
        todo := .inl doc' :: todo
        let {ctx, info, children := _} := t.info.val
        if let .text tok := doc' then
          out := out ++ .text (tok.takeWhile (·.isWhitespace))
          let k := .unknown --(← infoKind ctx info).getD .unknown
          out := out ++ .token ⟨k, tok.trim⟩
          out := out ++ .text (tok.takeRightWhile (·.isWhitespace))
        else
          todo := .inl doc' :: .inr outer :: todo
          --outer ← infoKind ctx info
          outer := none
      | .append xs =>
        todo := xs.toList.map (.inl ·) ++ todo

  return out
where
  tokenEnder str := str.isEmpty || !(SubVerso.Compat.String.Pos.get str 0 |>.isAlphanum)

open Lean Elab Command Term
def mkMonotonicityLemmas : TermElabM Name := do
    let names := (Meta.Monotonicity.monotoneExt.getState (← getEnv)).values
    let names := names.qsort (toString · < toString ·)

    let mut rows := #[]
    for name in names[0:30] do
      dbg_trace "making row for {name}"
      -- Extract the target pattern
      let ci ← getConstInfo name

      -- Omit the `Lean.Order` namespace, if present, to keep the table concise
      let nameStr := (name.replacePrefix `Lean.Order .anonymous).getString!
      let hl : Highlighted ← constTok name nameStr
      let nameStx ← `(Inline.other {Verso.Genre.Manual.InlineLean.Inline.name with data := ToJson.toJson $(quote hl)}
        #[Inline.code $(quote nameStr)])

      let patternStx : TSyntax `term ←
        forallTelescope ci.type fun _ concl => do
          unless concl.isAppOfArity ``Lean.Order.monotone 5 do
            throwError "Unexpected conclusion of {name}"
          let f := concl.appArg!
          unless f.isLambda do
            throwError "Unexpected conclusion of {name}"
          lambdaBoundedTelescope f 1 fun x call => do
            -- Monotone arguments are the free variables applied to `x`,
            -- Other arguments the other
            -- This is an ad-hoc transformation and may fail in cases more complex
            -- than we need right now (e.g. binders in the goal).
            let call' ← Meta.transform call (pre := fun e => do
              if e.isApp && e.appFn!.isFVar && e.appArg! == x[0]! then
                .done <$> mkAppM ``monoArg #[e]
              else if e.isFVar then
                .done <$> mkAppM ``otherArg #[e]
              else
                pure .continue)

            let hlCall ← withOptions (·.setBool `pp.tagAppFns true) do
              let fmt ← Lean.Widget.ppExprTagged call'
              renderTagged none fmt {ids := {}, definitionsPossible := false, includeUnparsed := false, suppressNamespaces := []}

            let fmt ← ppExpr call'
            ``(Inline.other (Verso.Genre.Manual.InlineLean.Inline.lean $(quote hlCall)) #[(Inline.code $(quote fmt.pretty))])

      rows := rows.push #[nameStx, patternStx]

    dbg_trace "now there's {rows.size} rows"

    mkInlineTable rows (tag := "--monotonicity-lemma-table")

elab "def_mono_entries" name:ident : command => do
  elabCommand <| ← `(def $name := $(mkIdent (← runTermElabM <| fun _ => mkMonotonicityLemmas)))

def_mono_entries x

#check x

@[block_command]
def monotonicityLemmas : BlockCommandOf Unit
  | () => do

    let extraCss ← `(Block.other {Block.CSS with data := $(quote css)} #[])
    dbg_trace "extraCss created"
    ``(Block.concat #[$extraCss, x])
where
  css := r#"
table#--monotonicity-lemma-table {
  border-collapse: collapse;
}
table#--monotonicity-lemma-table th {
  text-align: center;
}
table#--monotonicity-lemma-table th, table#--monotonicity-lemma-table th p {
  font-family: var(--verso-structure-font-family);
}
table#--monotonicity-lemma-table td:first-child {
  padding-bottom: 0.25em;
  padding-top: 0.25em;
  padding-left: 0;
  padding-right: 1.5em;
}
  "#

-- #eval do
--   let (ss, _) ← (monotonicityLemmas #[] #[]).run {} (.init .missing)
--   logInfo (ss[0]!.raw.prettyPrint)
