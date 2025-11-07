/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import Verso

import Manual.Meta.Attribute
import Manual.Meta.Basic
import Manual.Meta.CustomStyle
import Manual.Meta.Instances

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


open Lean Elab Command Term
def mkMonotonicityLemmas : TermElabM Name := do
    let names := (Meta.Monotonicity.monotoneExt.getState (← getEnv)).values
    let names := names.qsort (toString · < toString ·)

    let mut rows := #[]

    for name in names do
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
            let n ← mkFreshUserName `monotonicity.hl

            -- This used to be a call to quote in the next quasiquotation, but that led to stack overflows in CI (but not locally)
            addAndCompile <| .defnDecl {name := n, levelParams := [], type := mkConst ``Highlighted, value := toExpr hlCall, hints := .regular 0, safety := .safe}

            ``(Inline.other (Verso.Genre.Manual.InlineLean.Inline.lean $(mkIdent n)) #[(Inline.code $(quote hlCall.toString))])

      rows := rows.push #[nameStx, patternStx]

    mkInlineTable rows (tag := "--monotonicity-lemma-table")


run_cmd do
  elabCommand <| ← `(def $(mkIdent `monoTable) := $(mkIdent (← runTermElabM <| fun _ => mkMonotonicityLemmas)))


@[block_command]
def monotonicityLemmas : BlockCommandOf Unit
  | () => do

    let extraCss ← `(Block.other {Block.CSS with data := $(quote css)} #[])
    dbg_trace "extraCss created"
    ``(Block.concat #[$extraCss, monoTable])
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
