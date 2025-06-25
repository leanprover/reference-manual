/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import Verso

import Manual.Meta.Attribute
import Manual.Meta.Basic
import Manual.Meta.CustomStyle

open Lean Meta Elab
open Verso Doc Elab Manual
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean (constTok)
open SubVerso.Highlighting Highlighted


namespace Manual

/--
A table for monotonicity lemmas. Likely some of this logic can be extracted to a helper
in `Manual/Meta/Table.lean`.
-/
private def mkInlineTable (rows : Array (Array Term)) (tag : Option String := none) : TermElabM Term := do
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
    -- The tag down here is relying on the coercion from `String` to `Tag`
    ``(Block.other (Block.table $(quote columns) (header := true) Option.none Option.none (tag := $(quote tag)))
        #[Block.ul #[$[Verso.Doc.ListItem.mk #[Block.para #[$blocks]]],*]])


section delabhelpers

/-!
To format the monotonicy lemma patterns, I’d like to clearly mark the monotone arguments from
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



@[block_role_expander monotonicityLemmas]
def monotonicityLemmas : BlockRoleExpander
  | #[], #[] => do
    let names := (Meta.Monotonicity.monotoneExt.getState (← getEnv)).values
    let names := names.qsort (toString · < toString ·)

    let rows : Array (Array Term) ← names.mapM fun name => do
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
              renderTagged none fmt ⟨{}, false, false, []⟩
            let fmt ← ppExpr call'
            ``(Inline.other (Verso.Genre.Manual.InlineLean.Inline.lean $(quote hlCall)) #[(Inline.code $(quote fmt.pretty))])

      pure #[nameStx, patternStx]

    let tableStx ← mkInlineTable rows (tag := "--monotonicity-lemma-table")
    let extraCss ← `(Block.other {Block.CSS with data := $(quote css)} #[])
    return #[extraCss, tableStx]
  | _, _ => throwError "Unexpected arguments"
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
