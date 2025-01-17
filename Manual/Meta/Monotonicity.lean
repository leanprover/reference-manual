/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Verso.Code

import SubVerso.Highlighting
import SubVerso.Examples

import Manual.Meta.Attribute
import Manual.Meta.Basic
import Manual.Meta.Bibliography
import Manual.Meta.CustomStyle
import Manual.Meta.Example
import Manual.Meta.Figure
import Manual.Meta.Lean
import Manual.Meta.Lean.IO
import Manual.Meta.Marginalia
import Manual.Meta.ParserAlias
import Manual.Meta.Syntax
import Manual.Meta.Table
import Manual.Meta.Tactics
import Manual.Meta.SpliceContents

open Lean Meta Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

@[block_role_expander monotonicityLemmas]
def monotonicityLemmas : BlockRoleExpander
  | #[], #[] => do
    let names := (Meta.Monotonicity.monotoneExt.getState (← getEnv)).values
    let names := names.qsort (toString · < toString ·)

    let itemStx : TSyntaxArray `term ← names.mapM fun name => do
      -- Extract the target pattern
      let ci ← getConstInfo name
      let targetStx : TSyntax `term ←
        forallTelescope ci.type fun _ concl => do
          unless concl.isAppOfArity ``Lean.Order.monotone 5 do
            throwError "Unexpecte conclusion of {name}"
          let f := concl.appArg!
          unless f.isLambda do
            throwError "Unexpecte conclusion of {name}"
          lambdaBoundedTelescope f 1 fun _ call => do
            let stx ← Lean.PrettyPrinter.delab call
            let format := Syntax.prettyPrint stx
            let str := format.pretty'
            `(Inline.code $(quote str))

      let hl : Highlighted ← constTok name name.toString
      let nameStx ← `(Inline.other {Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote name.getString!)])
      `(Verso.Doc.Block.para #[$nameStx, Inline.text ": applies to ", $targetStx])

    let theList ← `(Verso.Doc.Block.ul #[$[⟨#[$itemStx]⟩],*])
    return #[theList]
  | _, _ => throwError "Unexpected arguments"

-- #eval do
--   let (ss, _) ← (monotonicityLemmas #[] #[]).run {} (.init .missing)
--   logInfo (ss[0]!.raw.prettyPrint)
