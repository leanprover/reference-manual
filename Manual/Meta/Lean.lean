/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Lean.Elab.InfoTree.Types
import SubVerso.Highlighting.Code

open Verso Doc Elab
open Lean Elab
open Verso.Genre.Manual InlineLean Scopes
open Verso.SyntaxUtils
open SubVerso.Highlighting

/--
Elaborates the provided Lean term with a type annotation in the context of the current Verso module.
-/
@[role_expander typed]
def typed : RoleExpander
  -- Async elab is turned off to make sure that info trees and messages are available when highlighting
  | args, inlines => withoutAsync do
    let config ← LeanInlineConfig.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $term:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let altStr ← parserInputString term

    let leveller :=
      if let some us := config.universes then
        let us :=
          us.getString.splitOn " " |>.filterMap fun (s : String) =>
            if s.isEmpty then none else some s.toName
        Elab.Term.withLevelNames us
      else id

    match Parser.runParserCategory (← getEnv) `doc_metavar altStr (← getFileName) with
    | .error e => throw (.error (← getRef) e)
    | .ok stx => do
      let `(doc_metavar|$tm:term : $ty:term) := stx
        | throwErrorAt term "Expected colon-separated terms"

      let (newMsgs, type, tree) ← do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          let (tree', t) ← runWithOpenDecls <| runWithVariables fun _ => do

            let expectedType ← do
              let t ← leveller <| Elab.Term.elabType ty
              Term.synthesizeSyntheticMVarsNoPostponing
              let t ← instantiateMVars t
              -- if t.hasExprMVar || t.hasLevelMVar then
              --   throwErrorAt term "Type contains metavariables: {t}"
              pure t

            let e ← leveller <| Elab.Term.elabTerm (catchExPostpone := true) tm expectedType
            Term.synthesizeSyntheticMVarsNoPostponing
            let e ← Term.levelMVarToParam (← instantiateMVars e)
            let t ← Meta.inferType e >>= instantiateMVars >>= (Meta.ppExpr ·)
            let t := Std.Format.group <| (← Meta.ppExpr e) ++ (" :" ++ .line) ++ t

            Term.synthesizeSyntheticMVarsNoPostponing
            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure <| (InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Manual.leanInline, arg⟩) (← getInfoState).trees), t)
          pure (← Core.getMessageLog, t, tree')
        finally
          Core.setMessageLog initMsgs

      if let some name := config.name then

        let msgs ← newMsgs.toList.mapM fun (msg : Message) => do
          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let msg ← highlightMessage msg
          pure { msg with contents := .append #[.text head, msg.contents] }

        saveOutputs name msgs

      pushInfoTree tree

      if let `(inline|role{%$s $f $_*}%$e[$_*]) ← getRef then
        Hover.addCustomHover (mkNullNode #[s, e]) type
        Hover.addCustomHover f type

      match config.error with
      | none =>
        for msg in newMsgs.toArray do
          logMessage {msg with
            isSilent := msg.isSilent || msg.severity != .error
          }
      | some true =>
        if newMsgs.hasErrors then
          for msg in newMsgs.errorsToWarnings.toArray do
            logMessage {msg with isSilent := true}
        else
          throwErrorAt term "Error expected in code block, but none occurred"
      | some false =>
        for msg in newMsgs.toArray do
          logMessage {msg with isSilent := msg.isSilent || msg.severity != .error}
        if newMsgs.hasErrors then
          throwErrorAt term "No error expected in code block, one occurred"

      reportMessages config.error term newMsgs

      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))


      if config.show.getD true then
        pure #[← ``(Inline.other (Verso.Genre.Manual.InlineLean.Inline.lean $(quote hls)) #[Inline.code $(quote term.getString)])]
      else
        pure #[]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


  modifyInfoTrees {m} [Monad m] [MonadInfoTree m] (f : PersistentArray InfoTree → PersistentArray InfoTree) : m Unit :=
    modifyInfoState fun s => { s with trees := f s.trees }

  -- TODO - consider how to upstream this
  withInfoTreeContext {m α} [Monad m] [MonadInfoTree m] [MonadFinally m] (x : m α) (mkInfoTree : PersistentArray InfoTree → m InfoTree) : m (α × InfoTree) := do
    let treesSaved ← getResetInfoTrees
    MonadFinally.tryFinally' x fun _ => do
      let st    ← getInfoState
      let tree  ← mkInfoTree st.trees
      modifyInfoTrees fun _ => treesSaved.push tree
      pure tree
