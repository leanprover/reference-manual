/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Term
import Lean.Elab.Tactic

import Verso.Code.Highlighted
import Verso.Doc.ArgParse
import Verso.Doc.Suggestion
import SubVerso.Highlighting.Code
import SubVerso.Examples.Messages
import VersoManual

import Manual.Meta.Basic
import Manual.Meta.PPrint

namespace Manual

open Lean Elab Term Tactic
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open Verso.Genre.Manual.InlineLean.Scopes (runWithOpenDecls runWithVariables)
open SubVerso.Highlighting
open SubVerso.Examples.Messages

def Block.proofState (tag : Option String) (hl : Array (Highlighted.Goal Highlighted)) : Block where
  name := `Manual.proofState
  data := ToJson.toJson (tag, hl)

structure ProofStateOptions where
  tag : Option String := none


def ProofStateOptions.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m ProofStateOptions :=
  ProofStateOptions.mk <$> .named `tag .string true


open Lean.Parser in
/--
Show a proof state in the text. The proof goal is expected as a documentation comment immediately
prior to tactics.
-/
@[code_block_expander proofState]
def proofState : CodeBlockExpander
  | args, str => InlineLean.usingExamplesEnv do
    let opts ← ProofStateOptions.parse.run args
    let altStr ← parserInputString str
    let p :=
      node nullKind <|
      andthen ⟨{}, whitespace⟩ <|
      andthen termParser <|
      andthen ⟨{}, whitespace⟩ <|
      andthen ":=" <| andthen ⟨{}, whitespace⟩ <| andthen "by" <|
      andthen ⟨{}, whitespace⟩ <|
      andthen (andthen {fn := (fun _ => (·.pushSyntax (mkIdent `tacticSeq)))} (parserOfStack 0)) <|
      optional <|
        andthen  ⟨{}, whitespace⟩ <|
        Command.docComment
    match runParser (← getEnv) (← getOptions) p altStr (← getFileName) with
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<setup>" pos msg)
      throwErrorAt str "Failed to parse config (expected goal term, followed by ':=', 'by', and tactics, with optional docstring)"
    | .ok stx =>
      let goalStx := stx[0]
      let tacticStx := stx[4]
      let desired :=
        match stx[5][0] with
        | .missing => none
        | other => some (⟨other⟩ : TSyntax `Lean.Parser.Command.docComment)
      let goalExpr ← runWithOpenDecls <| runWithVariables fun _ => Elab.Term.elabTerm goalStx none
      let mv ← Meta.mkFreshExprMVar (some goalExpr)
        let Expr.mvar mvarId := mv
          | throwError "Not an mvar!"
      let (remainingGoals, infoTree) ← withInfoTreeContext (mkInfoTree := mkInfoTree `proofState (← getRef)) do
            Tactic.run mvarId <|
            withoutTacticIncrementality true <|
            withTacticInfoContext tacticStx do
              evalTactic tacticStx
      synthesizeSyntheticMVars (postpone := .no)
      let ci : ContextInfo := {
        env := ← getEnv, fileMap := ← getFileMap, ngen := ← getNGen,
        mctx := ← getMCtx, options := ← getOptions,
        currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls
      }
      let hlState ← highlightProofState ci remainingGoals (PersistentArray.empty.push infoTree)
      let st := goalsToMessageData remainingGoals
      --logInfoAt proofPrefix st1
      let stStr ← (← addMessageContext st).toString
      if let some s := desired then
        if normalizeMetavars stStr.trim != normalizeMetavars s.getDocString.trim then
          logErrorAt s m!"Expected: {indentD stStr}\n\nGot: {indentD s.getDocString}"
          Verso.Doc.Suggestion.saveSuggestion s (stStr.take 30 ++ "…") ("/--\n" ++ stStr ++ "\n-/\n")
      pure #[← `(Doc.Block.other (Block.proofState $(quote opts.tag) $(quote hlState)) #[Doc.Block.code $(quote stStr)])]

where
  mkInfoTree (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree) : DocElabM InfoTree := do
    let tree := InfoTree.node (Info.ofCommandInfo { elaborator, stx }) trees
    let ctx := PartialContextInfo.commandCtx {
      env := ← getEnv, fileMap := ← getFileMap, mctx := {}, currNamespace := ← getCurrNamespace,
      openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
    }
    return InfoTree.context ctx tree

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




def proofStateStyle := r#"
.hl.lean.tactic-view {
  white-space: collapse;
}
.hl.lean.tactic-view .tactic-state {
  display: block;
  left: 0;
  padding: 0;
  border: none;
}
.hl.lean.tactic-view .tactic-state .goal {
  margin-top: 1em;
  margin-bottom: 1em;
  display: block;
}
.hl.lean.tactic-view .tactic-state .goal:first-child {
  margin-top: 0.25em;
}
.hl.lean.tactic-view .tactic-state .goal:last-child {
  margin-bottom: 0.25em;
}


"#



@[block_extension Manual.proofState]
def proofState.descr : BlockDescr where
  traverse id data content := do
    match FromJson.fromJson? data (α := Option String × Array (Highlighted.Goal Highlighted)) with
    | .error e => logError s!"Error deserializing proof state info: {e}"; pure none
    | .ok (none, _) => pure none
    | .ok (some t, v) =>
      let path ← (·.path) <$> read
      let _tag ← Verso.Genre.Manual.externalTag id path t
      pure <| some <| Block.other {Block.proofState none v with id := some id, data := ToJson.toJson (α := (Option String × _)) (none, v)} content

  toTeX := none
  extraCss := [highlightingStyle, proofStateStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ id data _ => do
      match FromJson.fromJson? (α := Option Tag × Array (Highlighted.Goal Highlighted)) data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize proof state while rendering HTML: " ++ err
        pure .empty
      | .ok (_, goals) =>
        let xref ← HtmlT.state
        let idAttr := xref.htmlId id

        pure {{
          <div class="hl lean tactic-view">
            <div class="tactic-state" {{idAttr}}>
              {{← if goals.isEmpty then
                  pure {{"All goals completed! 🐙"}}
                else
                  .seq <$> goals.mapIndexedM (fun ⟨i, _⟩ x => withCollapsedSubgoals .never <| x.toHtml (·.toHtml) i)}}
            </div>
          </div>
        }}

deriving instance ToExpr for GuardMsgs.WhitespaceMode

structure TacticOutputConfig where
  «show» : Bool := true
  severity : Option MessageSeverity
  summarize : Bool
  whitespace : GuardMsgs.WhitespaceMode
deriving ToExpr

def TacticOutputConfig.parser [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m TacticOutputConfig :=
  TacticOutputConfig.mk <$>
    ((·.getD true) <$> .named `show .bool true) <*>
    .named `severity .messageSeverity true <*>
    ((·.getD false) <$> .named `summarize .bool true) <*>
    ((·.getD .exact) <$> .named `whitespace .whitespaceMode true)


def checkTacticExample (goal : Term) (proofPrefix : Syntax) (tactic : Syntax) (pre : TSyntax `str) (post : TSyntax `str) : TermElabM Unit := do
  let statement ← elabType goal
  let mv ← Meta.mkFreshExprMVar (some statement)
  let Expr.mvar mvarId := mv
    | throwError "Not an mvar!"
  -- `runTactic` is too specialized for this purpose - we need to capture the unsolved goals, not
  -- throw them as an exception. This code is adapted from `runTactic`.
  let remainingGoals ← withInfoHole mvarId <| Tactic.run mvarId do
    withoutTacticIncrementality true <|
    withTacticInfoContext proofPrefix do
      -- also put an info node on the `by` keyword specifically -- the token may be `canonical` and thus shown in the info
      -- view even though it is synthetic while a node like `tacticCode` never is (#1990)
      evalTactic proofPrefix
    synthesizeSyntheticMVars (postpone := .no)
  -- `runTactic` extraction done. Now prettyprint the proof state.
  let st1 := goalsToMessageData remainingGoals
  --logInfoAt proofPrefix st1
  let goodPre ← (← addMessageContext st1).toString
  if pre.getString != goodPre then
    logErrorAt pre m!"Mismatch. Expected {indentD goodPre}\n but got {indentD pre.getString}"
  -- Run the example
  let remainingGoals' ← Tactic.run mvarId do
    withoutTacticIncrementality true <|
    withTacticInfoContext tactic do
      set (Tactic.State.mk remainingGoals)
      evalTactic tactic
  let st2 := goalsToMessageData remainingGoals'
  --logInfoAt tactic st2
  let goodPost ← (← addMessageContext st2).toString
  if post.getString != goodPost then
    logErrorAt post m!"Mismatch. Expected {indentD goodPost}\n but got {indentD post.getString}"

open Lean.Elab.Tactic.GuardMsgs in
def checkTacticExample'
    (goal : Expr) (proofPrefix : Syntax) (tactic : Syntax)
    (pre : TSyntax `str) (post : TSyntax `str)
    (output : Option (TSyntax `str × TacticOutputConfig)) :
    TermElabM
      (Array (Highlighted.Goal Highlighted) ×
        Array (Highlighted.Goal Highlighted) ×
        Highlighted ×
        MessageSeverity) := do
  let mv ← Meta.mkFreshExprMVar (some goal)
  let Expr.mvar mvarId := mv
    | throwError "Not an mvar!"
  -- `runTactic` is too specialized for this purpose - we need to capture the unsolved goals, not
  -- throw them as an exception. This code is adapted from `runTactic`.
  let ((remainingGoals, _setupMsgs), preTree) ← withInfoTreeContext (mkInfoTree := mkInfoTree `leanInline (← getRef)) do
    let initMsgs ← Core.getMessageLog
    try
      Core.resetMessageLog
      let remainingGoals ←
        withInfoHole mvarId <| Tactic.run mvarId <|
        withoutTacticIncrementality true <|
        withTacticInfoContext proofPrefix do
          -- also put an info node on the `by` keyword specifically -- the token may be `canonical` and thus shown in the info
          -- view even though it is synthetic while a node like `tacticCode` never is (#1990)
          evalTactic proofPrefix
      synthesizeSyntheticMVars (postpone := .no)
      let msgs ← Core.getMessageLog
      pure (remainingGoals, msgs)
    finally Core.setMessageLog initMsgs


  -- `runTactic` extraction done. Now prettyprint the proof state.
  let st1 := goalsToMessageData remainingGoals
  --logInfoAt proofPrefix st1
  let goodPre ← (← addMessageContext st1).toString
  if pre.getString.trim != goodPre.trim then
    Verso.Doc.Suggestion.saveSuggestion pre (goodPre.take 30 ++ "…") (goodPre ++ "\n")
    logErrorAt pre m!"Mismatch. Expected {indentD goodPre}\n but got {indentD pre.getString}"

  let ci : ContextInfo := {
    env := ← getEnv, fileMap := ← getFileMap, ngen := ← getNGen,
    mctx := ← getMCtx, options := ← getOptions,
    currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls
  }
  let hlPre ← highlightProofState ci remainingGoals (PersistentArray.empty.push preTree)

  -- Run the example
  let ((remainingGoals', msgs), postTree) ← withInfoTreeContext (mkInfoTree := mkInfoTree `leanInline (← getRef)) do
    let initMsgs ← Core.getMessageLog
    try
      Core.resetMessageLog
      let remainingGoals' ← Tactic.run mvarId <|
        withoutTacticIncrementality true <|
        withTacticInfoContext tactic do
          set (Tactic.State.mk remainingGoals)
          evalTactic tactic
      let msgs ← Core.getMessageLog
      pure (remainingGoals', msgs)
    finally Core.setMessageLog initMsgs
  let st2 := goalsToMessageData remainingGoals'
  --logInfoAt tactic st2
  let goodPost ← (← addMessageContext st2).toString

  if post.getString.trim != goodPost.trim then
    Verso.Doc.Suggestion.saveSuggestion post (goodPost.take 30 ++ "…") (goodPost ++ "\n")
    logErrorAt post m!"Mismatch. Expected {indentD goodPost}\n but got {indentD post.getString}"

  let ci : ContextInfo := { ci with
    mctx := ← getMCtx
  }
  let hlPost ← highlightProofState ci remainingGoals' (PersistentArray.empty.push postTree)

  -- TODO suppress proof state bubbles here, at least as an option - `Inline.lean` needs to take that as an argument
  let hlTac ← highlight tactic msgs.toArray (PersistentArray.empty.push postTree)
  let outSev ← id <| do -- This 'id' is needed so that `return` in the `do` goes here
    if let some (wantedOut, config) := output then
      let processed ← msgs.toArray.mapM fun msg => do
            let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
            let txt := withNewline <| head ++ (← msg.data.toString)
            pure (msg.severity, txt)
      for (sev, txt) in processed do
        if mostlyEqual config.whitespace wantedOut.getString txt then
          if let some s := config.severity then
            if s != sev then
              throwErrorAt wantedOut s!"Expected severity {sevStr s}, but got {sevStr sev}"
          return sev
      for (_, m) in processed do
        Verso.Doc.Suggestion.saveSuggestion wantedOut (m.take 30 ++ "…") m
      throwErrorAt wantedOut "Didn't match - expected one of: {indentD (toMessageData <| processed.map (·.2))}\nbut got:{indentD (toMessageData wantedOut.getString)}"
    else pure .information

  return (hlPre, hlPost, hlTac, outSev)
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str

  sevStr : MessageSeverity → String
    | .error => "error"
    | .information => "information"
    | .warning => "warning"

  mostlyEqual (ws : WhitespaceMode) (s1 s2 : String) : Bool :=
    ws.apply s1.trim == ws.apply s2.trim

  mkInfoTree (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree) : TermElabM InfoTree := do
    let tree := InfoTree.node (Info.ofCommandInfo { elaborator, stx }) trees
    let ctx := PartialContextInfo.commandCtx {
      env := ← getEnv, fileMap := ← getFileMap, mctx := {}, currNamespace := ← getCurrNamespace,
      openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
    }
    return InfoTree.context ctx tree

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


open Command

-- TODO: This code would be much nicer if genres could impose custom elaboration contexts as well.
-- As things are, this seems to require hygiene-bending and environment mutation (basically the
-- fluid-let trick, in the absence of syntax parameters), which is icky and tricky and error-prone.

structure TacticExampleContext where
  goal : Option Expr := none
  setup : Option Syntax := none
  pre : Option (TSyntax `str) := none
  preName : Ident
  tactic : Option Syntax := none
  tacticName : Ident
  post : Option (TSyntax `str) := none
  postName : Ident
  output : Option (TSyntax `str × TacticOutputConfig) := none
  outputSeverityName : Ident

initialize tacticExampleCtx : Lean.EnvExtension (Option TacticExampleContext) ←
  Lean.registerEnvExtension (pure none)

def startExample [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT CoreM m] [MonadQuotation m] [MonadRef m] : m Unit := do
  match tacticExampleCtx.getState (← getEnv) with
  | some _ => throwError "Can't initialize - already in a context"
  | none =>
    let preName := mkIdentFrom (← getRef) (← mkFreshUserName `preState)
    let tacticName := mkIdentFrom (← getRef) (← mkFreshUserName `tactic)
    let postName := mkIdentFrom (← getRef) (← mkFreshUserName `postState)
    let outputSeverityName := mkIdentFrom (← getRef) (← mkFreshUserName `severity)
    modifyEnv fun env =>
      tacticExampleCtx.setState env (some {preName, tacticName, postName, outputSeverityName})

def saveGoal [Monad m] [MonadEnv m] [MonadError m] (goal : Expr) : m Unit := do
  match tacticExampleCtx.getState (← getEnv) with
  | none => throwError "Can't set goal - not in a tactic example"
  | some st =>
    match st.goal with
    | none => modifyEnv fun env => tacticExampleCtx.setState env (some {st with goal := goal})
    | some _ => throwError "Goal already specified"

def saveSetup [Monad m] [MonadEnv m] [MonadError m] (setup : Syntax) : m Unit := do
  match tacticExampleCtx.getState (← getEnv) with
  | none => throwError "Can't set setup - not in a tactic example"
  | some st =>
    match st.setup with
    | none => modifyEnv fun env => tacticExampleCtx.setState env (some {st with setup := setup})
    | some _ => throwError "Setup already specified"

def saveTactic [Monad m] [MonadEnv m] [MonadError m] (tactic : Syntax) : m Ident := do
  match tacticExampleCtx.getState (← getEnv) with
  | none => throwError "Can't set tactic step - not in a tactic example"
  | some st =>
    match st.tactic with
    | some _ => throwError "Tactic step already specified"
    | none =>
      modifyEnv fun env => tacticExampleCtx.setState env (some {st with tactic := tactic})
      return st.tacticName

def savePre [Monad m] [MonadEnv m] [MonadLog m] [MonadRef m] [MonadError m] [AddMessageContext m] [MonadOptions m] (pre : TSyntax `str) : m Ident := do
  match tacticExampleCtx.getState (← getEnv) with
  | none => throwError "Can't set pre-state - not in a tactic example"
  | some st =>
    match st.pre with
    | none =>
      modifyEnv fun env => tacticExampleCtx.setState env (some {st with pre := pre})
    | some _ =>
      logErrorAt (← getRef) "Pre-state already specified"
    return st.preName

def saveOutput [Monad m] [MonadEnv m] [MonadLog m] [MonadRef m] [MonadError m] [AddMessageContext m] [MonadOptions m] (output : TSyntax `str) (options : TacticOutputConfig) : m Ident := do
  match tacticExampleCtx.getState (← getEnv) with
  | none => throwError "Can't set expected output - not in a tactic example"
  | some st =>
    match st.output with
    | none =>
      modifyEnv fun env => tacticExampleCtx.setState env (some {st with output := some (output, options)})
    | some _ =>
      logErrorAt (← getRef) "Expected output already specified"
    return st.outputSeverityName


def savePost [Monad m] [MonadEnv m] [MonadLog m] [MonadRef m] [MonadError m] [AddMessageContext m] [MonadOptions m] (post : TSyntax `str) : m Ident := do
  match tacticExampleCtx.getState (← getEnv) with
  | none => throwError "Can't set post-state - not in a tactic example"
  | some st =>
    match st.post with
    | none =>
      modifyEnv fun env => tacticExampleCtx.setState env (some {st with post := post})
    | some _ =>
      logErrorAt (← getRef) "Post-state already specified"
    return st.postName


def endExampleSetup : DocElabM Unit := do
  match tacticExampleCtx.getState (← getEnv) with
  | none => throwError "Can't end examples - never started"
  | some {goal, setup, pre, preName, tactic, tacticName, post, postName, output, outputSeverityName} =>
    modifyEnv fun env =>
      tacticExampleCtx.setState env none
    let some goal := goal
      | throwError "No goal specified"
    let some setup := setup
      | throwError "No setup specified"
    let some pre := pre
      | throwError "No pre-state specified"
    let some tactic := tactic
      | throwError "No tactic specified"
    let some post := post
      | throwError "No post-state specified"

    let (hlPre, hlPost, hlTactic, outputSeverity) ← checkTacticExample' goal setup tactic pre post output

    let goalsType : Expr := .app (.const ``Array [0]) (.app (.const ``Highlighted.Goal [0]) (.const ``Highlighted []))
    addAndCompile <| .defnDecl {
      name := preName.getId, levelParams := [], type := goalsType,
      value := toExpr hlPre, hints := .opaque, safety := .safe
    }
    addAndCompile <| .defnDecl {
      name := postName.getId, levelParams := [], type := goalsType,
      value := toExpr hlPost, hints := .opaque, safety := .safe
    }
    addAndCompile <| .defnDecl {
      name := tacticName.getId, levelParams := [], type := .const ``Highlighted [],
      value := toExpr hlTactic, hints := .opaque, safety := .safe
    }
    addAndCompile <| .defnDecl {
      name := outputSeverityName.getId, levelParams := [], type := .const ``MessageSeverity [],
      value := toExpr outputSeverity, hints := .opaque, safety := .safe
    }

    let env ← getEnv
    let some _ := env.find? preName.getId
      | throwError "Didn't define {preName}"
    let some _ := env.find? postName.getId
      | throwError "Didn't define {postName}"
    let some _ := env.find? tacticName.getId
      | throwError "Didn't define {tacticName}"
    let some _ := env.find? outputSeverityName.getId
      | throwError "Didn't define {outputSeverityName}"

structure TacticGoalConfig where
  «show» : Bool

def TacticGoalConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m TacticGoalConfig :=
  TacticGoalConfig.mk <$> ((·.getD true) <$> .named `show .bool true)

@[role_elab goal]
def goal : RoleElab
  | args, inlines => do
    let config ← TacticGoalConfig.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $term:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"
    let altStr ← parserInputString term

    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt term e
    | .ok stx =>
      let (newMsgs, tree) ← withInfoTreeContext (mkInfoTree := mkInfoTree `leanInline (← getRef)) do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          let goalExpr ← runWithOpenDecls <| runWithVariables fun _ => Elab.Term.elabTerm stx none
          saveGoal goalExpr
          Core.getMessageLog
        finally
          Core.setMessageLog initMsgs


      for msg in newMsgs.toArray do
        logMessage msg

      -- TODO msgs
      let hls := (← highlight stx #[] (PersistentArray.empty.push tree))
      let g ← DocElabM.genreExpr

      if config.show then
        -- Just emit a normal Lean node - no need to do anything special with the rendered result
        let blockType := mkApp (.const ``InlineLean.Inline.lean []) (toExpr hls)
        pure <| mkApp3 (.const ``Inline.other []) g blockType (← DocElabM.inlineArray #[mkApp2 (.const ``Inline.code []) g (mkStrLit term.getString)])
      else
        pure <| mkApp2 (.const ``Inline.concat []) g (← DocElabM.inlineArray #[])
where
  mkInfoTree (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree) : DocElabM InfoTree := do
    let tree := InfoTree.node (Info.ofCommandInfo { elaborator, stx }) trees
    let ctx := PartialContextInfo.commandCtx {
      env := ← getEnv, fileMap := ← getFileMap, mctx := {}, currNamespace := ← getCurrNamespace,
      openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
    }
    return InfoTree.context ctx tree

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


open Lean.Parser in
@[code_block_elab setup]
def setup : CodeBlockElab
  | args, str => do
    let () ← ArgParse.done.run args

    let altStr ← parserInputString str

    let p := andthen ⟨{}, whitespace⟩ <| andthen {fn := (fun _ => (·.pushSyntax (mkIdent `tacticSeq)))} (parserOfStack 0)
    match runParser (← getEnv) (← getOptions) p altStr (← getFileName) with
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<setup>" pos msg)
      throwErrorAt str "Failed to parse setup"
    | .ok stx =>
      saveSetup stx
      let g ← DocElabM.genreExpr
      pure <| mkApp2 (.const ``Block.concat []) g (← DocElabM.blockArray #[])


open Lean.Parser in
@[code_block_elab tacticOutput]
def tacticOutput : CodeBlockElab
  | args, str => do
    let opts ← TacticOutputConfig.parser.run args
    let outputSeverityName ← saveOutput str opts

    let g ← DocElabM.genreExpr

    if opts.show then
      let t := mkApp2 (.const ``Prod [0, 0]) (.const ``MessageSeverity []) (mkApp2 (.const ``Prod [0, 0]) (.const ``String []) (.const ``Bool []))
      let noInternalId : Expr := .app (.const ``Option.none [0]) (.const ``InternalId [])
      let strSummarize ← Meta.mkAppM ``Prod.mk #[mkStrLit str.getString, toExpr opts.summarize]
      let strSummarizeT ← Meta.inferType strSummarize
      -- Can't use mkAppM here because the output severity constant isn't yet defined when this runs
      let sevStrSummarize := mkApp4 (.const ``Prod.mk [0, 0]) (.const ``MessageSeverity []) strSummarizeT (.const outputSeverityName.getId []) strSummarize
      let inst ← Meta.synthInstance (.app (.const ``ToJson [0]) t)
      let which := mkApp3 (.const ``Verso.Genre.Manual.Block.mk []) (toExpr Verso.Genre.Manual.InlineLean.Block.leanOutput.name) noInternalId (mkApp3 (.const ``ToJson.toJson [0]) t inst sevStrSummarize)
      let code := mkApp2 (.const ``Block.code []) g (mkStrLit str.getString)
      let code ← DocElabM.blockArray #[code]
      return mkApp3 (.const ``Block.other []) g which code
    else
      return mkApp2 (.const ``Block.concat []) g (← DocElabM.blockArray #[])


open Lean.Parser in
@[code_block_elab tacticStep]
def tacticStep : CodeBlockElab
  | args, str => do
    let () ← ArgParse.done.run args

    let altStr ← parserInputString str

    let p := andthen ⟨{}, whitespace⟩ <| andthen {fn := (fun _ => (·.pushSyntax (mkIdent `tacticSeq)))} (parserOfStack 0)
    match runParser (← getEnv) (← getOptions) p altStr (← getFileName) with
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<setup>" pos msg)
      throwErrorAt str "Failed to parse tactic step"
    | .ok stx =>
      let hlTac ← saveTactic stx
      let g ← DocElabM.genreExpr
      let which := .app (.const ``Verso.Genre.Manual.InlineLean.Block.lean []) (.const hlTac.getId [])
      let code := mkApp2 (.const ``Block.code []) g (mkStrLit str.getString)
      let code ← DocElabM.blockArray #[code]
      pure <| mkApp3 (.const ``Block.other []) g which code


open Lean.Parser in
@[role_elab tacticStep]
def tacticStepInline : RoleElab
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code( $tacStr:str )) := arg
      | throwErrorAt arg "Expected code literal with the example name"

    let altStr ← parserInputString tacStr

    let p := andthen ⟨{}, whitespace⟩ <| andthen {fn := (fun _ => (·.pushSyntax (mkIdent `tacticSeq)))} (parserOfStack 0)
    match runParser (← getEnv) (← getOptions) p altStr (← getFileName) with
    | .error es =>
      for (pos, msg) in es do
        log (severity := .error) (mkErrorStringWithPos  "<setup>" pos msg)
      throwErrorAt arg "Failed to parse tactic step"
    | .ok stx =>
      let hlTac ← saveTactic stx
      let g ← DocElabM.genreExpr
      let code := mkApp2 (.const ``Inline.code []) g (mkStrLit tacStr.getString)
      let which := .app (.const ``InlineLean.Inline.lean []) (.const hlTac.getId [])
      return mkApp3 (.const ``Inline.other []) g which (← DocElabM.inlineArray #[code])

structure StateConfig where
  tag : Option String := none
  «show» : Bool := true

def StateConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m StateConfig :=
  StateConfig.mk <$> .named `tag .string true <*> ((·.getD true) <$> .named `show .bool true)

@[code_block_elab pre]
def pre : CodeBlockElab
  | args, str => do
    let opts ← StateConfig.parse.run args
    let hlPre ← savePre str

    let g ← DocElabM.genreExpr
    if opts.show then
      let whichBlock : Expr := mkApp2 (.const ``Block.proofState []) (toExpr opts.tag) (.const hlPre.getId [])
      let codeBlock : Expr := mkApp2 (.const ``Doc.Block.code []) g (mkStrLit str.getString)
      return mkApp3 (.const ``Doc.Block.other []) g whichBlock (← DocElabM.blockArray #[codeBlock])
    else
      return mkApp2 (.const ``Block.concat []) g (← DocElabM.blockArray #[])


@[code_block_elab post]
def post : CodeBlockElab
  | args, str => do
    let opts ← StateConfig.parse.run args
    let hlPost ← savePost str

    let g ← DocElabM.genreExpr
    if opts.show then
      let whichBlock : Expr := mkApp2 (.const ``Block.proofState []) (toExpr opts.tag) (.const hlPost.getId [])
      let codeBlock : Expr := mkApp2 (.const ``Doc.Block.code []) g (mkStrLit str.getString)
      return mkApp3 (.const ``Doc.Block.other []) g whichBlock (← DocElabM.blockArray #[codeBlock])
    else
      return mkApp2 (.const ``Block.concat []) g (← DocElabM.blockArray #[])


private def specialNames :=  [``setup, ``goal, ``tacticStep, ``pre, ``post, ``tacticOutput]

@[directive_elab ref]
private def ref : DirectiveElab
  | args, #[] => do
    let (x : Ident) ← ArgParse.run (.positional' `name) args
    Term.elabTerm x (some (← DocElabM.blockType))
  | _, _ => throwError "Invalid use of `ref`"

@[role_elab ref]
private def refInline : RoleElab
  | args, #[] => do
    let (x : Ident) ← ArgParse.run (.positional' `name) args
    Term.elabTerm x (some (← DocElabM.inlineType))
  | _, _ => throwError "Invalid use of `ref`"

private partial def liftSpecialBlocks (stx : Syntax) : StateT (Array (Ident × (TSyntax `inline ⊕ TSyntax `block))) DocElabM Syntax :=
  stx.replaceM fun s =>
    match s with
    | `(block|```$nameStx:ident $_args*|$_contents:str```) => do
      let name ← realizeGlobalConstNoOverload nameStx
      if name ∈ specialNames then
        let x ← mkFreshUserName <| name.componentsRev.find? (· matches .str _ _) |>.getD `x
        let x := mkIdentFrom s x
        modify (·.push (x, .inr ⟨s⟩))
        let b' ← `(block|:::ref $x:ident {})
        pure (some b')
      else pure none
    | `(inline|role{$nameStx $_*}[$_contents*]) => do
      let name ← realizeGlobalConstNoOverload nameStx
      if name ∈ specialNames then
        let x ← mkFreshUserName <| name.componentsRev.find? (· matches .str _ _) |>.getD `x
        let x := mkIdentFrom s x
        modify (·.push (x, .inl ⟨s⟩))
        let i' ← `(inline|role{ref $x:ident}[])
        pure (some i')
      else pure none
    | _ => pure none

@[directive_elab tacticExample]
def tacticExample : DirectiveElab
 | args, blocks => do
    ArgParse.done.run args
    let g ← DocElabM.genreExpr
    try
      startExample
      let (blocks, lifted) ← StateT.run (blocks.mapM (liftSpecialBlocks ·.raw)) #[]
      let bt ← DocElabM.blockType
      let it ← DocElabM.inlineType
      -- First elaborate the special elements, which has a side effect on the environment extension
      let lifted ← lifted.mapM fun
        | (x, .inr b) => do
          let b ← elabBlock' b >>= instantiateMVars
          pure (x, bt, b)
        | (x, .inl i) => do
          let i ← elabInline' i >>= instantiateMVars
          pure (x, it, i)
      -- Use the extension's data to create helper definitions
      endExampleSetup
      -- Create definitions for the lifted blocks
      for (x, t, e) in lifted do
        addAndCompile <| .defnDecl {
          name := x.getId, levelParams := [], type := t, value := e, hints := .opaque, safety := .safe
        }
      -- Block until all helpers are ready before elaborating the final document
      for (x, _) in lifted do
        if (← getEnv).find? x.getId |>.isSome then continue else break

      let body ← blocks.mapM (elabBlock' ⟨·⟩)
      return mkApp2 (.const ``Block.concat []) g (← Meta.mkArrayLit (← DocElabM.blockType) body.toList)
    finally
      modifyEnv fun env =>
        tacticExampleCtx.setState env none
