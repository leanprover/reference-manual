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
import VersoManual

import Manual.Meta.Basic
import Manual.Meta.PPrint
import Manual.Meta.Lean
import Manual.Meta.Lean.Scopes

namespace Manual

open Lean Elab Term Tactic
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open Manual.Meta.Lean.Scopes
open SubVerso.Highlighting

structure TacticOutputConfig where
  «show» : Bool := true
  severity : Option MessageSeverity
  summarize : Bool
  whitespace : GuardMsgs.WhitespaceMode

def TacticOutputConfig.parser [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m TacticOutputConfig :=
  TacticOutputConfig.mk <$>
    ((·.getD true) <$> .named `show .bool true) <*>
    .named `severity LeanOutputConfig.parser.sev true <*>
    ((·.getD false) <$> .named `summarize .bool true) <*>
    ((·.getD .exact) <$> .named `whitespace LeanOutputConfig.parser.ws true)


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

def startExample [Monad m] [MonadEnv m] [MonadError m] [MonadQuotation m] [MonadRef m] : m Unit := do
  match tacticExampleCtx.getState (← getEnv) with
  | some _ => throwError "Can't initialize - already in a context"
  | none =>
    let preName ← mkFreshIdent (← getRef)
    let tacticName ← mkFreshIdent (← getRef)
    let postName ← mkFreshIdent (← getRef)
    let outputSeverityName ← mkFreshIdent (← getRef)
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
      modifyEnv fun env => tacticExampleCtx.setState env (some {st with output := (output, options)})
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


def endExample (body : TSyntax `term) : DocElabM (TSyntax `term) := do
  match tacticExampleCtx.getState (← getEnv) with
  | none => throwErrorAt body "Can't end examples - never started"
  | some {goal, setup, pre, preName, tactic, tacticName, post, postName, output, outputSeverityName} =>
    modifyEnv fun env =>
      tacticExampleCtx.setState env none
    let some goal := goal
      | throwErrorAt body "No goal specified"
    let some setup := setup
      | throwErrorAt body "No setup specified"
    let some pre := pre
      | throwErrorAt body "No pre-state specified"
    let some tactic := tactic
      | throwErrorAt body "No tactic specified"
    let some post := post
      | throwErrorAt body "No post-state specified"

    let (hlPre, hlPost, hlTactic, outputSeverity) ← checkTacticExample' goal setup tactic pre post output

    `(let $preName : Array (Highlighted.Goal Highlighted) := $(quote hlPre)
      let $postName : Array (Highlighted.Goal Highlighted) := $(quote hlPost)
      let $tacticName : Highlighted := $(quote hlTactic)
      let $outputSeverityName : MessageSeverity := $(quote outputSeverity)
      $body)

@[directive_expander tacticExample]
def tacticExample : DirectiveExpander
 | args, blocks => do
    ArgParse.done.run args
    startExample
    let body ← blocks.mapM elabBlock
    let body' ← `(Verso.Doc.Block.concat #[$body,*]) >>= endExample
    pure #[body']


structure TacticGoalConfig where
  «show» : Bool

def TacticGoalConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m TacticGoalConfig :=
  TacticGoalConfig.mk <$> ((·.getD true) <$> .named `show .bool true)

@[role_expander goal]
def goal : RoleExpander
  | args, inlines => do
    let config ← TacticGoalConfig.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $term:str }) := arg
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

      if config.show then
        -- Just emit a normal Lean node - no need to do anything special with the rendered result
        pure #[← ``(Inline.other (Inline.lean $(quote hls)) #[Inline.code $(quote term.getString)])]
      else
        pure #[]
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
@[code_block_expander setup]
def setup : CodeBlockExpander
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
      pure #[]


open Lean.Parser in
@[code_block_expander tacticOutput]
def tacticOutput : CodeBlockExpander
  | args, str => do
    let opts ← TacticOutputConfig.parser.run args
    let outputSeverityName ← saveOutput str opts

    if opts.show then
      return #[← `(Block.other {Block.leanOutput with data := ToJson.toJson ($outputSeverityName, $(quote str.getString), $(quote opts.summarize))} #[Block.code $(quote str.getString)])]
    else
      return #[]


open Lean.Parser in
@[code_block_expander tacticStep]
def tacticStep : CodeBlockExpander
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
      pure #[← ``(Block.other (Block.lean $hlTac) #[Block.code $(quote str.getString)])]

open Lean.Parser in
@[role_expander tacticStep]
def tacticStepInline : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $tacStr:str }) := arg
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

      pure #[← ``(Inline.other (Inline.lean $hlTac) #[Inline.code $(quote tacStr.getString)])]

def Block.proofState : Block where
  name := `Manual.proofState

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
  | args, str => do
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
      pure #[← `(Doc.Block.other {Block.proofState with data := ToJson.toJson (α := Option String × Array (Highlighted.Goal Highlighted)) ($(quote opts.tag), $(quote hlState))} #[Doc.Block.code $(quote stStr)])]

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
  margin-top: 0.25em;
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
      pure <| some <| Block.other {Block.proofState with id := some id, data := ToJson.toJson (α := (Option String × _)) (none, v)} content

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

structure StateConfig where
  tag : Option String := none
  «show» : Bool := true

def StateConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m StateConfig :=
  StateConfig.mk <$> .named `tag .string true <*> ((·.getD true) <$> .named `show .bool true)

@[code_block_expander pre]
def pre : CodeBlockExpander
  | args, str => do
    let opts ← StateConfig.parse.run args
    let hlPre ← savePre str
    -- The quote step here is to prevent the editor from showing document AST internals when the
    -- cursor is on the code block
    if opts.show then
      pure #[← `(Doc.Block.other {Block.proofState with data := ToJson.toJson (α := Option String × Array (Highlighted.Goal Highlighted)) ($(quote opts.tag), $(hlPre))} #[Doc.Block.code $(quote str.getString)])]
    else
      pure #[]


@[code_block_expander post]
def post : CodeBlockExpander
  | args, str => do
    let opts ← StateConfig.parse.run args
    let hlPost ← savePost str
    -- The quote step here is to prevent the editor from showing document AST internals when the
    -- cursor is on the code block
    if opts.show then
      pure #[← `(Doc.Block.other {Block.proofState with data := ToJson.toJson (α := Option String × Array (Highlighted.Goal Highlighted)) ($(quote opts.tag), $(hlPost))} #[Doc.Block.code $(quote str.getString)])]
    else
      pure #[]
