/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Term
import Lean.Elab.Tactic
import Lean.Elab.Tactic.Grind
import Lean.Elab.Tactic.Grind.ShowState

import Verso.Code.Highlighted
import Verso.Doc.ArgParse
import SubVerso.Highlighting.Code
import VersoManual

import Manual.Meta.Basic
import Manual.Meta.Tactics

open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open Lean Elab Term Tactic
open SubVerso.Highlighting
open Lean.Meta.Grind (Filter)
open Lean.Elab.Tactic.Grind (GrindTacticM evalGrindTactic getUnsolvedGoalMVarIds showState withMainContext)

namespace Manual

/--
The result of elaborating a `grind`/`sym` interactive tactic example: the highlighted goal state and
captured `grind` whiteboard before and after the demonstrated step, plus the highlighted step.
-/
structure GrindExampleResult where
  preGoals : Array (Highlighted.Goal Highlighted)
  postGoals : Array (Highlighted.Goal Highlighted)
  preGoalsStr : String
  postGoalsStr : String
  step : Highlighted
  preStateMsg : Highlighted.Message
  postStateMsg : Highlighted.Message
  preStateStr : String
  postStateStr : String

private partial def disableLinter : InfoTree → InfoTree
  | .context (.commandCtx ci) child =>
    .context (.commandCtx { ci with options := Lean.Linter.linter.unusedVariables.set ci.options false })
      (disableLinter child)
  | .context pci child => .context pci (disableLinter child)
  | .node info children => .node info (children.map disableLinter)
  | .hole id => .hole id

private def mkCtxInfoTree [Monad m] [MonadEnv m] [MonadFileMap m] [MonadOptions m] [MonadNameGenerator m] [MonadResolveName m]
    (elaborator : Name) (stx : Syntax) (trees : PersistentArray InfoTree) : m InfoTree := do
  let tree := InfoTree.node (Info.ofCommandInfo { elaborator, stx }) (trees.map disableLinter)
  let ctx := PartialContextInfo.commandCtx {
    env := ← getEnv, fileMap := ← getFileMap, mctx := {}, currNamespace := ← getCurrNamespace,
    openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
  }
  return InfoTree.context ctx tree

private def withTrees {m α} [Monad m] [MonadInfoTree m] [MonadFinally m]
    (x : m α) (mk : PersistentArray InfoTree → m InfoTree) : m (α × InfoTree) := do
  let saved ← getResetInfoTrees
  MonadFinally.tryFinally' x fun _ => do
    let tree ← mk (← getInfoState).trees
    modifyInfoState fun s => { s with trees := saved.push tree }
    pure tree

/-- Captures the messages logged while running `x`. -/
private def captureMessages (x : GrindTacticM Unit) : GrindTacticM (List Message) := do
  let init ← Core.getMessageLog
  try
    Core.resetMessageLog
    x
    pure (← Core.getMessageLog).toList
  finally Core.setMessageLog init

/-- Highlights the `grind` whiteboard messages into one structured message, with its plain text. -/
private def captureWhiteboard (x : GrindTacticM Unit) : GrindTacticM (Highlighted.Message × String) := do
  let msgs ← captureMessages x
  let str := "\n".intercalate (← msgs.mapM (·.data.toString))
  match msgs with
  | [m] => return (← highlightMessage m, str)
  | _ => return (.ofSeverityString .information str, str)

/--
Elaborates a `grind`/`sym` interactive example. Runs `setup` as ordinary tactics, enters the
interactive engine on the resulting goal (with eager preprocessing unless `sym`), runs `grindPrefix`,
captures the goal state and whiteboard, runs `step`, and captures them again.
-/
def checkGrindExample
    (goal : Expr) (setup : Option Syntax) (grindPrefix : Option Syntax) (step : Syntax) (sym : Bool) :
    TermElabM GrindExampleResult := do
  let mv ← Meta.mkFreshExprMVar (some goal)
  let .mvar mvarId := mv | throwError "Not an mvar!"
  let params ← Lean.Meta.Grind.mkDefaultParams {}

  let preGoalsRef ← IO.mkRef ([] : List MVarId)
  let postGoalsRef ← IO.mkRef ([] : List MVarId)
  let preGoalsStrRef ← IO.mkRef ""
  let postGoalsStrRef ← IO.mkRef ""
  let emptyMsg : Highlighted.Message := .ofSeverityString .information ""
  let preStateRef ← IO.mkRef (emptyMsg, "")
  let postStateRef ← IO.mkRef (emptyMsg, "")
  let preTreeRef ← IO.mkRef (none : Option InfoTree)
  let postTreeRef ← IO.mkRef (none : Option InfoTree)

  let goalsStr (goals : List MVarId) : GrindTacticM String := do
    (← addMessageContext (goalsToMessageData goals)).toString

  let go : GrindTacticM Unit := do
    let ((), preTree) ← withTrees (mk := mkCtxInfoTree `grindExample (← getRef)) do
      if let some pfx := grindPrefix then evalGrindTactic pfx
    preTreeRef.set (some preTree)
    let preGoals ← getUnsolvedGoalMVarIds
    preGoalsRef.set preGoals
    preGoalsStrRef.set (← goalsStr preGoals)
    preStateRef.set (← captureWhiteboard (withMainContext (showState Filter.true)))
    let ((), postTree) ← withTrees (mk := mkCtxInfoTree `grindExample (← getRef)) do
      evalGrindTactic step
    postTreeRef.set (some postTree)
    let postGoals ← getUnsolvedGoalMVarIds
    postGoalsRef.set postGoals
    postGoalsStrRef.set (← goalsStr postGoals)
    postStateRef.set (← captureWhiteboard (withMainContext (showState Filter.true)))

  discard <| Tactic.run mvarId do
    withoutTacticIncrementality true do
      if let some s := setup then evalTactic s
    let mainGoal ← getMainGoal
    discard <| Lean.Elab.Tactic.Grind.GrindTacticM.runAtGoal mainGoal params go (sym := sym)

  let ci : ContextInfo := {
    env := ← getEnv, fileMap := ← getFileMap, ngen := ← getNGen,
    mctx := ← getMCtx, options := ← getOptions,
    currNamespace := ← getCurrNamespace, openDecls := ← getOpenDecls
  }
  let preTrees := (← preTreeRef.get).toArray.toPArray'
  let postTrees := (← postTreeRef.get).toArray.toPArray'
  let preGoals ← highlightProofState ci (← preGoalsRef.get) preTrees
  let postGoals ← highlightProofState ci (← postGoalsRef.get) postTrees
  let hlStep ← highlight step #[] postTrees

  let (preStateMsg, preStateStr) ← preStateRef.get
  let (postStateMsg, postStateStr) ← postStateRef.get
  return {
    preGoals, postGoals, step := hlStep
    preGoalsStr := ← preGoalsStrRef.get, postGoalsStr := ← postGoalsStrRef.get
    preStateMsg, postStateMsg, preStateStr, postStateStr
  }

/-! ## The `grindTacticExample` directive -/

open Lean.Doc.Syntax in
open Manual (TacticOutputConfig)

structure GrindExampleContext where
  sym : Bool
  goal : Option Expr := none
  setup : Option Syntax := none
  grindPrefix : Option Syntax := none
  step : Option Syntax := none
  seenStep : Bool := false
  prePS : Option (TSyntax `str) := none
  postPS : Option (TSyntax `str) := none
  preGS : Option (TSyntax `str × TacticOutputConfig) := none
  postGS : Option (TSyntax `str × TacticOutputConfig) := none
  preGoalsName : Ident
  postGoalsName : Ident
  stepName : Ident
  preStateName : Ident
  postStateName : Ident

initialize grindExampleCtx : EnvExtension (Option GrindExampleContext) ←
  registerEnvExtension (pure none)

variable [Monad m] [MonadEnv m] [MonadError m] [MonadQuotation m] [MonadRef m]

private def getCtx : m GrindExampleContext := do
  match grindExampleCtx.getState (← getEnv) with
  | some st => return st
  | none => throwError "Not in a grind tactic example"

private def setCtx (st : GrindExampleContext) : m Unit := do
  modifyEnv fun env => grindExampleCtx.setState env (some st)

def startGrindExample (sym : Bool) : m Unit := do
  if (grindExampleCtx.getState (← getEnv)).isSome then
    throwError "Already in a grind tactic example"
  let preGoalsName ← mkFreshIdent (← getRef)
  let postGoalsName ← mkFreshIdent (← getRef)
  let stepName ← mkFreshIdent (← getRef)
  let preStateName ← mkFreshIdent (← getRef)
  let postStateName ← mkFreshIdent (← getRef)
  setCtx { sym, preGoalsName, postGoalsName, stepName, preStateName, postStateName }

def saveGrindGoal (goal : Expr) : m Unit := do
  let st ← getCtx
  if st.goal.isSome then throwError "Goal already specified"
  setCtx { st with goal := goal }

def saveGrindSetup (setup : Syntax) : m Unit := do
  let st ← getCtx
  if st.setup.isSome then throwError "Setup already specified"
  setCtx { st with setup }

def saveGrindPrefix (grindPrefix : Syntax) : m Unit := do
  let st ← getCtx
  if st.grindPrefix.isSome then throwError "Grind prefix already specified"
  setCtx { st with grindPrefix }

/-- Saves the demonstrated step and returns the ident bound to its highlighting. -/
def saveGrindStep (step : Syntax) : m Ident := do
  let st ← getCtx
  if st.step.isSome then throwError "Step already specified"
  setCtx { st with step, seenStep := true }
  return st.stepName

/-- Saves a proof state, before or after the step depending on position, returning its goals ident. -/
def saveGrindProofState (str : TSyntax `str) : m Ident := do
  let st ← getCtx
  if st.seenStep then
    if st.postPS.isSome then throwError "Final proof state already specified"
    setCtx { st with postPS := some str }
    return st.postGoalsName
  else
    if st.prePS.isSome then throwError "Initial proof state already specified"
    setCtx { st with prePS := some str }
    return st.preGoalsName

/-- Saves a grind state, before or after the step depending on position, returning its message ident. -/
def saveGrindState (str : TSyntax `str) (opts : TacticOutputConfig) : m Ident := do
  let st ← getCtx
  if st.seenStep then
    if st.postGS.isSome then throwError "Final grind state already specified"
    setCtx { st with postGS := some (str, opts) }
    return st.postStateName
  else
    if st.preGS.isSome then throwError "Initial grind state already specified"
    setCtx { st with preGS := some (str, opts) }
    return st.preStateName

open scoped Lean.Doc.Syntax
open Verso.Genre.Manual.InlineLean.Scopes (runWithOpenDecls runWithVariables)

open Lean.Parser in
/-- Parses `str` as a sequence in the syntax category `cat` (e.g. `tacticSeq` or `grindSeq`). -/
private def parseSeq (cat : Name) (str : TSyntax `str) : DocElabM Syntax := do
  let altStr ← parserInputString str
  let p := andthen ⟨{}, whitespace⟩ <|
    andthen {fn := (fun _ => (·.pushSyntax (mkIdent cat)))} (parserOfStack 0)
  match runParser (← getEnv) (← getOptions) p altStr (← getFileName) with
  | .error es =>
    for (pos, msg) in es do
      log (severity := .error) (mkErrorStringWithPos "<grind example>" pos msg)
    throwErrorAt str s!"Failed to parse as `{cat}`"
  | .ok stx => pure stx

@[role_expander grindGoal]
def grindGoal : RoleExpander
  | args, inlines => do
    let config ← TacticGoalConfig.parse.run args
    let #[arg] := inlines | throwError "Expected exactly one argument"
    let `(inline|code( $term:str )) := arg
      | throwErrorAt arg "Expected code literal with the goal"
    let altStr ← parserInputString term
    match Parser.runParserCategory (← getEnv) `term altStr (← getFileName) with
    | .error e => throwErrorAt term e
    | .ok stx =>
      let goalExpr ← runWithOpenDecls <| runWithVariables fun _ => Elab.Term.elabTerm stx none
      saveGrindGoal goalExpr
      if config.show then
        let hls ← highlight stx #[] {}
        pure #[← ``(Inline.other (Verso.Genre.Manual.InlineLean.Inline.lean $(quote hls)) #[Inline.code $(quote term.getString)])]
      else pure #[]

@[code_block_expander grindSetup]
def grindSetup : CodeBlockExpander
  | args, str => do
    ArgParse.done.run args
    saveGrindSetup (← parseSeq `tacticSeq str)
    pure #[]

@[code_block_expander grindPrefix]
def grindPrefix : CodeBlockExpander
  | args, str => do
    ArgParse.done.run args
    saveGrindPrefix (← parseSeq `Lean.Parser.Tactic.Grind.grindSeq str)
    pure #[← `(Block.code $(quote str.getString))]

@[code_block_expander grindStep]
def grindStep : CodeBlockExpander
  | args, str => do
    ArgParse.done.run args
    let stepStx ← parseSeq `Lean.Parser.Tactic.Grind.grindSeq str
    let stepName ← saveGrindStep stepStx
    pure #[← ``(Block.other (Verso.Genre.Manual.InlineLean.Block.lean $stepName) #[Block.code $(quote str.getString)])]

@[code_block_expander grindProofState]
def grindProofState : CodeBlockExpander
  | args, str => do
    let opts ← StateConfig.parse.run args
    let goalsName ← saveGrindProofState str
    if opts.show then
      pure #[← `(Block.other {Block.proofState with data := ToJson.toJson (α := Option String × Array (Highlighted.Goal Highlighted)) ($(quote opts.tag), $goalsName)} #[Block.code $(quote str.getString)])]
    else pure #[]

@[code_block_expander grindState]
def grindState : CodeBlockExpander
  | args, str => do
    let opts ← TacticOutputConfig.parser.run args
    let stateName ← saveGrindState str opts
    if opts.show then
      pure #[← `(Block.other {Verso.Genre.Manual.InlineLean.Block.leanOutput with data := ToJson.toJson ($stateName, $(quote opts.summarize), ($(quote opts.expandTraces) : List Name))} #[Block.code $(quote str.getString)])]
    else pure #[]

def endGrindExample (body : TSyntax `term) : DocElabM (TSyntax `term) := do
  let st ← getCtx
  modifyEnv fun env => grindExampleCtx.setState env none
  let some goal := st.goal | throwErrorAt body "No goal specified"
  let some step := st.step | throwErrorAt body "No step specified"
  let some (preGSStr, preCfg) := st.preGS | throwErrorAt body "No initial grind state specified"
  let some (postGSStr, postCfg) := st.postGS | throwErrorAt body "No final grind state specified"
  let r ← checkGrindExample goal st.setup st.grindPrefix step st.sym
  if let some pre := st.prePS then checkText pre r.preGoalsStr "proof state"
  if let some post := st.postPS then checkText post r.postGoalsStr "proof state"
  checkWs preGSStr r.preStateStr preCfg
  checkWs postGSStr r.postStateStr postCfg
  let preGoalsName := st.preGoalsName
  let postGoalsName := st.postGoalsName
  let stepName := st.stepName
  let preStateName := st.preStateName
  let postStateName := st.postStateName
  `(let $preGoalsName : Array (Highlighted.Goal Highlighted) := $(quote r.preGoals)
    let $postGoalsName : Array (Highlighted.Goal Highlighted) := $(quote r.postGoals)
    let $stepName : Highlighted := $(quote r.step)
    let $preStateName : Highlighted.Message := $(quote r.preStateMsg)
    let $postStateName : Highlighted.Message := $(quote r.postStateMsg)
    $body)
where
  checkText (expected : TSyntax `str) (actual : String) (what : String) : DocElabM Unit := do
    if expected.getString.trimAscii != actual.trimAscii then
      Verso.Doc.Suggestion.saveSuggestion expected ((actual.take 30).copy ++ "…") (actual ++ "\n")
      logErrorAt expected m!"Mismatch in {what}. Expected:{indentD actual}\nGot:{indentD expected.getString}"
  checkWs (expected : TSyntax `str) (actual : String) (opts : TacticOutputConfig) : DocElabM Unit := do
    if opts.whitespace.apply expected.getString.trimAscii.copy != opts.whitespace.apply actual.trimAscii.copy then
      Verso.Doc.Suggestion.saveSuggestion expected ((actual.take 30).copy ++ "…") (actual ++ "\n")
      logErrorAt expected m!"Grind state mismatch. Expected:{indentD actual}\nGot:{indentD expected.getString}"

structure GrindExampleConfig where
  sym : Bool := false

def GrindExampleConfig.parse [Monad m] [MonadError m] : ArgParse m GrindExampleConfig :=
  GrindExampleConfig.mk <$> .flag `sym false

@[directive_expander grindTacticExample]
def grindTacticExample : DirectiveExpander
  | args, blocks => do
    let config ← GrindExampleConfig.parse.run args
    startGrindExample config.sym
    let body ← blocks.mapM elabBlock
    let body' ← `(Verso.Doc.Block.concat #[$body,*]) >>= endGrindExample
    pure #[body']
