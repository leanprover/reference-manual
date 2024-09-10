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
  logInfoAt proofPrefix st1
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
  logInfoAt tactic st2
  let goodPost ← (← addMessageContext st2).toString
  if post.getString != goodPost then
    logErrorAt post m!"Mismatch. Expected {indentD goodPost}\n but got {indentD post.getString}"

def checkTacticExample'
    (goal : Expr) (proofPrefix : Syntax) (tactic : Syntax)
    (pre : TSyntax `str) (post : TSyntax `str) :
    TermElabM
      (Array (Highlighted.Goal Highlighted) ×
        Array (Highlighted.Goal Highlighted) ×
        Highlighted) := do
  let mv ← Meta.mkFreshExprMVar (some goal)
  let Expr.mvar mvarId := mv
    | throwError "Not an mvar!"
  -- `runTactic` is too specialized for this purpose - we need to capture the unsolved goals, not
  -- throw them as an exception. This code is adapted from `runTactic`.
  let (remainingGoals, preTree) ← withInfoTreeContext (mkInfoTree := mkInfoTree `leanInline (← getRef)) do
    let remainingGoals ←
      withInfoHole mvarId <| Tactic.run mvarId <|
      withoutTacticIncrementality true <|
      withTacticInfoContext proofPrefix do
        -- also put an info node on the `by` keyword specifically -- the token may be `canonical` and thus shown in the info
        -- view even though it is synthetic while a node like `tacticCode` never is (#1990)
        evalTactic proofPrefix
    synthesizeSyntheticMVars (postpone := .no)
    pure remainingGoals

  -- `runTactic` extraction done. Now prettyprint the proof state.
  let st1 := goalsToMessageData remainingGoals
  logInfoAt proofPrefix st1
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
  let (remainingGoals', postTree) ← withInfoTreeContext (mkInfoTree := mkInfoTree `leanInline (← getRef)) do
    Tactic.run mvarId <|
    withoutTacticIncrementality true <|
    withTacticInfoContext tactic do
      set (Tactic.State.mk remainingGoals)
      evalTactic tactic
  let st2 := goalsToMessageData remainingGoals'
  logInfoAt tactic st2
  let goodPost ← (← addMessageContext st2).toString
  if post.getString.trim != goodPost.trim then
    Verso.Doc.Suggestion.saveSuggestion post (goodPost.take 30 ++ "…") (goodPost ++ "\n")
    logErrorAt post m!"Mismatch. Expected {indentD goodPost}\n but got {indentD post.getString}"

  let hlPost ← highlightProofState ci remainingGoals' (PersistentArray.empty.push postTree)
  -- TODO messages
  -- TODO suppress proof state bubbles here, at least as an option - `Inline.lean` needs to take that as an argument
  let hlTac ← highlight tactic #[] (PersistentArray.empty.push postTree)

  return (hlPre, hlPost, hlTac)
where
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

initialize tacticExampleCtx : Lean.EnvExtension (Option TacticExampleContext) ←
  Lean.registerEnvExtension (pure none)

def startExample [Monad m] [MonadEnv m] [MonadError m] [MonadQuotation m] (ref : Syntax) : m Unit := do
  match tacticExampleCtx.getState (← getEnv) with
  | some _ => throwError "Can't initialize - already in a context"
  | none =>
    let preName ← mkFreshIdent ref
    let tacticName ← mkFreshIdent ref
    let postName ← mkFreshIdent ref
    modifyEnv fun env =>
      tacticExampleCtx.setState env (some {preName, tacticName, postName})

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
  | some {goal, setup, pre, preName, tactic, tacticName, post, postName} =>
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

    let (hlPre, hlPost, hlTactic) ← checkTacticExample' goal setup tactic pre post

    `(let $preName := $(quote hlPre)
      let $postName := $(quote hlPost)
      let $tacticName := $(quote hlTactic)
      $body)

@[directive_expander tacticExample]
def tacticExample : DirectiveExpander
 | args, blocks => do
    ArgParse.done.run args
    startExample (← getRef)
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
        pure #[← `(Inline.other {Inline.lean with data := ToJson.toJson $(quote hls)} #[Inline.code $(quote term.getString)])]
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

@[code_block_expander tacticStep]
def tacticStep : CodeBlockExpander
  | args, str => do
    let () ← ArgParse.done.run args

    let altStr ← parserInputString str

    match Parser.runParserCategory (← getEnv) `tacticSeq altStr (← getFileName) with
    | .error e => throwErrorAt str e
    | .ok stx =>
      let hlTac ← saveTactic stx

      pure #[← `(Block.other {Block.lean with data := ToJson.toJson (α := Highlighted) $hlTac} #[Block.code $(quote str.getString)])]

@[role_expander tacticStep]
def tacticStepInline : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $tacStr:str }) := arg
      | throwErrorAt arg "Expected code literal with the example name"

    let altStr ← parserInputString tacStr

    match Parser.runParserCategory (← getEnv) `tactic altStr (← getFileName) with
    | .error e => throwErrorAt tacStr e
    | .ok stx =>
      let hlTac ← saveTactic stx

      pure #[← `(Inline.other {Inline.lean with data := ToJson.toJson (α := Highlighted) $hlTac} #[Inline.code $(quote tacStr.getString)])]

def Block.proofState : Block where
  name := `Manual.proofState

def proofState := ()

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
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle, proofStateStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize proof state while rendering HTML: " ++ err
        pure .empty
      | .ok (goals : Array (Highlighted.Goal Highlighted)) =>
        pure {{
          <div class="hl lean tactic-view">
            <div class="tactic-state">
              {{← if goals.isEmpty then
                  pure {{"All goals completed! 🐙"}}
                else
                  .seq <$> goals.mapIndexedM (fun ⟨i, _⟩ x => withCollapsedSubgoals .never <| x.toHtml (·.toHtml) i)}}
            </div>
          </div>
        }}

@[code_block_expander pre]
def pre : CodeBlockExpander
  | args, str => do
    let () ← ArgParse.done.run args
    let hlPre ← savePre str
    pure #[← `(Doc.Block.other {Block.proofState with data := ToJson.toJson (α := Array (Highlighted.Goal Highlighted)) $(hlPre)} #[Doc.Block.code $str])]


@[code_block_expander post]
def post : CodeBlockExpander
  | args, str => do
    let () ← ArgParse.done.run args
    let hlPost ← savePost str
    pure #[← `(Doc.Block.other {Block.proofState with data := ToJson.toJson (α := Array (Highlighted.Goal Highlighted)) $(hlPost)} #[Doc.Block.code $str])]
