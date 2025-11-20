/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import Lean.ErrorExplanations
import SubVerso.Highlighting

/-!
Tool for extracting rendering data from a batch of error-explanation MWEs with
identical imports. We use this in a preprocessing step rather than during the
manual's elaboration so that we can group MWEs with the same imports, which
avoids the sizable performance overhead of reloading the environment for each
example.
-/

open Lean Meta Elab Term SubVerso Highlighting

structure ExtractedExample where
  highlighted : Highlighted
  messages : Array (MessageSeverity × String)
  hash : UInt64
  version : String
  deriving ToJson, FromJson

/-- Returns the result of processing this example as well as the environment and message log
produced *only* by the header-processing step (which is taken to be `envWithMsgs?` if it's supplied) -/
def processMWE (input : String) (inputHash : UInt64) (envWithMsgs? : Option (Environment × MessageLog)) :
    IO (ExtractedExample × Environment × MessageLog) := do
  let fileName   := "Main.lean"
  let inputCtx   := Parser.mkInputContext input fileName
  let (hdrStx, s, msgs) ← Parser.parseHeader inputCtx
  let (env, msgs') ← envWithMsgs?.getDM <| processHeader hdrStx {} {} inputCtx
  let msgs := msgs ++ msgs'
  let cmdState := Command.mkState env msgs

  -- If header processing failed, don't try to elaborate the body; however, we
  -- must still parse it for the syntax highlighter
  let shouldElab := !msgs.hasErrors
  let mut (cmdState, stxs) ← processCommands inputCtx s cmdState shouldElab
  stxs := #[hdrStx] ++ stxs
  let nonSilentMsgs := cmdState.messages.toArray.filter (!·.isSilent)
  let hls ← mkHighlights cmdState nonSilentMsgs inputCtx stxs
  let msgs ← mkMessages nonSilentMsgs
  let ex := {
    highlighted := hls
    messages := msgs
    hash := inputHash
    version := Lean.versionString
  }
  return (ex, env, msgs')
where
  processCommands (inputCtx : Parser.InputContext) (s : Parser.ModuleParserState) (cmdState : Command.State) (doElab : Bool) := do
    let mut s := s
    let mut cmdState := cmdState
    let mut stxs := #[]
    let mut msgs := {}
    repeat
      let scope := cmdState.scopes.head!
      let pmctx : Parser.ParserModuleContext := {
        env := cmdState.env,
        options := scope.opts,
        currNamespace := scope.currNamespace,
        openDecls := scope.openDecls
      }
      let (stx, s', msgs') := Parser.parseCommand inputCtx pmctx s cmdState.messages
      s := s'
      msgs := msgs ++ msgs'
      stxs := stxs.push stx
      if doElab then
        (_, cmdState) ← runCommandElabM (Command.elabCommandTopLevel stx) inputCtx cmdState s
      if Parser.isTerminalCommand stx then
        break
    return ({ cmdState with messages := msgs }, stxs)

  withNewline (str : String) :=
    if str == "" || str.back != '\n' then str ++ "\n" else str

  mkHighlights (cmdState : Command.State) (nonSilentMsgs : Array Message)
      (inputCtx : Parser.InputContext) (cmds : Array Syntax) :
      IO Highlighted :=
    let termElab : TermElabM Highlighted := do
      let mut hls := Highlighted.empty
      let mut lastPos : String.Pos.Raw := 0
      for cmd in cmds do
        let hl ← highlightIncludingUnparsed cmd nonSilentMsgs cmdState.infoState.trees [] lastPos
        hls := hls ++ hl
        lastPos := (cmd.getTrailingTailPos?).getD lastPos
      return hls
    Prod.fst <$> runCommandElabM (Command.liftTermElabM termElab) inputCtx cmdState

  mkMessages (nonSilentMsgs : Array Message) := do
    nonSilentMsgs.mapM fun msg => do
      let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
      let txt := withNewline <| head ++ (← msg.data.toString)
      pure (msg.severity, txt)

  runCommandElabM {α} (x : Command.CommandElabM α) (ictx : Parser.InputContext)
      (cmdState : Command.State) (s? : Option Parser.ModuleParserState := none) :
      IO (α × Command.State) := do
    let ctx : Command.Context := {
      cmdPos := s?.map (·.pos) |>.getD 0
      fileName := ictx.fileName
      fileMap := ictx.fileMap
      snap? := none
      cancelTk? := none
    }
    let eio := x.run ctx |>.run cmdState
    match (← eio.toIO') with
    | .ok res => return res
    | .error e => throw <| IO.userError (← e.toMessageData.toString)

def writeEx (outDir : System.FilePath) (id : String) (json : String) : IO Unit := do
  if ! (← System.FilePath.pathExists outDir) then
    IO.FS.createDir outDir
  let path := outDir / (id ++ ".json")
  IO.FS.writeFile path json

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let outDir :: inFiles := args |
    throw <| IO.userError "Usage: extract_explanation_examples <out-dir> <input-files...>\n\
      where all input files have the same imports"
  let mut envWithMsgs? : Option (Environment × MessageLog) := none
  for file in inFiles do
    let input ← IO.FS.readFile file
    let inputHash := hash input
    let some exampleName := (file : System.FilePath).fileStem |
      throw <| IO.userError s!"Malformed file path: {file}"
    let (ex, env, msgs) ← processMWE input inputHash envWithMsgs?
    envWithMsgs? := some (env, msgs)
    let json := (toJson ex).compress
    writeEx outDir exampleName json
  return 0
