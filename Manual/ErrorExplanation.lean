import Lean
import Verso.Doc
import Verso.Code
import VersoManual.Docstring
import Manual.Meta
import SubVerso.Highlighting

open Verso Doc Genre Manual

namespace Lean

structure ErrorExplanation.Metadata where
  severity : MessageSeverity
  sinceVersion : String
  deprecatedVersion : Option String := none
  summary : String

structure ErrorExplanation extends ErrorExplanation.Metadata where
  doc : String
  name : Name

initialize errorExplanationExt : MapDeclarationExtension String ← mkMapDeclarationExtension

end Lean

open Lean Elab Term in
private def attempt (str : String) (xs : List (String → DocElabM α)) : DocElabM α := do
  match xs with
  | [] => throwError "No attempt succeeded"
  | [x] => x str
  | x::y::xs =>
    let info ← getInfoState
    try
      setInfoState {}
      x str
    catch e =>
      if isAutoBoundImplicitLocalException? e |>.isSome then
        throw e
      else attempt str (y::xs)
    finally
      setInfoState info


-- TODO: look at `leanOutput`
open Lean Elab Term in
def tryElabBlockCode (str : String) : DocElabM Term := do
try
  attempt str [
    tryElabBlockCodeCommand,
    tryElabBlockCodeTerm,
    withTheReader Term.Context (fun ctx => {ctx with autoBoundImplicit := true}) ∘
      tryElabBlockCodeTerm
  ]
catch
  | .error ref e =>
    logWarningAt ref e
    ``(Verso.Doc.Block.code $(quote str))
  | e =>
    if isAutoBoundImplicitLocalException? e |>.isSome then
      throw e
    else
      logWarning m!"Internal exception uncaught: {e.toMessageData}"
      ``(Verso.Doc.Block.code $(quote str))

open Lean Meta Elab
open Manual.Meta.Lean.Scopes SubVerso.Highlighting

private def abbrevFirstLine (width : Nat) (str : String) : String :=
  let str := str.trimLeft
  let short := str.take width |>.replace "\n" "⏎"
  if short == str then short else short ++ "…"

def lean : CodeBlockExpander
  | args, str => withoutAsync <| do
    let config ← LeanBlockConfig.parse.run args

    PointOfInterest.save (← getRef) ((config.name.map toString).getD (abbrevFirstLine 20 str.getString))
      (kind := Lsp.SymbolKind.file)
      (detail? := some ("Lean code" ++ config.outlineMeta))

    let col? := (← getRef).getPos? |>.map (← getFileMap).utf8PosToLspPos |>.map (·.character)

    let origScopes ← if config.fresh then pure [{header := ""}] else getScopes

    -- Turn of async elaboration so that info trees and messages are available when highlighting syntax
    let origScopes := origScopes.modifyHead fun sc => {sc with opts := Elab.async.set sc.opts false}

    let altStr ← parserInputString str

    let ictx := Parser.mkInputContext altStr (← getFileName)
    let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString altStr, snap? := none, cancelTk? := none}

    let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := origScopes}
    let mut pstate := {pos := 0, recovering := false}
    let mut cmds := #[]

    repeat
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
      cmds := cmds.push cmd
      pstate := ps'
      cmdState := {cmdState with messages := messages}


      cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.lean, stx := cmd})) <|
        runCommand (Command.elabCommand cmd) cmd cctx cmdState

      if Parser.isTerminalCommand cmd then break

    let origEnv ← getEnv
    try
      setEnv cmdState.env
      setScopes cmdState.scopes

      for t in cmdState.infoState.trees do
        pushInfoTree t


      let mut hls := Highlighted.empty
      for cmd in cmds do
        hls := hls ++ (← highlight cmd cmdState.messages.toArray cmdState.infoState.trees)

      if let some col := col? then
        hls := hls.deIndent col

      if config.show.getD true then
        pure #[← ``(Block.other (Block.lean $(quote hls)) #[Block.code $(quote str.getString)])]
      else
        pure #[]
    finally
      if !config.keep.getD true then
        setEnv origEnv

      if let some name := config.name then
        let msgs ← cmdState.messages.toList.mapM fun msg => do

          let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
          let txt := withNewline <| head ++ (← msg.data.toString)

          pure (msg.severity, txt)
        modifyEnv (leanOutputs.modifyState · (·.insert name msgs))

      match config.error with
      | .none =>
        for msg in cmdState.messages.toArray do
          logMessage msg
      | some true =>
        if cmdState.messages.hasErrors then
          for msg in cmdState.messages.errorsToWarnings.toArray do
            logMessage msg
        else
          throwErrorAt str "Error expected in code block, but none occurred"
      | some false =>
        for msg in cmdState.messages.toArray do
          logMessage msg
        if cmdState.messages.hasErrors then
          throwErrorAt str "No error expected in code block, one occurred"

      if config.show.getD true then
        for (_line, lit, msg) in (← Meta.warnLongLines col? str) do
          logWarningAt lit msg
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str
  runCommand (act : Command.CommandElabM Unit) (stx : Syntax)
      (cctx : Command.Context) (cmdState : Command.State) :
      DocElabM Command.State := do
    let (output, cmdState) ←
      match (← liftM <| IO.FS.withIsolatedStreams <| EIO.toIO' <| (act.run cctx).run cmdState) with
      | (output, .error e) => logError e.toMessageData; pure (output, cmdState)
      | (output, .ok ((), cmdState)) => pure (output, cmdState)

    if output.trim.isEmpty then return cmdState

    let log : MessageData → Command.CommandElabM Unit :=
      if let some tok := firstToken? stx then logInfoAt tok
      else logInfo

    match (← liftM <| EIO.toIO' <| ((log output).run cctx).run cmdState) with
    | .error _ => pure cmdState
    | .ok ((), cmdState) => pure cmdState
