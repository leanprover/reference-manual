import Lean
import SubVerso.Highlighting

open Lean Meta Elab Term SubVerso Highlighting

structure ExtractedExample where
  highlighted : Highlighted
  messages : Array (MessageSeverity × String)
  hash : UInt64
  deriving ToJson, FromJson

def processMWE (input : String) (inputHash : UInt64) : IO ExtractedExample := do
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (hdrStx, s, msgs) ← Parser.parseHeader inputCtx
  let (env, msgs) ← processHeader hdrStx {} msgs inputCtx
  let cmdState := Command.mkState env msgs

  -- If header processing failed, don't try to elaborate the body; however, we
  -- must still parse it for the syntax highlighter
  let shouldElab := !msgs.hasErrors
  let mut (cmdState, stxs) ← processCommands inputCtx s cmdState shouldElab
  stxs := #[hdrStx] ++ stxs
  let stxWithUnparsed := addMissingSubstrs stxs inputCtx
  let nonSilentMsgs := cmdState.messages.toArray.filter (!·.isSilent)
  let hls ← mkHighlights cmdState nonSilentMsgs inputCtx stxWithUnparsed
  let msgs ← mkMessages nonSilentMsgs
  return {
    highlighted := hls
    messages := msgs
    hash := inputHash
  }
where
  processCommands (inputCtx : Parser.InputContext) (s : Parser.ModuleParserState) (cmdState : Command.State) (doElab : Bool) := do
    let mut s := s
    let mut cmdState := cmdState
    let mut stxs := #[]
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
      cmdState := {cmdState with messages := msgs'}
      stxs := stxs.push stx
      if doElab then
        (_, cmdState) ← runCommandElabM (Command.elabCommandTopLevel stx) inputCtx cmdState s
      if Parser.isTerminalCommand stx then
        break
    return (cmdState, stxs)

  addMissingSubstrs (stxs : Array Syntax) (inputCtx : Parser.InputContext) : Array (Syntax ⊕ Substring) := Id.run do
    -- Fill in the (malformed) source that was skipped by the parser
    let mut last : String.Pos := 0
    let mut stxOrStrs : Array (Syntax ⊕ Substring) := #[]
    for stx in stxs do
      let some this := stx.getPos?
        | stxOrStrs := stxOrStrs.push (.inl stx)  -- empty headers have no info
          continue
      if this != last then
        let missedStr := Substring.mk inputCtx.input last this
        stxOrStrs := stxOrStrs.push (.inr missedStr)
      stxOrStrs := stxOrStrs.push (.inl stx)
      last := stx.getTrailingTailPos?.getD this
    return stxOrStrs

  -- TODO: process messages linearly -- calling this repeatedly for s spans with
  -- an m-message log should be O(max(m,s)), not O(m*s)
  findMessagesForUnparsedSpan (ictx : Parser.InputContext) (src : Substring) (msgs : Array Message) : IO Highlighted := do
    let msgsHere := msgs.filterMap fun m =>
      let pos := ictx.fileMap.ofPosition m.pos
      let endPos := ictx.fileMap.ofPosition (m.endPos.getD m.pos)
      if src.startPos ≤ pos && pos ≤ src.stopPos then
        some (m, pos, min src.stopPos endPos)
      else
        none

    if msgsHere.isEmpty then
      return .text src.toString

    let mut res := #[]
    for (msg, start, fin) in msgsHere do
      if src.startPos < start then
        let initialSubstr := { src with stopPos := start }
        res := res.push (.text initialSubstr.toString)
      let kind : Highlighted.Span.Kind :=
        match msg.severity with
        | .error => .error
        | .warning => .warning
        | .information => .info
      let content := { src with startPos := start, stopPos := fin }
      res := res.push (.span #[(kind, ← openUntil.contents msg)] (.text content.toString))
      if fin < src.stopPos then
        let finalSubstr := { src with startPos := fin }
        res := res.push (.text finalSubstr.toString)
    return .seq res

  withNewline (str : String) :=
    if str == "" || str.back != '\n' then str ++ "\n" else str

  mkHighlights (cmdState : Command.State) (nonSilentMsgs : Array Message)
      (inputCtx : Parser.InputContext) (cmds : Array (Syntax ⊕ Substring)) :
      IO Highlighted :=
    let termElab : TermElabM Highlighted := do
      let mut hls := Highlighted.empty
      for cmd in cmds do
        let hl ←
          match cmd with
          | .inl cmd => withTheReader Core.Context (fun ctx => { ctx with
                  fileMap := inputCtx.fileMap
                  fileName := inputCtx.fileName }) <|
                highlight cmd nonSilentMsgs cmdState.infoState.trees
          | .inr cmd =>
            findMessagesForUnparsedSpan inputCtx cmd nonSilentMsgs
        hls := hls ++ hl
      return hls
    Prod.fst <$> runCommandElabM (Command.liftTermElabM termElab) inputCtx cmdState

  mkMessages (nonSilentMsgs : Array Message) := do
    let msgs ← nonSilentMsgs.mapM fun msg => do
      let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
      let txt := withNewline <| head ++ (← msg.data.toString)

      pure (msg.severity, txt)
    let msgs : Array (MessageSeverity × String) := FromJson.fromJson? (ToJson.toJson msgs) |>.toOption.get!
    return msgs

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

partial def readStdin : IO String :=
  loop #[]
where
  loop acc := do
    let line ← (← IO.getStdin).getLine
    if line.isEmpty then
      return ("\n".intercalate acc.toList)
    else
      loop (acc.push line)

structure Result where
  code : String
  messages : Array String

def hasUsableCache (path : System.FilePath) (hash : UInt64) : IO Bool := do
  if (← System.FilePath.pathExists path) then
    let cachedFile ← IO.FS.readFile path
    if let .ok json := Json.parse cachedFile then
      if let .ok ex := FromJson.fromJson? (α := ExtractedExample) json then
        return ex.hash == hash
  return false

unsafe def main (args : List String) : IO UInt32 := do
  let [outputDir, mweName] := args
    | IO.eprintln "Usage: extract_explanation_example output-directory mwe-name"
      return 1
  let input ← readStdin
  let inputHash := hash input
  let jsonPath := (outputDir : System.FilePath) / (mweName ++ ".json")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  unless (← hasUsableCache jsonPath inputHash) do
    let ex ← processMWE input inputHash
    let outStr := (toJson ex).compress
    IO.FS.createDirAll outputDir
    IO.FS.writeFile jsonPath outStr
  return 0
