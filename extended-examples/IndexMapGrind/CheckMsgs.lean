import Lean.Message
import Lean.DocString
import Lean.Elab.Command
import Lean.Elab.GuardMsgs
import SubVerso.Examples.Messages
import SubVerso.Highlighting

open Lean Elab Command Tactic GuardMsgs
open SubVerso.Examples.Messages
/--
A version of `#guard_msgs` that leaves the messages in the log for extraction.

The passthrough parts of the spec are ignored.
-/
syntax (name := checkMsgsCmd)
  (docComment)? "#check_msgs" (" (" &"maxDiff" " := " num "%" ")")? (ppSpace guardMsgsSpec)? " in" ppLine command : command

/-- Gives a string representation of a message without source position information.
Ensures the message ends with a '\n'. -/
private def messageToStringWithoutPos (msg : Message) : BaseIO String := do
  let mut str ← msg.data.toString
  unless msg.caption == "" do
    str := msg.caption ++ ":\n" ++ str
  if !("\n".isPrefixOf str) then str := " " ++ str
  match msg.severity with
  | MessageSeverity.information => str := "info:" ++ str
  | MessageSeverity.warning     => str := "warning:" ++ str
  | MessageSeverity.error       => str := "error:" ++ str
  if str.isEmpty || str.back != '\n' then
    str := str ++ "\n"
  return str

def messagesEq (maxDiff? : Option Nat) (whitespace : WhitespaceMode) (msg1 msg2 : String) : Bool × Option String := Id.run do
  let msg1 := normalizeLineNums <| normalizeMetavars msg1
  let msg2 := normalizeLineNums <| normalizeMetavars msg2
  if let some maxDiff := maxDiff? then
    let lines1 := msg1.splitToList (· == '\n') |>.map (·.trimAsciiEnd.copy |> whitespace.apply) |>.reverse |>.dropWhile String.isEmpty |>.reverse
    let lines2 := msg2.splitToList (· == '\n') |>.map (·.trimAsciiEnd.copy |> whitespace.apply) |>.reverse |>.dropWhile String.isEmpty |>.reverse
    let maxPercent := maxDiff.toFloat / 100.0
    let lines1 := lines1.toArray
    let lines2 := lines2.toArray
    let maxDiff := (min lines1.size lines2.size).toFloat * maxPercent |>.floor |>.toUInt64
    let mut ins : UInt64 := 0
    let mut del : UInt64 := 0
    let mut d : UInt64 := 0
    for (act, _) in Diff.diff lines1 lines2 do
      match act with
      | .insert => ins := ins + 1
      | .delete => del := del + 1
      | .skip =>
        d := d + max ins del
        ins := 0
        del := 0
    d := d + max ins del
    return (d ≤ maxDiff, some s!"{d}/{maxDiff} lines differ")
  else
    return (whitespace.apply msg1 == whitespace.apply msg2, none)


open Tactic.GuardMsgs in
@[command_elab checkMsgsCmd]
def elabCheckMsgs : CommandElab
  | `(command| $[$dc?:docComment]? #check_msgs%$tk $[(maxDiff := $maxDiff % )]? $(spec?)? in $cmd) => do
    let expected : String := (← dc?.mapM (getDocStringText ·)).getD ""
        |>.trimAscii.copy |> removeTrailingWhitespaceMarker
    let {whitespace, ordering, filterFn, .. } ← parseGuardMsgsSpec spec?
    let maxDiff? := maxDiff.map (·.getNat)
    let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
    -- do not forward snapshot as we don't want messages assigned to it to leak outside
    withReader ({ · with snap? := none }) do
      -- The `#guard_msgs` command is special-cased in `elabCommandTopLevel` to ensure linters only run once.
      elabCommandTopLevel cmd
    -- collect sync and async messages
    let msgs := (← get).messages ++
      (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) {}) {}
    -- clear async messages as we don't want them to leak outside
    modify ({ · with snapshotTasks := #[] })
    let mut toCheck : MessageLog := .empty
    let mut toPassthrough : MessageLog := .empty
    for msg in msgs.toList do
      match filterFn msg with
      | .check => toCheck := toCheck.add msg
      | .drop => pure ()
      | .pass => toPassthrough := toPassthrough.add msg
    let strings ← toCheck.toList.mapM (messageToStringWithoutPos ·)
    let strings := ordering.apply strings
    let res := "---\n".intercalate strings |>.trimAscii.copy
    let (same, msg?) := messagesEq maxDiff? whitespace expected res
    let text ← getFileMap
    let msg? : Option Message ← msg?.bindM fun s => OptionT.run do
      let ⟨pos, endPos⟩ ← OptionT.mk <| pure tk.getRange?
      return {
        fileName := (← getFileName),
        pos := text.toPosition pos,
        endPos := text.toPosition endPos,
        data := s,
        isSilent := true
        severity := .information
      }
    let msg := msg?.map (MessageLog.empty.add ·) |>.getD .empty
    if same then
      -- Passed. Put messages back on the log, downgrading errors to warnings while recording their original status
      modify fun st => { st with messages := initMsgs ++ SubVerso.Highlighting.Messages.errorsToWarnings msgs ++ msg }
    else
      -- Failed. Put all the messages back on the message log and add an error
      modify fun st => { st with messages := initMsgs ++ msgs ++ msg }
      let feedback :=
        let diff := Diff.diff (expected.splitToList (· == '\n')).toArray (res.splitToList (· == '\n')).toArray
        Diff.linesToString diff

      logErrorAt tk m!"❌️ Docstring on `#check_msgs` does not match generated message:\n\n{feedback}"
      pushInfoLeaf (.ofCustomInfo { stx := ← getRef, value := Dynamic.mk (GuardMsgFailure.mk res) })
  | _ => throwUnsupportedSyntax

attribute [command_code_action checkMsgsCmd] Tactic.GuardMsgs.guardMsgsCodeAction

syntax withPosition("discarding" (colGe command)* "stop " "discarding") : command
open Lean Elab Command in
elab_rules : command
  | `(discarding $cmds* stop discarding) => do
      withoutModifyingEnv do
        for c in cmds do
          elabCommand c
