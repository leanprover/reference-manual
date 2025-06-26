/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.GuardMsgs
import SubVerso.Examples.Messages
open Lean Elab Command

open SubVerso.Examples.Messages (messagesMatch)

/--
A version of `#guard_msgs` that compares messages modulo metavariable and line number normalization.
-/
syntax (name := checkMsgsCmd)
  (docComment)? "#check_msgs" (ppSpace guardMsgsSpec)? " in" ppLine command : command

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


open Tactic.GuardMsgs in
@[command_elab checkMsgsCmd]
def elabCheckMsgs : CommandElab
  | `(command| $[$dc?:docComment]? #check_msgs%$tk $(spec?)? in $cmd) => do
    let expected : String := (← dc?.mapM (getDocStringText ·)).getD ""
        |>.trim |> removeTrailingWhitespaceMarker
    let (whitespace, ordering, specFn) ← parseGuardMsgsSpec spec?
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
      if msg.isSilent then
        continue
      match specFn msg with
      | .check => toCheck := toCheck.add msg
      | .drop => pure ()
      | .pass => toPassthrough := toPassthrough.add msg
    let strings ← toCheck.toList.mapM (messageToStringWithoutPos ·)
    let strings := ordering.apply strings
    let res := "---\n".intercalate strings |>.trim
    if messagesMatch (whitespace.apply expected) (whitespace.apply res) then
      -- Passed. Only put toPassthrough messages back on the message log
      modify fun st => { st with messages := initMsgs ++ toPassthrough }
    else
      -- Failed. Put all the messages back on the message log and add an error
      modify fun st => { st with messages := initMsgs ++ msgs }
      let feedback :=
        if guard_msgs.diff.get (← getOptions) then
          let diff := Diff.diff (expected.split (· == '\n')).toArray (res.split (· == '\n')).toArray
          Diff.linesToString diff
        else res
      logErrorAt tk m!"❌️ Docstring on `#guard_msgs` does not match generated message:\n\n{feedback}"
      pushInfoLeaf (.ofCustomInfo { stx := ← getRef, value := Dynamic.mk (GuardMsgFailure.mk res) })
  | _ => throwUnsupportedSyntax


attribute [command_code_action checkMsgsCmd] Tactic.GuardMsgs.guardMsgsCodeAction
