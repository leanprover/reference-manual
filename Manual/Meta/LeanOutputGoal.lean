/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Manual.Meta.ExpectString
public import Verso.Doc.ArgParse
public meta import Manual.Meta.ExpectString
public meta import SubVerso.Examples.Messages
public meta import SubVerso.Examples.Messages.NormalizeMetavars
public meta import Verso.Doc.Elab.Block
public meta import VersoManual.InlineLean
public meta import VersoManual.InlineLean.Outputs
public import VersoManual.Basic

public section

namespace Manual

open Verso ArgParse Doc Elab Genre.Manual
open Lean Elab
open SubVerso.Highlighting
open SubVerso.Examples.Messages
open Verso.Genre.Manual.InlineLean (LeanOutputConfig getOutputs)

/-- The goals in a message that are tagged with the case name `name`. -/
meta partial def goalsNamed (name : String) :
    Highlighted.MessageContents Highlighted → Array (Highlighted.Goal Highlighted)
  | .goal g => if g.name == some name then #[g] else #[]
  | .append xs => xs.foldl (init := #[]) fun acc x => acc ++ goalsNamed name x
  | _ => #[]

/-- The case names of all the goals in a message. -/
meta partial def goalNames : Highlighted.MessageContents Highlighted → Array String
  | .goal g => g.name.toArray
  | .append xs => xs.foldl (init := #[]) fun acc x => acc ++ goalNames x
  | _ => #[]

/--
Arguments for `leanOutputGoal`: those of `leanOutput`, together with the case name of the goal to
show.
-/
meta def LeanOutputGoalConfig.parser {m : Type → Type}
    [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] :
    ArgParse m (LeanOutputConfig × String) :=
  Prod.mk <$> LeanOutputConfig.parser <*> .named `goal .string false

/--
Shows a single goal from the output of a named Lean block.

The goal is selected by its case name with the `goal` argument. The block's contents are compared
with the selected goal in the same way as with `leanOutput`, and the goal is rendered with the same
highlighting and hovers.
-/
@[code_block_expander leanOutputGoal]
meta def leanOutputGoal : CodeBlockExpander
  | args, str => do
    let (config, goal) ← LeanOutputGoalConfig.parser.run args
    let msgs ← getOutputs config.name
    let candidates : Array Highlighted.Message := msgs.toArray.filterMap fun msg =>
      match goalsNamed goal msg.contents with
      | #[g] => some { msg with contents := .goal g }
      | _ => none
    if candidates.isEmpty then
      let names := msgs.foldl (init := #[]) fun acc msg => acc ++ goalNames msg.contents
      throwErrorAt str
        m!"No goal named '{goal}' in the output '{config.name.getId}'. Goals in the output: {names}"
    let normalize (s : String) : String :=
      if config.normalizeMetas then normalizeMetavars s else s
    let expected := normalize str.getVersoCodeBlock
    let isMatch (msg : Highlighted.Message) : Bool :=
      let actual := normalize (msg.toString (expandTraces := config.expandTraces))
      messagesMatch
        (config.whitespace.apply expected.trimAscii.copy)
        (config.whitespace.apply actual.trimAscii.copy)
    let msg := (candidates.find? isMatch).getD candidates[0]!
    unless isMatch msg do
      let actual := msg.toString (expandTraces := config.expandTraces)
      let actual := if actual.endsWith "\n" then actual else actual ++ "\n"
      discard <| expectString "goal" str actual (useLine := (·.any (! Char.isWhitespace ·)))
    if let some s := config.severity then
      if s != msg.severity.toSeverity then
        throwErrorAt str s!"Expected a different severity for the output '{config.name.getId}'"
    if config.show then
      return #[← `(Block.other {Verso.Genre.Manual.InlineLean.Block.leanOutput with data := ToJson.toJson ($(quote msg), $(quote config.summarize), ($(quote config.expandTraces) : List Name))} #[Block.code $(quote str.getVersoCodeBlock)])]
    else
      return #[]
