/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import Mathlib

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

set_option maxHeartbeats 0
set_option maxRecDepth 10000000000

section

open Lean.Elab.Tactic.Doc

#eval do
  let tacs ← allTacticDocs
  return s!"There are {tacs.size} tactics"

/--
if we include more tactics than up to `have`,
it fails with deep recursion, but looks like chunking the tactics in multiple segments works.

`from` is included, `to` excluded.

-/
structure AllTacticsOptions where
  «from» : Option String
  «to» : Option String

open Lean Verso.ArgParse in
def AllTacticsOptions.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m AllTacticsOptions :=
  AllTacticsOptions.mk <$> .named `from .string true <*> .named `to .string true

open Lean Verso Doc Elab in
/-- Get all tactics from the environment and create a verso tactic block for each of them.

This is directly inspired by `Verso.Genre.Manual.tactic` which defined the `::tactic` syntax. -/
@[directive_expander all_tactics]
def all_tactics : DirectiveExpander
  -- the first (unused) parameter contains any arguments that would be
  -- passed to `all_tactics`, but we don't need any currently.
  | args, more => do
    let opts ← AllTacticsOptions.parse.run args

    let filter (tac : TacticDoc) : Bool :=
      (match opts.from with | some f => f ≤ tac.userName | none => true) && (match opts.to with | some t => tac.userName < t | none => true)

    -- get all tactics with their docs
    let tacs := (← allTacticDocs).filter filter|>.heapSort (·.userName < ·.userName)
    -- create an array containing one verso block per tactic
    let blocks : Array (TSyntax `term) ← tacs.mapM fun tactic => do
      Doc.PointOfInterest.save (← getRef) tactic.userName
      let doc := match tactic.userName with
      | "tfae_have" => tactic.docString.getD "" |>.replace "***\n" ""
      | _ => tactic.docString.getD ""
      let contents ← do
        let some mdAst := doc >>= MD4Lean.parse
          | throwError s!"Failed to parse docstring of {tactic.userName} as Markdown:\n{doc}"
        try
          mdAst.blocks.mapM (blockFromMarkdownWithLean [])
        catch e =>
          logWarning s!"({tactic.userName}): bad docstring"
          (⟨#[]⟩ : MD4Lean.Document).blocks.mapM (blockFromMarkdownWithLean [])
      return ← ``(Verso.Doc.Block.other (Block.tactic $(quote tactic) $(quote (none : Option String))) #[$(contents),*])
    return blocks

end

open Lean.Elab.Tactic

#doc (Manual) "All tactics" =>
%%%
tag := "all_tactics"
%%%

This list of tactics is automatically generated and contains all tactics known in Mathlib, regardless of which
package (Lean/Std/Batteries/Mathlib/etc.) defines them.

If you see two tactics which are almost identical, consider adding `tactic_alt TAC` to the variant version of a tactic to tell Lean to group them together.

:::all_tactics to:="g"
:::

:::all_tactics from:="g" to:="p"
:::

:::all_tactics from:="p"
:::
