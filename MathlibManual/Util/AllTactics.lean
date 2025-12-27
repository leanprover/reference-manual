/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/
import VersoManual
import Manual.Meta
import Mathlib

/-!
Implements a Verso syntax to display all tactics:

```lean
:::all_tactics (from := "c") (to := "e")
:::
```

The range is mainly because of timeout/max-heartbeat issues when the entire list is created in one go.
-/

open Verso.Genre Manual
open Lean.Elab.Tactic.Doc

/--
if we include more tactics than up to `have`,
it fails with deep recursion, but looks like chunking the tactics in multiple segments works.

`from` is included, `to` excluded.

-/
structure AllTacticsOptions where
  «from» : Option String
  «to» : Option String

open Lean in
def AllTacticsOptions.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : Verso.ArgParse m AllTacticsOptions :=
  AllTacticsOptions.mk <$> .named `from .string true <*> .named `to .string true

open Lean Verso Doc Elab in
/-- Get all tactics from the environment and create a verso tactic block for each of them.

This is directly inspired by `Verso.Genre.Manual.tactic` which defined the `::tactic` syntax. -/
@[directive_expander all_tactics]
def all_tactics : DirectiveExpander
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
      | "tfae_have" => tactic.docString.getD "" |>.replace "***\n" "" -- TODO
      | _ => tactic.docString.getD ""
      let content ← do
        let some mdAst := doc >>= MD4Lean.parse
          | throwError s!"Failed to parse docstring of {tactic.userName} as Markdown:\n{doc}"
        try
          mdAst.blocks.mapM (blockFromMarkdownWithLean [])
        catch e =>
          logWarning s!"({tactic.userName}): bad docstring"
          (⟨#[]⟩ : MD4Lean.Document).blocks.mapM (blockFromMarkdownWithLean [])
      return ← ``(Verso.Doc.Block.other (Block.tactic $(quote tactic) $(quote (none : Option String))) #[$(content),*])
    return blocks
