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


section

open Lean.Elab.Tactic.Doc

-- set_option pp.deepTerms.threshold 500 in
-- #eval do
--   let tacs ← allTacticDocs
--   return tacs.map (fun x => TacticDoc.userName x)

-- set_option pp.deepTerms.threshold 500 in
-- #eval do
--   let tacs ← allTacticDocs
--   return tacs.map (fun x => TacticDoc.internalName x)

-- #eval do
--   let tacs ← allTacticDocs
--   return tacs.map (fun x => TacticDoc.docString x)

#eval do
  let tacs ← allTacticDocs
  return s!"There are {tacs.size} tactics"

-- TODO: This could be used to generate a list of all tactics automatically
-- but I'm not sure this is desired...

end

set_option maxHeartbeats 0
set_option maxRecDepth 100000000000000000

open Lean.Elab.Tactic


#doc (Manual) "Tactics" =>
%%%
tag := "tactics"
%%%

This list of tactics attempts to be fairly complete but
does leave out slight variations of certain tactics,
such as `fconstructor` vs. `constructor`.

If a tactic is missing from this file,
please PR to [this repository](https://github.com/leanprover-community/mathlib-manual).

The displayed docstring and name are automatically extracted from the Lean code.

If the information about a tactic is wrong, you should directly change the tactic's docstring by
creating a [PR to mathlib](https://github.com/leanprover-community/mathlib4).



# Interactive

These tactics help the user discover tactics or statements.

:::tactic Mathlib.Tactic.LibrarySearch.observe
:::

:::tactic "exact?"
:::

:::tactic "apply?"
:::

:::tactic "rw?"
:::

:::tactic Mathlib.Tactic.Hint.hintStx
:::



# Automation


:::tactic Aesop.Frontend.Parser.aesopTactic
:::

:::tactic "omega"
:::

:::tactic Lean.Parser.Tactic.decide show:="decide"
:::

:::tactic Lean.Parser.Tactic.simp
:::

:::tactic "infer_instance"
:::

:::tactic Mathlib.Tactic.Tauto.tauto
:::

:::tactic "trivial"
:::

:::tactic Mathlib.Tactic.cc
:::

:::example "polyrith"
TODO
:::

:::tactic linarith show:="linarith"
:::

:::tactic Mathlib.Tactic.Positivity.positivity
:::

# Algebra

These tactics deal with algebraic calculations.

:::tactic Mathlib.Tactic.Abel.abel
:::

:::tactic Mathlib.Tactic.Group.group
:::

:::tactic Mathlib.Tactic.RingNF.ring
:::

:::tactic Mathlib.Tactic.NoncommRing.noncomm_ring
:::

:::tactic Mathlib.Tactic.Module.tacticModule
:::

:::tactic Mathlib.Tactic.LinearCombination.linearCombination
:::

:::tactic Mathlib.Tactic.FieldSimp.fieldSimp
:::

:::tactic cancelDenoms
:::

:::tactic Mathlib.Tactic.tacticAlgebraize__
:::

:::tactic Tactic.ReduceModChar.reduce_mod_char
:::

:::tactic Mathlib.Tactic.ComputeDegree.computeDegree
:::

:::tactic Mathlib.Tactic.ComputeDegree.monicityMacro
:::



# Function Properties / Analysis / Measure Theory

These tactics proof certain properties about functions.

:::tactic Mathlib.Meta.FunProp.funPropTacStx
:::

:::tactic tacticContinuity
:::

:::tactic tacticMeasurability
:::

:::tactic Mathlib.Tactic.Borelize.tacticBorelize___
:::

:::example "bound"
TODO
:::

:::tactic ArithmeticFunction.arith_mult
:::



# Category Theory

These tactics are explicitely written for category theory.

TODO



# Miscellaneous

:::tactic finiteness show:="finiteness"
:::

:::tactic Mathlib.Tactic.Monotonicity.mono
:::

:::tactic Mathlib.Tactic.Nontriviality.nontriviality
:::

:::tactic Mathlib.Tactic.subsingletonStx
:::



# Induction / case distinction

:::tactic "induction"
:::

:::tactic "cases"
:::

:::tactic "rcases"
:::

:::tactic "by_cases"
:::

:::tactic Lean.Elab.Tactic.finCases
:::

:::tactic Mathlib.Tactic.intervalCases
:::

:::tactic "split"
:::

:::tactic Mathlib.Tactic.splitIfs
:::




# Logic

These tactics deal with statements in logic. Remember that
`tauto`, listed above, is also good a these.

:::tactic Mathlib.Tactic.Contrapose.contrapose
:::

:::tactic Mathlib.Tactic.PushNeg.tacticPush_neg_
:::

:::tactic Mathlib.Tactic.TFAE.tfaeHave
:::

:::tactic Mathlib.Tactic.TFAE.tfaeFinish
:::

:::tactic Mathlib.Tactic.useSyntax
:::

:::tactic Mathlib.Tactic.wlog
:::

:::tactic Mathlib.Tactic.Choose.choose
:::

:::tactic Mathlib.Tactic.Peel.peel
:::

:::tactic "left"
:::

:::tactic "right"
:::

:::tactic "contradiction"
:::

:::tactic "exfalso"
:::



# Rewriting / `calc`

These tactics are used for rewriting parts of a goal with something
that is equal (or equivalent/etc.)

:::tactic "calc"
:::

:::tactic "rw"
:::

:::tactic Mathlib.Tactic.nthRewriteSeq
:::

:::tactic Mathlib.Tactic.tacticSimp_rw___
:::

The following Tactic is avoided in Mathlib

:::tactic "erw"
:::



# Congr / ext

These tactics have not made it into any other category yet, please move them.

:::tactic Mathlib.Tactic.subsingletonStx
:::

:::tactic "congr"
:::

:::tactic Mathlib.Tactic.GCongr.tacticGcongr__With__
:::

:::tactic "ext"
:::

:::tactic "funext"
:::



# Coersions

These tactics deal with coersions/casts between different types.

:::tactic Mathlib.Tactic.normNum
:::

:::tactic Lean.Parser.Tactic.tacticNorm_cast__
:::

:::tactic Lean.Parser.Tactic.pushCast
:::

:::tactic Lean.Parser.Tactic.tacticAssumption_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticExact_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticApply_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticRw_mod_cast___
:::

:::tactic Mathlib.Tactic.lift
:::

:::tactic Mathlib.Tactic.Zify.zify
:::

:::tactic Mathlib.Tactic.Rify.rify
:::

:::tactic Mathlib.Tactic.Qify.qify
:::



# Definitional equality

These tactics modify the goal or assumptions in a way that remains
definitionally equal.

:::tactic Lean.Parser.Tactic.dsimp
:::

:::tactic "change"
:::

:::tactic "unfold"
:::



# Basic tactics / assumptions

:::tactic "rfl"
:::

:::tactic "symm"
:::

:::tactic Batteries.Tactic.tacticTrans___
:::

:::tactic Lean.Parser.Tactic.assumption
:::

:::tactic "exact"
:::

:::tactic Lean.Parser.Tactic.apply
:::

Note that `apply` and `apply at` are formally considered two distinct tactics
even though they appear to be one to the user.

:::tactic Mathlib.Tactic.tacticApply_At_ show:="apply at"
:::


:::tactic "specialize"
:::

:::tactic "generalize"
:::

:::tactic Lean.Parser.Tactic.tacticHave_
:::

:::tactic Lean.Parser.Tactic.tacticLet_
:::

-- TODO: The `set` docstring ought to be on the `syntax`, not the `elab_rules`
-- remove the replace below once that's fixed
:::tactic Mathlib.Tactic.setTactic replace:=true
:::

:::tactic "replace"
:::


:::tactic "suffices"
:::

:::tactic Lean.Parser.Tactic.obtain
:::


:::tactic "refine"
:::

:::tactic Mathlib.Tactic.convert
:::

:::tactic "constructor"
:::

:::tactic "injection"
:::

:::tactic "intro"
:::

:::tactic Lean.Parser.Tactic.revert
:::




# Conv mode

:::tactic Lean.Parser.Tactic.Conv.conv
:::

TODO: a lot of tactics have a `conv`-equivalent. Add them here.
Meanwhile, try other tactics and see which work in `conv` mode.



# Control flow

These tactics should not appear in a final proof but might be
useful along the way.

:::tactic "sorry"
:::

:::tactic "done"
:::

:::tactic "checkpoint"
:::

:::tactic "save"
:::

:::tactic "stop"
:::



# For Tests

These are particularly helpful for writing tests to the `MathlibTest` suite.


:::tactic Lean.Parser.Tactic.guardHyp
:::

:::tactic Lean.Parser.Tactic.guardTarget
:::

:::tactic Lean.Parser.Tactic.guardExpr
:::

:::tactic Lean.Parser.Tactic.failIfSuccess
:::

Finally, this is a command and not a tactic, but it is also essential for test files.

:::tactic Lean.guardMsgsCmd
:::
