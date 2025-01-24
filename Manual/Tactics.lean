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
set_option maxRecDepth 100000000000000000

open Lean.Elab.Tactic

#doc (Manual) "Tactics" =>
%%%
tag := "tactics"
%%%

This lists of tactics if far from complete

*Contribute*: Most information about tactics is directly from the docstring of the tactic In
mathlib. In order to improve this text, PR to the docstring of the tactic.

If a tactic is missing from this file, PR to this repo.




# Interactive

These tactics help the user discover tactics or statements.

:::tactic Mathlib.Tactic.LibrarySearch.observe
:::

:::tactic Mathlib.Tactic.Hint.hintStx
:::



# High level automation

This section contains a few general-purpose tactics
that try to automatically solve a goal.

:::tactic Aesop.Frontend.Parser.aesopTactic
:::

:::tactic Mathlib.Tactic.cc
:::

:::tactic Mathlib.Tactic.Tauto.tauto
:::

:::example "polyrith"
TODO
:::

:::tactic Mathlib.Tactic.Positivity.positivity
:::

:::example "linarith"
TODO
:::






# Algebra

These tactics deal with algebraic calculations.

:::tactic Mathlib.Tactic.Abel.abel
:::

:::tactic Mathlib.Tactic.tacticAlgebraize__
:::

:::tactic Mathlib.Tactic.FieldSimp.fieldSimp
:::

:::tactic Mathlib.Tactic.Group.group
:::

:::tactic Mathlib.Tactic.Module.tacticModule
:::

:::tactic Mathlib.Tactic.NoncommRing.noncomm_ring
:::

:::tactic Mathlib.Tactic.RingNF.ring
:::

:::tactic Mathlib.Tactic.LinearCombination.linearCombination
:::

:::tactic cancelDenoms
:::

:::tactic Tactic.ReduceModChar.reduce_mod_char
:::





# Function Properties / Analysis

These tactics proof certain properties about functions.

:::tactic Mathlib.Meta.FunProp.funPropTacStx
:::

:::tactic tacticContinuity
:::

:::tactic tacticMeasurability
:::

:::example "bound"
TODO
:::


# Category Theory

These tactics are explicitely written for category theory.

todo



# Coersions / type casting / definitional Equivalence

These tactics are used for modifying the goal in a way that seems mathematically
trivial: handling coersions/casts, changing the goal to something definitionally
equivalent, etc.

:::tactic Mathlib.Tactic.convert
:::

:::tactic Mathlib.Tactic.lift
:::

:::tactic Mathlib.Tactic.normNum
:::

:::tactic Mathlib.Tactic.Rify.rify
:::

:::tactic Mathlib.Tactic.Qify.qify
:::

:::tactic Mathlib.Tactic.Zify.zify
:::



# Logic

These tactics deal with statements in logic.

:::tactic Mathlib.Tactic.Contrapose.contrapose
:::

:::tactic Mathlib.Tactic.PushNeg.tacticPush_neg_
:::

:::tactic Mathlib.Tactic.splitIfs
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


# Rewriting

These tactics are used for rewriting parts of a goal with something
that is equal (or equivalent/etc.)

:::tactic Mathlib.Tactic.nthRewriteSeq
:::

:::tactic Mathlib.Tactic.tacticSimp_rw___
:::




# Unsorted

These tactics have not made it into any other category yet, please move them.

:::tactic Mathlib.Tactic.tacticApply_At_
:::

:::tactic Mathlib.Tactic.applyFun
:::

:::tactic ArithmeticFunction.arith_mult
:::

:::tactic Mathlib.Tactic.ComputeDegree.computeDegree
:::

:::tactic Mathlib.Tactic.ComputeDegree.monicityMacro
:::

:::tactic Lean.Elab.Tactic.finCases
:::

:::example "finiteness"
TODO
:::

:::tactic Mathlib.Tactic.GCongr.tacticGcongr__With__
:::

:::tactic Mathlib.Tactic.intervalCases
:::

:::tactic Mathlib.Tactic.Monotonicity.mono
:::

:::tactic Mathlib.Tactic.Nontriviality.nontriviality
:::

:::example " Mathlib.Tactic.setTactic"
TODO
:::

:::tactic Mathlib.Tactic.subsingletonStx
:::


# Conv mode

:::tactic Lean.Parser.Tactic.Conv.conv
:::

TODO: This section should contain anything used in conv mode
