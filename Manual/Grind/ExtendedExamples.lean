/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

import Manual.Grind.ExtendedExamples.Integration
import Manual.Grind.ExtendedExamples.IfElseNorm
import Manual.Grind.ExtendedExamples.IndexMap

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Grind

#doc (Manual) "Bigger Examples" =>
%%%
tag := "grind-bigger-examples"
%%%

{include 1 Manual.Grind.ExtendedExamples.Integration}

{include 1 Manual.Grind.ExtendedExamples.IfElseNorm}

{include 1 Manual.Grind.ExtendedExamples.IndexMap}
