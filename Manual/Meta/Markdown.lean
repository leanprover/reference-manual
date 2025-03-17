/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual
import Manual.Meta.Figure
import Manual.Meta.Lean
import Lean.Elab.InfoTree.Types

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab

namespace Manual

@[code_block_expander markdown]
def markdown : CodeBlockExpander
  | _args, str => do
    let str ← parserInputString str
    let some ast := MD4Lean.parse str
      | throwError "Failed to parse docstring as Markdown"
    ast.blocks.mapM <|
      Markdown.blockFromMarkdown (handleHeaders := Markdown.strongEmphHeaders)
