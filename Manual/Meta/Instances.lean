/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
import Lean
public import SubVerso.Highlighting.Highlighted

open SubVerso.Highlighting
open Lean

namespace Manual

public section

deriving instance ToExpr for Token.Kind
deriving instance ToExpr for Token
deriving instance ToExpr for Highlighted.Hypothesis
deriving instance ToExpr for Highlighted.Goal
deriving instance ToExpr for Highlighted.MessageContents
deriving instance ToExpr for Highlighted.Span.Kind
deriving instance ToExpr for Highlighted
