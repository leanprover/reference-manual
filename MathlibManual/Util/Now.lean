/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/
import VersoManual
import Std
import Lean

open Lean Verso.Doc.Elab

namespace MathlibManual

/-- Display the time the manual was built in the verso text. -/
@[role_expander now]
def now : RoleExpander
  | #[], #[] => do
    let now := (← Std.Time.ZonedDateTime.now) |>.format "uuuu-MM-dd HH:mm (ZZ)"
    pure #[← ``(Verso.Doc.Inline.text $(quote now))]
  | _, _ => throwError "Unexpected arguments"
