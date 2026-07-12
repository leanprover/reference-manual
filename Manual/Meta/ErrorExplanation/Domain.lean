/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual

open Lean
open Verso.Genre.Manual

namespace Manual

def errorExplanationDomain := `Manual.errorExplanation

open Verso.Search in
def errorExplanationDomainMapper :=
  DomainMapper.withDefaultJs errorExplanationDomain "Error Explanation" "error-explanation-domain"
    |>.setFont { family := .code }
