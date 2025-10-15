/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/

import Verso

open Verso Doc Elab

namespace Manual

/--
Defines a code block expander for specifying imports for lean code examples.
It elaborates to nothing normally, but it is useful for constructing examples
as self-contained code for copy-paste or linking to the live sandbox website.
-/
@[code_block_expander imports]
def imports : CodeBlockExpander
  | _args, _str => do
    return #[]
