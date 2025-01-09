/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

set_option maxHeartbeats 300000

#doc (Manual) "Comparisons" =>
%%%
tag := "fixed-int-comparisons"
%%%


The operators in this section are rarely invoked by name.
Typically, comparisons operations on fixed-width integers should use the decidability of the corresponding relations, which consist of the equality type {name}`Eq` and those implemented in instances of {name}`LE`, {name}`LT`.

```lean (show := false)
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  for t in types do
    elabCommand <| ← `(example : LE $(mkIdent t) := inferInstance)
    elabCommand <| ← `(example : LT $(mkIdent t) := inferInstance)
```

```lean (show := false)
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  for t in types do
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x < y) := inferInstance)
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x ≤ y) := inferInstance)
    elabCommand <| ← `(example (x y : $(mkIdent t):ident) : Decidable (x = y) := inferInstance)
```


{docstring USize.le}

{docstring ISize.le}

{docstring UInt8.le}

{docstring Int8.le}

{docstring UInt16.le}

{docstring Int16.le}

`{docstring UInt32.le}`

{docstring Int32.le}

{docstring UInt64.le}

{docstring Int64.le}

{docstring USize.lt}

{docstring ISize.lt}

{docstring UInt8.lt}

{docstring Int8.lt}

{docstring UInt16.lt}

{docstring Int16.lt}

`{docstring UInt32.lt}`

{docstring Int32.lt}

{docstring UInt64.lt}

{docstring Int64.lt}

{docstring USize.decEq}

{docstring ISize.decEq}

{docstring UInt8.decEq}

{docstring Int8.decEq}

{docstring UInt16.decEq}

{docstring Int16.decEq}

{docstring UInt32.decEq}

{docstring Int32.decEq}

{docstring UInt64.decEq}

{docstring Int64.decEq}

{docstring USize.decLe}

{docstring ISize.decLe}

{docstring UInt8.decLe}

{docstring Int8.decLe}

{docstring UInt16.decLe}

{docstring Int16.decLe}

{docstring UInt32.decLe}

{docstring Int32.decLe}

{docstring UInt64.decLe}

{docstring Int64.decLe}

{docstring USize.decLt}

{docstring ISize.decLt}

{docstring UInt8.decLt}

{docstring Int8.decLt}

{docstring UInt16.decLt}

{docstring Int16.decLt}

{docstring UInt32.decLt}

{docstring Int32.decLt}

{docstring UInt64.decLt}

{docstring Int64.decLt}
