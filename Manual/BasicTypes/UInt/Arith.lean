/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

#doc (Manual) "Arithmetic" =>
%%%
tag := "fixed-int-arithmetic"
%%%

Typically, arithmetic operations on fixed-width integers should be accessed using Lean's overloaded arithmetic notation, particularly their instances of {name}`Add`, {name}`Sub`, {name}`Mul`, {name}`Div`, and {name}`Mod`, as well as {name}`Neg` for signed types.

```lean (show := false)
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let signed := [`ISize, `Int8, `Int16, `Int32, `Int64]
  let unsigned := [`USize, `UInt8, `UInt16, `UInt32, `UInt64]
  let types := signed ++ unsigned
  let classes : List Name := [`Add, `Sub, `Mul, `Div, `Mod]
  for t in types do
    for c in classes do
      elabCommand <| ← `(example : $(mkIdent c):ident $(mkIdent t) := inferInstance)
  for t in signed do
    elabCommand <| ← `(example : Neg $(mkIdent t) := inferInstance)
```

{docstring ISize.neg}

{docstring Int8.neg}

{docstring Int16.neg}

{docstring Int32.neg}

{docstring Int64.neg}

{docstring USize.add}

{docstring ISize.add}

{docstring UInt8.add}

{docstring Int8.add}

{docstring UInt16.add}

{docstring Int16.add}

{docstring UInt32.add}

{docstring Int32.add}

{docstring UInt64.add}

{docstring Int64.add}

{docstring USize.sub}

{docstring ISize.sub}

{docstring UInt8.sub}

{docstring Int8.sub}

{docstring UInt16.sub}

{docstring Int16.sub}

{docstring UInt32.sub}

{docstring Int32.sub}

{docstring UInt64.sub}

{docstring Int64.sub}

{docstring USize.mul}

{docstring ISize.mul}

{docstring UInt8.mul}

{docstring Int8.mul}

{docstring UInt16.mul}

{docstring Int16.mul}

{docstring UInt32.mul}

{docstring Int32.mul}

{docstring UInt64.mul}

{docstring Int64.mul}

{docstring USize.div}

{docstring ISize.div}

{docstring UInt8.div}

{docstring Int8.div}

{docstring UInt16.div}

{docstring Int16.div}

{docstring UInt32.div}

{docstring Int32.div}

{docstring UInt64.div}

{docstring Int64.div}

{docstring USize.mod}

{docstring ISize.mod}

{docstring UInt8.mod}

{docstring Int8.mod}

{docstring UInt16.mod}

{docstring Int16.mod}

{docstring UInt32.mod}

{docstring Int32.mod}

{docstring UInt64.mod}

{docstring Int64.mod}

{docstring USize.log2}

{docstring UInt8.log2}

{docstring UInt16.log2}

{docstring UInt32.log2}

{docstring UInt64.log2}
