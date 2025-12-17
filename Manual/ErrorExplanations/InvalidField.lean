/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "About: `invalidField`" =>
%%%
shortTitle := "invalidField"
%%%

{errorExplanationHeader lean.invalidField}

This error indicates that an expression containing a dot followed by an identifier was encountered,
and that it wasn't possible to understand the identifier as a field.

Lean's field notation is very powerful, but this can also make it confusing: the expression
`color.value` can either be a single {ref "identifiers-and-resolution"}[identifier].
it can be a reference to the {ref "structure-fields"}[field of a structure], and it
and be a calling a function on the value `color` with
{ref "generalized-field-notation"}[generalized field notation].

# Examples

:::errorExample "Incorrect Field Name"

```broken
#eval (4 + 2).suc
```
```output
Invalid field `suc`: The environment does not contain `Nat.suc`, so it is not possible to project the field `suc` from an expression
  4 + 2
of type `Nat`
```
```fixed
#eval (4 + 1).succ
```

The simplest reason for an invalid field error is that the function being sought, like `Nat.suc`,
does not exist.
:::

:::errorExample "Projecting from the Wrong Expression"
```broken
#eval '>'.leftpad 10 ['a', 'b', 'c']
```
```output
Invalid field `leftpad`: The environment does not contain `Char.leftpad`, so it is not possible to project the field `leftpad` from an expression
  '>'
of type `Char`
```
```fixed
#eval ['a', 'b', 'c'].leftpad 10 '>'
```

The type of the expression before the dot entirely determines the function being called by the field
projection. There is no `Char.leftpad`, and the only way to invoke `List.leftpad` with generalized
field notation is to have the list come before the dot.
:::

:::errorExample "Type is Not Specific"
```broken
def double_plus_one {α} [Add α] (x : α) :=
   (x + x).succ
```
```output
Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  x + x
has type `α` which does not have the necessary form.
```
```fixed
def double_plus_one (x : Nat) :=
   (x + x).succ
```

The `Add` typeclass is sufficient for performing the addition `x + x`, but the `.succ` field notation
cannot operate without knowing more about the actual type from which `succ` is being projected.
:::

:::errorExample "Insufficient Type Information"

```broken
example := fun (n) => n.succ.succ
```
```output
Invalid field notation: Type of
  n
is not known; cannot resolve field `succ`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Fin.succ`
  • `Nat.succ`
  • `Lean.Level.succ`
  • `Std.PRange.succ`
  • `Lean.Level.PP.Result.succ`
  • `Std.Time.Internal.Bounded.LE.succ`
```
```fixed
example := fun (n : Nat) => n.succ.succ
```

Generalized field notation can only be used when it is possible to determine the type that is being
projected. Type annotations may need to be added to make generalized field notation work.
:::
