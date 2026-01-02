/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "About: `inferBinderTypeFailed`" =>
%%%
shortTitle := "inferBinderTypeFailed"
%%%

{errorExplanationHeader lean.inferBinderTypeFailed}

This error occurs when the type of a binder in a declaration header or local binding is not fully
specified and cannot be inferred by Lean. Generally, this can be resolved by providing more
information to help Lean determine the type of the binder, either by explicitly annotating its type
or by providing additional type information at sites where it is used. When the binder in question
occurs in the header of a declaration, this error is often accompanied by
{ref "lean.inferDefTypeFailed" (domain := Manual.errorExplanation)}[`lean.inferDefTypeFailed`].

Note that if a declaration is annotated with an explicit resulting type—even one that contains
holes—Lean will not use information from the definition body to infer parameter types. It may
therefore be necessary to explicitly specify the types of parameters whose types would otherwise be
inferable without the resulting-type annotation; see the "uninferred binder due to resulting type
annotation" example below for a demonstration. In {keyword}`theorem` declarations, the body is never
used to infer the types of binders, so any binders whose types cannot be inferred from the rest of
the theorem type must include a type annotation.

This error may also arise when identifiers that were intended to be declaration names are
inadvertently written in binder position instead. In these cases, the erroneous identifiers are
treated as binders with unspecified type, leading to a type inference failure. This frequently
occurs when attempting to simultaneously define multiple constants of the same type using syntax
that does not support this. Such situations include:
* Attempting to name an example by writing an identifier after the {keyword}`example` keyword;
* Attempting to define multiple constants with the same type and (if applicable) value by listing
  them sequentially after {keyword}`def`, {keyword}`opaque`, or another declaration keyword;
* Attempting to define multiple fields of a structure of the same type by sequentially listing their
  names on the same line of a structure declaration; and
* Omitting vertical bars between inductive constructor names.

The first three cases are demonstrated in examples below.

# Examples

:::errorExample "Binder Type Requires New Type Variable"
```broken
def identity x :=
  x
```
```output
Failed to infer type of binder `x`
```
```fixed
def identity (x : α) :=
  x
```
In the code above, the type of `x` is unconstrained; as this example demonstrates, Lean does not
automatically generate fresh type variables for such binders. Instead, the type `α` of `x` must be
specified explicitly. Note that if automatic implicit parameter insertion is enabled (as it is by
default), a binder for `α` itself need not be provided; Lean will insert an implicit binder for this
parameter automatically.
:::

:::errorExample "Uninferred Binder Type Due to Resulting Type Annotation"
```broken
def plusTwo x : Nat :=
  x + 2
```
```output
Failed to infer type of binder `x`

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
```
```fixed
def plusTwo (x : Nat) : Nat :=
  x + 2
```
Even though `x` is inferred to have type `Nat` in the body of `plusTwo`, this information is not
available when elaborating the type of the definition because its resulting type (`Nat`) has been
explicitly specified. Considering only the information in the header, the type of `x` cannot be
determined, resulting in the shown error. It is therefore necessary to include the type of `x` in
its binder.
:::

:::errorExample "Attempting to Name an Example Declaration"
```broken
example trivial_proof : True :=
  trivial
```
```output
Failed to infer type of binder `trivial_proof`

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
```
```fixed
example : True :=
  trivial
```
This code is invalid because it attempts to give a name to an {keywordOf Lean.Parser.Command.example}`example` declaration. Examples cannot
be named, and an identifier written where a name would appear in other declaration forms is instead
elaborated as a binder, whose type cannot be inferred. If a declaration must be named, it should be
defined using a declaration form that supports naming, such as {keywordOf Lean.Parser.Command.declaration}`def` or {keywordOf Lean.Parser.Command.declaration}`theorem`.
:::

:::errorExample "Attempting to Define Multiple Opaque Constants at Once"
```broken
opaque m n : Nat
```
```output
Failed to infer type of binder `n`

Note: Multiple constants cannot be declared in a single declaration. The identifier(s) `n` are being interpreted as parameters `(n : _)`.
```
```fixed
opaque m : Nat
opaque n : Nat
```
This example incorrectly attempts to define multiple constants with a single {keywordOf Lean.Parser.Command.declaration}`opaque` declaration.
Such a declaration can define only one constant: it is not possible to list multiple identifiers
after {keywordOf Lean.Parser.Command.declaration}`opaque` or {keywordOf Lean.Parser.Command.declaration}`def` to define them all to have the same type (or value). Such a declaration is
instead elaborated as defining a single constant (e.g., `m` above) with parameters given by the
subsequent identifiers (`n`), whose types are unspecified and cannot be inferred. To define multiple
global constants, it is necessary to declare each separately.
:::

:::errorExample "Attempting to Define Multiple Structure Fields on the Same Line"
```broken
structure Person where
  givenName familyName : String
  age : Nat
```
```output
Failed to infer type of binder `familyName`
```
```fixed "Fixed (separate lines)"
structure Person where
  givenName : String
  familyName : String
  age : Nat
```
```fixed "Fixed (parenthesized)"
structure Person where
  (givenName familyName : String)
  age : Nat
```
This example incorrectly attempts to define multiple structure fields (`givenName` and `familyName`)
of the same type by listing them consecutively on the same line. Lean instead interprets this as
defining a single field, `givenName`, parametrized by a binder `familyName` with no specified type.
The intended behavior can be achieved by either listing each field on a separate line, or enclosing
the line specifying multiple field names in parentheses (see the manual section on
{ref "inductive-types"}[Inductive Types] for further details about structure
declarations).
:::
