/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Sum Types" =>
%%%
tag := "sum-types"
%%%


{deftech}_Sum types_ represent a choice between two types: an element of the sum is an element of one of the other types, paired with an indication of which type it came from.
Sums are also known as disjoint unions, discriminated unions, or tagged unions.
The constructors of a sum are also called {deftech}_injections_; mathematically, they can be considered as injective functions from each summand to the sum.

:::paragraph
There are two varieties of the sum type:

 * {lean}`Sum` is {tech key:="universe polymorphism"}[polymorphic] over all {lean}`Type` {tech}[universes], and is never a {tech}[proposition].

 * {lean}`PSum` is allows the summands to be propositions or types. Unlike {name}`Or`, the {name}`PSum` of two propositions is still a type, and non-propositional code can check which injection was used to construct a given value.

Manually-written Lean code almost always uses only {lean}`Sum`, while {lean}`PSum` is used as part of the implementation of proof automation. This is because it imposes problematic constraints that universe level unification cannot solve.
:::

{docstring Sum}

{docstring PSum}



# Syntax
%%%
tag := "sum-syntax"
%%%

The names {name}`Sum` and {name}`PSum` are rarely written explicitly.
Most code uses the corresponding infix operators.

```lean (show := false)
section
variable {α : Type u} {β : Type v}
```

:::syntax term title:="Sum Types"
```grammar
$_ ⊕ $_
```

{lean}`α ⊕ β` is notation for {lean}`Sum α β`.

:::

```lean (show := false)
end
```

```lean (show := false)
section
variable {α : Sort u} {β : Sort v}
```

:::syntax term title:="Potentially-Propositional Sum Types"
```grammar
$_ ⊕' $_
```

{lean}`α ⊕' β` is notation for {lean}`PSum α β`.

:::

```lean (show := false)
end
```

# API Reference
%%%
tag := "sum-api"
%%%

Sum types are primarily used with {tech}[pattern matching] rather than explicit function calls from an API.
As such, their primary API is the constructors {name Sum.inl}`inl` and {name Sum.inr}`inr`.

## Case Distinction

{docstring Sum.isLeft}

{docstring Sum.isRight}

## Extracting Values

{docstring Sum.elim}

{docstring Sum.getLeft}

{docstring Sum.getLeft?}

{docstring Sum.getRight}

{docstring Sum.getRight?}

## Transformations

{docstring Sum.map}

{docstring Sum.swap}

## Inhabited

The {name}`Inhabited` definitions for {name}`Sum` and {name}`PSum` are not registered as instances.
This is because there are two separate ways to construct a default value (via {name Sum.inl}`inl` or {name Sum.inr}`inr`), and instance synthesis might result in either choice.
The result could be situations where two identically-written terms elaborate differently and are not {tech key:="definitional equality"}[definitionally equal].

Both types have {name}`Nonempty` instances, for which {tech}[proof irrelevance] makes the choice of {name Sum.inl}`inl` or {name Sum.inr}`inr` not matter.
This is enough to enable {keyword}`partial` functions.
For situations that require an {name}`Inhabited` instance, such as programs that use {keyword}`panic!`, the instance can be explicitly used by adding it to the local context with {keywordOf Lean.Parser.Term.have}`have` or {keywordOf Lean.Parser.Term.let}`let`.

:::example "Inhabited Sum Types"

In Lean's logic, {keywordOf Lean.Parser.Term.panic}`panic!` is equivalent to the default value specified in its type's {name}`Inhabited` instance.
This means that the type must have such an instance—a {name}`Nonempty` instance combined with the axiom of choice would render the program non-computable.

Products have the right instance:
```lean
example : Nat × String := panic! "Cant' find it"
```

Sums do not, by default:
```lean (error := true) (name := panic)
example : Nat ⊕ String := panic! "Cant' find it"
```
```leanOutput panic
failed to synthesize
  Inhabited (Nat ⊕ String)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

The desired instance can be made available to instance synthesis using {keywordOf Lean.Parser.Term.have}`have`:
```lean
example : Nat ⊕ String :=
  have : Inhabited (Nat ⊕ String) := Sum.inhabitedLeft
  panic! "Cant' find it"
```
:::

{docstring Sum.inhabitedLeft}

{docstring Sum.inhabitedRight}

{docstring PSum.inhabitedLeft}

{docstring PSum.inhabitedRight}
