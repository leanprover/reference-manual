/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Meta
import Manual.Papers

open Verso.Genre Manual

set_option pp.rawOnError true

open Lean (Syntax SourceInfo)



#doc (Manual) "Coercions" =>
%%%
tag := "coercions"
%%%

When the Lean elaborator is expecting one type but produces a term with a different type, it attempts to automatically insert a {deftech}_coercion_, which is a specially designated function from the term's type to the expected type.
{TODO}[A sentence about why they're great]
Coercions are used pervasively in the Lean standard library:
 * A {name}`Nat` to be used where an {name}`Int` is expected.
 * `TSyntax` TODO
 * TODO more good examples

Coercions are found using type class {tech}[instance synthesis].
The set of coercions can be extended by adding further instances of the appropriate type classes.

Coercions are not used to resolve {tech}[generalized field notation]. {TODO}[expand]


# Coercion Insertion
%%%
tag := "coercion-insertion"
%%%

:::paragraph
The process of searching for a coercion from one type to another is called {deftech}_coercion insertion_.
Coercion insertion occurs in the following situations where an error would otherwise occur:

 * When the expected type for a term is not equal to the type found for the term
 * When a {tech}[sort] is expected, but the term's type is not a sort
 * When a term is applied as though it were a function, but its type is not a function type

Coercion are also inserted when they are explicitly requested.
Each situation in which coercions may be inserted has a corresponding prefix operator that triggers the appropriate insertion.
:::



## Coercing Between Types

Coercions between types may be either dependent or non-dependent.
Dependent coercions are needed when the specific term being coerced is needed in order to resolve the coercion: for example, only decidable propositions can be coerced to {name}`Bool`, so the proposition in question must occur as part of the instance's type so that it can require the {name}`Decidable` instance.
Non-dependent coercions are used in all other cases.

```lean (show := false)
section
variable {α : Sort u} {β β'' βₙ: Sort v} {γ : Sort v'} {α' : Sort u'} {α'' : Sort u''}

macro "…":term => Lean.mkIdentFromRef `β''

variable [CoeHead α α'] [CoeOut α' β] [Coe β β'] [Coe … βₙ] [CoeTail β' γ]


```

:::paragraph
Non-dependent coercions may be chained: if there is a coercion from {lean}`α` to {lean}`β` and from {lean}`β` to {lean}`γ`, then there is also a coercion from {lean}`α` to {lean}`γ`.
{index subterm:="of coercions"}[chain]
The chain may consist of:

 * Zero or one instances of {inst}`CoeHead α α'`, followed by
 * Zero or more instances of {inst}`CoeOut α' β`, followed by
 * Zero or more instances of {inst}`Coe β β'` … {inst}`Coe … βₙ`, followed by
 * Zero or one {inst}`CoeTail β' γ`

Most coercions can be implemented as instances of {name}`Coe`.
{name}`CoeHead`, {name}`CoeOut`, and {name}`CoeTail` are needed in certain special situations.

{name}`CoeHead` and {name}`CoeOut` instances are chained from left to right (that is, from the type found for the term towards the type expected for it).
{name}`Coe` and {name}`CoeTail` instances are chained from right to left (that is, from the expected type towards the type found for the term).
This is reflected in their type signatures: {name}`CoeHead` and {name}`CoeOut` use {tech}[semi-output parameters] for the coercions' outputs, while {name}`Coe` and {name}`CoeTail` use {tech}[semi-out parameters] for the coercions' inputs.
Practically, {name}`CoeOut` should be used when the variables that occur in the coercion's output are a subset of those in its input, while {name}`Coe` should be used when the variables in the input are a subset of those in the output.
:::

```lean (show := false)
end
```

{docstring CoeHead}

{docstring CoeOut}

{docstring Coe}

{docstring CoeTail}



:::syntax term (title := "Coercions")

TODO describe

```grammar
↑$_:term
```

:::

## Coercing to Sorts

:::TODO

Is this only when some sort is needed, or also when a specific known one is expected?

It's also CoeOut

:::


:::syntax term (title := "Explicit Coercion to Sorts")
```grammar
↥ $_:term
```
:::


## Coercing to Function Types

:::syntax term (title := "Explicit Coercion to Functions")
```grammar
⇑ $_:term
```
:::



:::syntax attr (title := "Marking Coercions")

:::


:::TODO

Situations in which a coercion might be inserted

:::

:::planned 146
 * {deftech}[Coercions]
 * When they are inserted
 * Varieties of coercions
 * When should each be used?
:::
