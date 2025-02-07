/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Tuples" =>
%%%
tag := "tuples"
%%%



:::paragraph
The Lean standard library includes a variety of tuple-like types.
In practice, they differ in four ways:
 * whether the first projection is a type or a proposition
 * whether the second projection is a type or a proposition
 * whether the second projection's type depends on the first projection's value
 * whether the type as a whole is a proposition or type
:::

:::table (header := true)
* + Type
  + First Projection
  + Second Projection
  + Dependent?
  + Universe
* + {name}`Prod`
  + {lean universes:="u"}`Type u`
  + {lean universes:="v"}`Type v`
  + ❌️
  + {lean universes:="u v"}`Type (max u v)`
* + {name}`And`
  + {lean universes:="u v"}`Prop`
  + {lean universes:="u v"}`Prop`
  + ❌️
  + {lean universes:="u v"}`Prop`
* + {name}`Sigma`
  + {lean universes:="u"}`Type u`
  + {lean universes:="v"}`Type v`
  + ✔
  + {lean universes:="u v"}`Type (max u v)`
* + {name}`Subtype`
  + {lean universes:="u"}`Type u`
  + {lean universes:="v"}`Prop`
  + ✔
  + {lean universes:="u v"}`Type u`
* + {name}`Exists`
  + {lean universes:="u"}`Type u`
  + {lean universes:="v"}`Prop`
  + ✔
  + {lean universes:="u v"}`Prop`
:::

:::paragraph
Some potential rows in this table do not exist in the library:

 * There is no dependent pair where the first projection is a proposition, because {tech}[proof irrelevance] renders this meaningless.

 * There is no non-dependent pair that combines a type with a proposition because the situation is rare in practice: grouping data with _unrelated_ proofs is uncommon.
:::

These differences lead to very different use cases.
{name}`Prod` and its variants {name}`PProd` and {name}`MProd` simply group data together—they are products.
Because its second projection is dependent, {name}`Sigma` has the character of a sum: for each element of the first projection's type, there may be a different type in the second projection.
{name}`Subtype` selects the values of a type that satisfy a predicate.
Even though it syntactically resembles a pair, in practice it is treated as an actual subset.
{name}`And` is a logical connective, and {name}`Exists` is a quantifier.
This chapter documents the tuple-like pairs, namely {name}`Prod` and {name}`Sigma`.

# Ordered Pairs
%%%
tag := "pairs"
%%%

```lean (show:=false)
section
variable {α : Type u} {β : Type v} {γ : Type w} {x : α} {y : β} {z : γ}
```

The type {lean}`α × β`, which is a {tech}[notation] for {lean}`Prod α β`, contains ordered pairs in which the first item is an {lean}`α` and the second is a {lean}`β`.
These pairs are written in parentheses, separated by commas.
Larger tuples are represented as nested tuples, so {lean}`α × β × γ` is equivalent to {lean}`α × (β × γ)` and {lean}`(x, y, z)` is equivalent to {lean}`(x, (y, z))`.

:::syntax term title:="Product Types"
```grammar
$_ × $_
```
The product {lean}`Prod α β` is written {lean}`α × β`.
:::

:::syntax term title:="Pairs"
```grammar
($_, $_)
```
:::

{docstring Prod}

```lean (show:=false)
section
variable {α : Sort u} {β : Sort v} {γ : Type w}
```

There are also the variants {lean}`α ×' β` (which is notation for {lean}`PProd α β`) and {lean}`MProd`, which differ with respect to {tech}[universe] levels: like {name}`PSum`, {name}`PProd` allows either {lean}`α` or {lean}`β` to be a proposition, while {lean}`MProd` requires that both be types at the _same_ universe level.
Generally speaking, {name}`PProd` is primarily used in the implementation of proof automation and the elaborator, as it tends to give rise to universe level unification problems that can't be solved.
{lean}`MProd`, on the other hand, can simplify universe level issues in certain advanced use cases.

```lean (show:=false)
end
```

:::syntax term title:="Product Types"
```grammar
$_ ×' $_
```
The product {lean}`PProd α β`, in which both types could be propositions, is written {lean}`α × β`.
:::


{docstring PProd}

{docstring MProd}

## API Reference
%%%
tag := "prod-api"
%%%

As a mere pair, the primary API for {lean}`Prod` is provided by pattern matching and by the first and second projections {name}`Prod.fst` and {name}`Prod.snd`.

### Ordering

{docstring Prod.lexLt}

### Transformation

{docstring Prod.map}

{docstring Prod.swap}


### Natural Number Ranges

{docstring Prod.allI}

{docstring Prod.anyI}

{docstring Prod.foldI}



# Dependent Pairs
%%%
tag := "sigma-types"
%%%

:::planned 176
Describe {name}`Sigma` and {name}`PSigma`, their syntax and API.
:::

:::TODO
 * Sigma and PSigma syntax
 * Example of a "product-like" use of {name}`Sigma`
:::

{docstring Sigma}

{docstring PSigma}


:::example "Dependent Pairs as Sums"
{name}`Sigma` can be used to implement sums of {lean}`Type`s.
```lean
def Sum' (α : Type) (β : Type) : Type :=
  Σ (b : Bool), match b with | true => α | false => β
```

The injections pair a tag with a value of the indicated type.
Annotating them with {attr}`match_pattern` allows them to be used in patterns as well as in ordinary terms.
```lean
variable {α β : Type}

@[match_pattern]
def Sum'.inl (x : α) : Sum' α β := ⟨true, x⟩

@[match_pattern]
def Sum'.inr (x : β) : Sum' α β := ⟨false, x⟩

def Sum'.swap : Sum' α β → Sum' β α
  | .inl x => .inr x
  | .inr y => .inl y
```
:::
