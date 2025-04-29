/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual InlineLean

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

:::syntax term title:="Products of Arbitrary Sorts"
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

### Transformation

{docstring Prod.map}

{docstring Prod.swap}

### Natural Number Ranges

{docstring Prod.allI}

{docstring Prod.anyI}

{docstring Prod.foldI}

### Ordering

{docstring Prod.lexLt}


# Dependent Pairs
%%%
tag := "sigma-types"
%%%


{deftech}_Dependent pairs_, also known as {deftech}_dependent sums_ or {deftech}_Σ-types_,{see "Σ-types"}[Sigma types]{index}[Σ-types] are pairs in which the second term's type may depend on the _value_ of the first term.
They are closely related to the existential quantifier{TODO}[xref] and {name}`Subtype`.
Unlike existentially quantified statements, dependent pairs are in the {lean}`Type` universe and are computationally relevant data.
Unlike subtypes, the second term is also computationally relevant data.
Like ordinary pairs, dependent pairs may be nested; this nesting is right-associative.

:::syntax term (title := "Dependent Pair Types")

```grammar
($x:ident : $t) × $t
```

```grammar
Σ $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
Σ ($x:ident $[$x:ident]* : $t), $_
```

Dependent pair types bind one or more variables, which are then in scope in the final term.
If there is one variable, then its type is a that of the first element in the pair and the final term is the type of the second element in the pair.
If there is more than one variable, the types are nested right-associatively.
The identifiers may also be `_`.
With parentheses, multiple bound variables may have different types, while the unparenthesized variant requires that all have the same type.
:::

::::example "Nested Dependent Pair Types"

:::paragraph
The type
```leanTerm
Σ n k : Nat, Fin (n * k)
```
is equivalent to
```leanTerm
Σ n : Nat, Σ k : Nat, Fin (n * k)
```
and
```leanTerm
(n : Nat) × (k : Nat) × Fin (n * k)
```
:::

:::paragraph
The type
```leanTerm
Σ (n k : Nat) (i : Fin (n * k)) , Fin i.val
```
is equivalent to
```leanTerm
Σ (n : Nat), Σ (k : Nat), Σ (i : Fin (n * k)) , Fin i.val
```
and
```leanTerm
(n : Nat) × (k : Nat) × (i : Fin (n * k)) × Fin i.val
```
:::

The two styles of annotation cannot be mixed in a single {keywordOf «termΣ_,_»}`Σ`-type:
```syntaxError mixedNesting (category := term)
Σ n k (i : Fin (n * k)) , Fin i.val
```
```leanOutput mixedNesting
<example>:1:5-1:7: unexpected token '('; expected ','
```
::::

```lean (show := false)
section
variable {α : Type} (x : α)
```
::::paragraph
Dependent pairs are typically used in one of two ways:

 1. They can be used to “package” a concrete type index together with a value of the indexed family, used when the index value is not known ahead of time.
    The type {lean}`Σ n, Fin n` is a pair of a natural number and some other number that's strictly smaller.
    This is the most common way to use dependent pairs.

 2. :::paragraph
    The first element can be thought of as a “tag” that's used to select from among different types for the second term.
    This is similar to the way that selecting a constructor of a sum type determines the types of the constructor's arguments.
    For example, the type

    ```leanTerm
    Σ (b : Bool), if b then Unit else α
    ```

    is equivalent to {lean}`Option α`, where {lean type:="Option α"}`none` is {lean type:="Σ (b : Bool), if b then Unit else α"}`⟨true, ()⟩` and {lean type:="Option α"}`some x` is {lean type:="Σ (b : Bool), if b then Unit else α"}`⟨false, x⟩`.
    Using dependent pairs this way is uncommon, because it's typically much easier to define a special-purpose {tech}[inductive type] directly.
    :::
::::

```lean (show := false)
end
```

{docstring Sigma}

:::::example "Dependent Pairs with Data"

::::ioExample
The type {name}`Vector`, which associates a known length with an array, can be placed in a dependent pair with the length itself.
While this is logically equivalent to just using {name}`Array`, this construction is sometimes necessary to bridge gaps in an API.

```ioLean
def getNLinesRev : (n : Nat) → IO (Vector String n)
  | 0 => pure #v[]
  | n + 1 => do
    let xs ← getNLinesRev n
    return xs.push (← (← IO.getStdin).getLine)

def getNLines (n : Nat) : IO (Vector String n) := do
  return (← getNLinesRev n).reverse

partial def getValues : IO (Σ n, Vector String n) := do
  let stdin ← IO.getStdin

  IO.println "How many lines to read?"
  let howMany ← stdin.getLine

  if let some howMany := howMany.trim.toNat? then
    return ⟨howMany, (← getNLines howMany)⟩
  else
    IO.eprintln "Please enter a number."
    getValues

def main : IO Unit := do
  let values ← getValues
  IO.println s!"Got {values.fst} values. They are:"
  for x in values.snd do
    IO.println x.trim
```
:::paragraph
When calling the program with this standard input:
```stdin
4
Apples
Quince
Plums
Raspberries
```
the output is:
```stdout
How many lines to read?
Got 4 values. They are:
Raspberries
Plums
Quince
Apples
```
:::
::::

:::::

:::example "Dependent Pairs as Sums"
{name}`Sigma` can be used to implement sum types.
The {name}`Bool` in the first projection of {name}`Sum'` indicates which type the second projection is drawn from.
```lean
def Sum' (α : Type) (β : Type) : Type :=
  Σ (b : Bool),
    match b with
    | true => α
    | false => β
```

The injections pair a tag (a {name}`Bool`) with a value of the indicated type.
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


Just as {name}`Prod` has a variant {name}`PProd` that accepts propositions as well as types, {name}`PSigma` allows its projections to be propositions.
This has the same drawbacks as {name}`PProd`: it is much more likely to lead to failures of universe level unification.
However, {name}`PSigma` can be necessary when implementing custom proof automation or in some rare, advanced use cases.

:::syntax term (title := "Fully-Polymorphic Dependent Pair Types")

```grammar
Σ' $x:ident $[$_:ident]* $[: $t]? , $_
```

```grammar
Σ' ($x:ident $[$x:ident]* : $t), $_
```

The rules for nesting {keyword}`Σ'`, as well as those that govern its binding structure, are the same as those for {keywordOf «termΣ_,_»}`Σ`.
:::

{docstring PSigma}
