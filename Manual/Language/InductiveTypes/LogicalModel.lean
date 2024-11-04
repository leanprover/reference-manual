/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta

open Verso.Genre Manual

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800

#doc (Manual) "Logical Model" =>
%%%
tag := "inductive-types-logical-model"
%%%


# Recursors
%%%
tag := "recursors"
%%%

Every inductive type is equipped with a {tech}[recursor].
The recursor is completely determined by the signatures of the type constructor and the constructors.
Recursors have function types, but they are primitive and are not definable using `fun`.

## Recursor Types
%%%
tag := "recursor-types"
%%%


The recursor takes the following parameters:
: The inductive type's {tech}[parameters]

  Because parameters are consistent, they can be abstracted over the entire recursor

: The {deftech}_motive_

  The motive determines the type of an application of the recursor. The motive is a function whose arguments are the type's indices and an instance of the type with these indices instantiated. The specific universe for the type that the motive determines depends on the inductive type's universe and the specific constructors—see the section on {ref "subsingleton-elimination"}[{tech}[subsingleton] elimination] for details.

: A case for each constructor

  For each constructor, the recursor expects a function that satisfies the motive for an arbitrary application of the constructor. Each case abstracts over all of the constructor's parameters. If the constructor's parameter's type is the inductive type itself, then the case additionally takes a parameter whose type is the motive applied to that parameter's value—this will receive the result of recursively processing the recursive parameter.

: The target

  Finally, the recursor takes an instance of the type as an argument, along with any index values.

The result type of the recursor is the motive applied to these indices and the target.

:::example "The recursor for {lean}`Bool`"
{lean}`Bool`'s recursor {name}`Bool.rec` has the following parameters:

 * The motive computes a type in any universe, given a {lean}`Bool`.
 * There are cases for both constructors, in which the motive is satisfied for both {lean}`false` and {lean}`true`.
 * The target is some {lean}`Bool`.

The return type is the motive applied to the target.

```signature
Bool.rec.{u} {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) : motive t
```
:::

::::example "The recursor for {lean}`List`"
{lean}`List`'s recursor {name}`List.rec` has the following parameters:

:::keepEnv
```lean (show := false)
axiom α.{u} : Type u
```

 * The parameter {lean}`α` comes first, because the parameter and the cases need to refer to it
 * The motive computes a type in any universe, given a {lean}`List α`. There is no connection between the universe levels `u` and `v`.
 * There are cases for both constructors:
    - The motive is satisfied for {name}`List.nil`
    - The motive should be satisfiable for any application of {name}`List.cons`, given that it is satisfiable for the tail. The extra parameter `motive tail` is because `tail`'s type is a recursive occurrence of {name}`List`.
 * The target is some {lean}`List α`.
:::

Once again, the return type is the motive applied to the target.

```signature
List.rec.{u, v} {α : Type v} {motive : List α → Sort u}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail →
    motive (head :: tail))
  (t : List α) : motive t
```
::::

:::::keepEnv
::::example "Recursor with parameters and indices"
Given the definition of {name}`EvenOddList`:
```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```


The recursor {name}`EvenOddList.rec` is very similar to that for `List`.
The difference comes from the presence of the index:
 * The motive now abstracts over any arbitrary choice of index.
 * The case for {name EvenOddList.nil}`nil` applies the motive to {name EvenOddList.nil}`nil`'s index value `true`.
 * The case for {name EvenOddList.cons}`cons` abstracts over the index value used in its recursive occurrence, and instantiates the motive with its negation.
 * The target additionally abstracts over an arbitrary choice of index.

```signature
EvenOddList.rec.{u, v} {α : Type v}
  {motive : (isEven : Bool) → EvenOddList α isEven → Sort u}
  (nil : motive true EvenOddList.nil)
  (cons : {isEven : Bool} →
    (head : α) →
    (tail : EvenOddList α isEven) → motive isEven tail →
    motive (!isEven) (EvenOddList.cons head tail)) :
  {isEven : Bool} → (t : EvenOddList α isEven) → motive isEven t
```
::::
:::::

When using a predicate (that is, a function that returns a {lean}`Prop`) for the motive, recursors express induction.
The cases for non-recursive constructors are the base cases, and the additional arguments supplied to constructors with recursive arguments are the induction hypotheses.

### Subsingleton Elimination
%%%
tag := "subsingleton-elimination"
%%%

Proofs in Lean are computationally irrelevant.
In other words, having been provided with *some* proof of a proposition, it should be impossible for a program to check *which* proof it has received.
This is reflected in the types of recursors for inductively defined propositions or predicates.
For these types, if there's more than one potential proof of the theorem then the motive may only return another {lean}`Prop`.
If the type is structured such that there's only at most one proof anyway, then the motive may return a type in any universe.
A proposition that has at most one inhabitant is called a {deftech}_subsingleton_.
Rather than obligating users to _prove_ that there's only one possible proof, a conservative syntactic approximation is used to check whether a proposition is a subsingleton.
Propositions that fulfill both of the following requirements are considered to be subsingletons:
 * There is at most one constructor.
 * Each of the constructor's parameter types is either a {lean}`Prop`, a parameter, or an index.

:::example "{lean}`True` is a subsingleton"
{lean}`True` is a subsingleton because it has one constructor, and this constructor has no parameters.
Its recursor has the following signature:
```signature
True.rec.{u} {motive : True → Sort u}
  (intro : motive True.intro)
  (t : True) : motive t
```
:::

:::example "{lean}`False` is a subsingleton"
{lean}`False` is a subsingleton because it has no constructors.
Its recursor has the following signature:
```signature
False.rec.{u} (motive : False → Sort u) (t : False) : motive t
```
Note that the motive is an explicit parameter.
This is because it is not mentioned in any further parameters' types, so it could not be solved by unification.
:::


:::example "{name}`And` is a subsingleton"
{lean}`And` is a subsingleton because it has one constructor, and both of the constructor's parameters' types are propositions.
Its recursor has the following signature:
```signature
And.rec.{u} {a b : Prop} {motive : a ∧ b → Sort u}
  (intro : (left : a) → (right : b) → motive (And.intro left right))
  (t : a ∧ b) : motive t
```
:::

:::example "{name}`Or` is not a subsingleton"
{lean}`Or` is not a subsingleton because it has more than one constructor.
Its recursor has the following signature:
```signature
Or.rec {a b : Prop} {motive : a ∨ b → Prop}
  (inl : ∀ (h : a), motive (.inl h))
  (inr : ∀ (h : b), motive (.inr h))
  (t : a ∨ b) : motive t
```
The motive's type indicates that it can only be used to recursor into other propositions.
A proof of a disjunction can be used to prove something else, but there's no way for a program to inspect _which_ of the two disjuncts was true and used for the proof.
:::

:::example "{name}`Eq` is a subsingleton"
{lean}`Eq` is a subsingleton because it has just one constructor, {name}`Eq.refl`.
This constructor instantiates {lean}`Eq`'s index with a parameter value, so all arguments are parameters:
```signature
Eq.refl.{u} {α : Sort u} (x : α) : Eq x x
```

Its recursor has the following signature:
```signature
Eq.rec.{u, v} {α : Sort v} {x : α}
  {motive : (y : α) → x = y → Sort u}
  (refl : motive x (.refl x))
  {y : α} (t : x = y) : motive y t
```
This means that proofs of equality can be used to rewrite the types of non-propositions.
:::

## Reduction
%%%
tag := "iota-reduction"
%%%


In addition to adding new constants to the logic, inductive type declarations also add new reduction rules.
These rules govern the interaction between recursors and constructors; specifically recursors that have constructors as their targets.
This form of reduction is called {deftech}_ι-reduction_ (iota reduction){index}[ι-reduction]{index (subterm:="ι (iota)")}[reduction].

When the recursor's target is a constructor with no recursive parameters, the recursor application reduces to an application of the constructor's case to the constructor's arguments.
If there are recursive parameters, then these arguments to the case are found by applying the recursor to the recursive occurrence.

# Well-Formedness Requirements
%%%
tag := "well-formed-inductives"
%%%

Inductive type declarations are subject to a number of well-formedness requirements.
These requirements ensure that Lean remains consistent as a logic when it is extended with the inductive type's new rules.
They are conservative: there exist potential inductive types that do not undermine consistency, but that these requirements nonetheless reject.

## Universe Levels

Type constructors of inductive types must either inhabit a {tech}[universe] or a function type whose return type is a universe.
Each constructor must inhabit a function type that returns a saturated application of the inductive type.
If the inductive type's universe is {lean}`Prop`, then there are no further restrictions on universes, because {lean}`Prop` is {tech}[impredicative].
If the universe is not {lean}`Prop`, then the following must hold for each parameter to the constructor:
 * If the constructor's parameter is a parameter (in the sense of parameters vs indices) of the inductive type, then this parameter's type may be no larger than the type constructor's universe.
 * All other constructor parameters must be smaller than the type constructor's universe.

:::::keepEnv
::::example "Universes, constructors, and parameters"
{lean}`Either` is in the greater of its arguments' universes, because both are parameters to the inductive type:
```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Either α β
  | inr : β → Either α β
```

{lean}`CanRepr` is in a larger universe than the constructor parameter `α`, because `α` is not one of the inductive type's parameters:
```lean
inductive CanRepr : Type (u + 1) where
  | mk : (α : Type u) → [Repr α] → CanRepr
```

Constructorless inductive types may be in universes smaller than their parameters:
```lean
inductive Spurious (α : Type 5) : Type 0 where
```
It would, however, be impossible to add a constructor to {name}`Spurious` without changing its levels.
::::
:::::

## Strict Positivity
%%%
tag := "strict-positivity"
%%%


All occurrences of the type being defined in the types of the parameters of the constructors must be in {deftech}_strictly positive_ positions.
A position is strictly positive if it is not in a function's argument type (no matter how many function types are nested around it) and it is not an argument of any expression other than type constructors of inductive types.
This restriction rules out unsound inductive type definitions, at the cost of also ruling out some unproblematic ones.

:::::example "Non-strictly-positive inductive types"
::::keepEnv
The type `Bad` would make Lean inconsistent if it were not rejected:
```lean (name := Bad) (error := true)
inductive Bad where
  | bad : (Bad → Bad) → Bad
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```

:::keepEnv
```lean (show := false)
axiom Bad : Type
axiom Bad.bad : (Bad → Bad) → Bad
```
This is because it would be possible to write a circular argument that proves {lean}`False` under the assumption {lean}`Bad`.
{lean}`Bad.bad` is rejected because the constructor's parameter has type {lean}`Bad → Bad`, which is a function type in which {lean}`Bad` occurs as an argument type.
:::

This declaration of a fixed point operator is rejected, because `Fix` occurs as an argument to `f`:
```lean (name := Fix) (error := true)
inductive Fix (f : Type u → Type u) where
  | fix : f (Fix f) → Fix f
```
```leanOutput Fix
(kernel) arg #2 of 'Fix.fix' contains a non valid occurrence of the datatypes being declared
```

`Fix.fix` is rejected because `f` is not a type constructor of an inductive type, but `Fix` itself occurs as an argument to it.
In this case, `Fix` is also sufficient to construct a type equivalent to `Bad`:
```lean (show := false)
axiom Fix : (Type → Type) → Type
```
```lean
def Bad : Type := Fix fun t => t → t
```
::::
:::::


## Prop vs Type
%%%
tag := "prop-vs-type"
%%%

Lean rejects universe-polymorphic types that could not, in practice, be used polymorphically.
This could arise if certain instantiations of the universe parameters would cause the type itself to be a {lean}`Prop`.
If this type is not a {tech}[subsingleton], then is recursor can only target propositions (that is, the {tech}[motive] must return a {lean}`Prop`).
These types only really make sense as {lean}`Prop`s themselves, so the universe polymorphism is probably a mistake.
Because they are largely useless, Lean's inductive type elaborator has not been designed to support these types.

When such universe-polymorphic inductive types are indeed subsingletons, it can make sense to define them.
Lean's standard library defines {name}`PUnit` and {name}`PEmpty`.
To define a subsingleton that can inhabit {lean}`Prop` or a {lean}`Type`, set the option {option}`bootstrap.inductiveCheckResultingUniverse` to {lean}`false`.

{optionDocs bootstrap.inductiveCheckResultingUniverse}

::::keepEnv
:::example "Overly-universe-polymorphic {lean}`Bool`"
Defining a version of {lean}`Bool` that can be in any universe is not allowed:
```lean (error := true) (name := PBool)
inductive PBool : Sort u where
  | true
  | false
```


```leanOutput PBool
invalid universe polymorphic type, the resultant universe is not Prop (i.e., 0), but it may be Prop for some parameter values (solution: use 'u+1' or 'max 1 u')
  u
```
:::
::::



# Constructions for Termination Checking
%%%
tag := "recursor-elaboration-helpers"
%%%

In addition to the type constructor, constructors, and recursors that Lean's core type theory prescribes for inductive types, Lean constructs a number of useful helpers.
First, the equation compiler (which translates recursive functions with pattern matching in to applications of recursors) makes use of these additional constructs:
 * `recOn` is a version of the recursor in which the target is prior to the cases for each constructor.
 * `casesOn` is a version of the recursor in which the target is prior to the cases for each constructor, and recursive arguments do not yield induction hypotheses. It expresses case analysis rather than primitive recursion.
 * `below` computes a type that, for some motive, expresses that _all_ inhabitants of the inductive type that are subtrees of the target satisfy the motive. It transforms a motive for induction or primitive recursion into a motive for strong recursion or strong induction.
 * `brecOn` is a version of the recursor in which `below` is used to provide access to all subtrees, rather than just immediate recursive parameters. It represents strong induction.
 * `noConfusion` is a general statement from which injectivity and disjointness of constructors can be derived.
 * `noConfusionType` is the motive used for `noConfusion` that determines what the consequences of two constructors being equal would be. For separate constructors, this is {lean}`False`; if both constructors are the same, then the consequence is the equality of their respective parameters.


For {tech}[well-founded recursion], it is frequently useful to have a generic notion of size available.
This is captured in the {name}`SizeOf` class.

{docstring SizeOf}
