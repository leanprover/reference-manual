/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.Language.Functions
import Manual.Language.InductiveTypes

open Verso.Genre Manual

set_option maxRecDepth 800

#doc (Manual) "The Type System" =>
%%%
tag := "type-system"
%%%

{deftech}_Terms_, also known as {deftech}_expressions_, are the fundamental units of meaning in Lean's core language.
They are produced from user-written syntax by the {tech}[elaborator].
Lean's type system relates terms to their _types_, which are also themselves terms.
Types can be thought of as denoting sets, while terms denote individual elements of these sets.
A term is {deftech}_well-typed_ if it has a type under the rules of Lean's type theory.
Only well-typed terms have a meaning.

Terms are a dependently typed λ-calculus: they include function abstraction, application, variables, and `let`-bindings.
In addition to bound variables, variables in the term language may refer to {tech}[constructors], {tech}[type constructors], {tech}[recursors], {deftech}[defined constants], or opaque constants.
Constructors, type constructors, recursors, and opaque constants are not subject to substitution, while defined constants may be replaced with their definitions.

A {deftech}_derivation_ demonstrates the well-typedness of a term by explicitly indicating the precise inference rules that are used.
Implicitly, well-typed terms can stand in for the derivations that demonstrate their well-typedness.
Lean's type theory is explicit enough that derivations can be reconstructed from well-typed terms, which greatly reduces the overhead that would be incurred from storing a complete derivation, while still being expressive enough to represent modern research mathematics.
This means that proof terms are sufficient evidence of the truth of a theorem and are amenable to independent verification.

In addition to having types, terms are also related by {deftech}_definitional equality_.
This is the mechanically-checkable relation that equates terms modulo their computational behavior.
Definitional equality includes the following forms of {deftech}[reduction]:

 : {deftech}[β] (beta)

    Applying a function abstraction to an argument by substitution for the bound variable

 : {deftech}[δ] (delta)

    Replacing occurrences of {tech}[defined constants] by the definition's value

 : {deftech}[ι] (iota)

    Reduction of recursors whose targets are constructors (primitive recursion)

 : {deftech}[ζ] (zeta)

     Replacement of let-bound variables by their defined values

Terms in which all possible reductions have been carried out are in {deftech}_normal form_.

::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : Type
axiom f : α → β

structure S where
  f1 : α
  f2 : β

axiom x : S

-- test claims in next para

example : (fun x => f x) = f := by rfl
example : S.mk x.f1 x.f2 = x := by rfl

export S (f1 f2)
```

Definitional equality includes η-equivalence of functions and single-constructor inductive types.
That is, {lean}`fun x => f x` is definitionally equal to {lean}`f`, and {lean}`S.mk x.f1 x.f2` is definitionally equal to {lean}`x`, if {lean}`S` is a structure with fields {lean}`f1` and {lean}`f2`.
It also features proof irrelevance, so any two proofs of the same proposition are definitionally equal.
It is reflexive, symmetric, and a congruence.
::::

Definitional equality is used by conversion: if two terms are definitionally equal, and a given term has one of them as its type, then it also has the other as its type.
Because definitional equality includes reduction, types can result from computations over data.

::::keepEnv
:::Manual.example "Computing types"

When passed a natural number, the function {lean}`LengthList` computes a type that corresponds to a list with precisely that many entries in it:

```lean
def LengthList (α : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => α × LengthList α n
```

Because Lean's tuples nest to the right, multiple nested parentheses are not needed:
````lean
example : LengthList Int 0 := ()

example : LengthList String 2 :=
  ("Hello", "there", ())
````

If the length does not match the number of entries, then the computed type will not match the term:
```lean error:=true name:=wrongNum
example : LengthList String 5 :=
  ("Wrong", "number", ())
```
```leanOutput wrongNum
application type mismatch
  ("number", ())
argument
  ()
has type
  Unit : Type
but is expected to have type
  LengthList String 3 : Type
```
:::
::::

The basic types in Lean are {tech}[universes], {tech}[function] types, and {tech}[type constructors] of {tech}[inductive types].
{tech}[Defined constants], applications of {tech}[recursors], function application, {tech}[axioms] or {tech}[opaque constants] may additionally give types, just as they can give rise to terms in any other type.


{include Manual.Language.Functions}

# Propositions
%%%
tag := "propositions"
%%%

{deftech}[Propositions] are meaningful statements that admit proof. {index}[proposition]
Nonsensical statements are not propositions, but false statements are.
All propositions are classified by {lean}`Prop`.

Propositions have the following properties:

: Definitional proof irrelevance

  Any two proofs of the same proposition are completely interchangeable.

: Run-time irrelevance

  Propositions are erased from compiled code.

: Impredicativity

  Propositions may quantify over types from any universe whatsoever.

: Restricted Elimination

  With the exception of {tech}[subsingletons], propositions cannot be eliminated into non-proposition types.

: {deftech key:="propositional extensionality"}[Extensionality] {index subterm:="of propositions"}[extensionality]

  Any two logically equivalent propositions can be proven to be equal with the {lean}`propext` axiom.

{docstring propext}

# Universes

Types are classified by {deftech}_universes_. {index}[universe]
Each universe has a {deftech (key:="universe level")}_level_, {index subterm := "of universe"}[level] which is a natural number.
The {lean}`Sort` operator constructs a universe from a given level. {index}[`Sort`]
If the level of a universe is smaller than that of another, the universe itself is said to be smaller.
With the exception of propositions (described later in this chapter), types in a given universe may only quantify over types in smaller universes.
{lean}`Sort 0` is the type of propositions, while each `Sort (u + 1)` is a type that describes data.

Every universe is an element of the next larger universe, so {lean}`Sort 5` includes {lean}`Sort 4`.
This means that the following examples are accepted:
```lean
example : Sort 5 := Sort 4
example : Sort 2 := Sort 1
```

On the other hand, {lean}`Sort 3` is not an element of {lean}`Sort 5`:
```lean (error := true) (name := sort3)
example : Sort 5 := Sort 3
```

```leanOutput sort3
type mismatch
  Type 2
has type
  Type 3 : Type 4
but is expected to have type
  Type 4 : Type 5
```

Similarly, because {lean}`Unit` is in {lean}`Sort 1`, it is not in {lean}`Sort 2`:
```lean
example : Sort 1 := Unit
```
```lean error := true name := unit1
example : Sort 2 := Unit
```

```leanOutput unit1
type mismatch
  Unit
has type
  Type : Type 1
but is expected to have type
  Type 1 : Type 2
```

Because propositions and data are used differently and are governed by different rules, the abbreviations {lean}`Type` and {lean}`Prop` are provided to make the distinction more convenient.  {index}[`Type`] {index}[`Prop`]
`Type u` is an abbreviation for `Sort (u + 1)`, so {lean}`Type 0` is {lean}`Sort 1` and {lean}`Type 3` is {lean}`Sort 4`.
{lean}`Type 0` can also be abbreviated {lean}`Type`, so `Unit : Type` and `Type : Type 1`.
{lean}`Prop` is an abbreviation for {lean}`Sort 0`.

## Predicativity

Each universe contains dependent function types, which additionally represent universal quantification and implication.
A function type's universe is determined by the universes of its argument and return types.
The specific rules depend on whether the return type of the function is a proposition.

Predicates, which are functions that return propositions (that is, where the result of the function is some type in `Prop`) may have argument types in any universe whatsoever, but the function type itself remains in `Prop`.
In other words, propositions feature {deftech}[_impredicative_] {index}[impredicative]{index subterm := "impredicative"}[quantification] quantification, because propositions can themselves be statements about all propositions (and all other types).

:::Manual.example "Impredicativity"
Proof irrelevance can be written as a proposition that quantifies over all propositions:
```lean
example : Prop := ∀ (P : Prop) (p1 p2 : P), p1 = p2
```

A proposition may also quantify over all types, at any given level:
```lean
example : Prop := ∀ (α : Type), ∀ (x : α), x = x
example : Prop := ∀ (α : Type 5), ∀ (x : α), x = x
```
:::

For universes at {tech key:="universe level"}[level] `1` and higher (that is, the `Type u` hierarchy), quantification is {deftech}[_predicative_]. {index}[predicative]{index subterm := "predicative"}[quantification]
For these universes, the universe of a function type is the least upper bound of the argument and return types' universes.

:::Manual.example "Universe levels of function types"
Both of these types are in {lean}`Type 2`:
```lean
example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β
```
:::

:::Manual.example "Predicativity of {lean}`Type`"
This example is not accepted, because `α`'s level is greater than `1`. In other words, the annotated universe is smaller than the function type's universe:
```lean error := true name:=toosmall
example (α : Type 2) (β : Type 1) : Type 1 := α → β
```
```leanOutput toosmall
type mismatch
  α → β
has type
  Type 2 : Type 3
but is expected to have type
  Type 1 : Type 2
```
:::

Lean's universes are not {deftech}[cumulative];{index}[cumulativity] a type in `Type u` is not automatically also in `Type (u + 1)`.
Each type inhabits precisely one universe.

:::Manual.example "No cumulativity"
This example is not accepted because the annotated universe is larger than the function type's universe:
```lean error := true name:=toobig
example (α : Type 2) (β : Type 1) : Type 3 := α → β
```
```leanOutput toobig
type mismatch
  α → β
has type
  Type 2 : Type 3
but is expected to have type
  Type 3 : Type 4
```
:::

## Polymorphism

Lean supports {deftech}_universe polymorphism_, {index subterm:="universe"}[polymorphism] {index}[universe polymorphism] which means that constants defined in the Lean environment can take {deftech}[universe parameters].
These parameters can then be instantiated with universe levels when the constant is used.
Universe parameters are written in curly braces following a dot after a constant name.

:::Manual.example "Universe-polymorphic identity function"
When fully explicit, the identity function takes a universe parameter `u`. Its signature is:
```signature
id.{u} {α : Sort u} (x : α) : α
```
:::

Universe variables may additionally occur in {ref "level-expressions"}[universe level expressions], which provide specific universe levels in definitions.
When the polymorphic definition is instantiated with concrete levels, these universe level expressions are also evaluated to yield concrete levels.

::::keepEnv
:::Manual.example "Universe level expressions"

In this example, {lean}`Codec` is in a universe that is one greater than the universe of the type it contains:
```lean
structure Codec.{u} : Type (u + 1) where
  type : Type u
  encode : Array UInt32 → type → Array UInt32
  decode : Array UInt32 → Nat → Option (type × Nat)
```

Lean automatically infers most level parameters.
In the following example, it is not necessary to annotate the type as {lean}`Codec.{0}`, because {lean}`Char`'s type is {lean}`Type 0`, so `u` must be `0`:
```lean (keep := true)
def Codec.char : Codec where
  type := Char
  encode buf ch := buf.push ch.val
  decode buf i := do
    let v ← buf[i]?
    if h : v.isValidChar then
      let ch : Char := ⟨v, h⟩
      return (ch, i + 1)
    else
      failure
```
:::
::::

Universe-polymorphic definitions in fact create a _schematic definition_ that can be instantiated at a variety of levels, and different instantiations of universes create incompatible values.

::::keepEnv
:::Manual.example "Universe polymorphism and definitional equality"

This can be seen in the following example, in which {lean}`T` is a gratuitously-universe-polymorphic function that always returns {lean}`true`.
Because it is marked {keywordOf Lean.Parser.Command.declaration}`opaque`, Lean can't check equality by unfolding the definitions.
Both instantiations of {lean}`T` have the parameters and the same type, but their differing universe instantiations make them incompatible.
```lean (error := true) (name := uniIncomp)
opaque T.{u} (_ : Nat) : Bool := (fun (α : Sort u) => true) PUnit.{u}

set_option pp.universes true

def test.{u, v} : T.{u} 0 = T.{v} 0 := rfl
```
```leanOutput uniIncomp
type mismatch
  rfl.{?u.27}
has type
  Eq.{?u.27} ?m.29 ?m.29 : Prop
but is expected to have type
  Eq.{1} (T.{u} 0) (T.{v} 0) : Prop
```
:::
::::

Auto-bound implicit arguments are as universe-polymorphic as possible.
Defining the identity function as follows:
```lean
def id' (x : α) := x
```
results in the signature:
```signature
id'.{u} {α : Sort u} (x : α) : α
```

:::Manual.example "Universe monomorphism in auto-bound implicit parameters"
On the other hand, because {name}`Nat` is in universe {lean}`Type 0`, this function automatically ends up with a concrete universe level for `α`, because `m` is applied to both {name}`Nat` and `α`, so both must have the same type and thus be in the same universe:
```lean
partial def count [Monad m] (p : α → Bool) (act : m α) : m Nat := do
  if p (← act) then
    return 1 + (← count p act)
  else
    return 0
```

```lean (show := false)
/-- info: Nat : Type -/
#guard_msgs in
#check Nat

/--
info: count.{u_1} {m : Type → Type u_1} {α : Type} [Monad m] (p : α → Bool) (act : m α) : m Nat
-/
#guard_msgs in
#check count
```
:::

### Level Expressions
%%%
tag := "level-expressions"
%%%

Levels that occur in a definition are not restricted to just variables and addition of constants.
More complex relationships between universes can be defined using level expressions.

````
Level ::= 0 | 1 | 2 | ...  -- Concrete levels
        | u, v             -- Variables
        | Level + n        -- Addition of constants
        | max Level Level  -- Least upper bound
        | imax Level Level -- Impredicative LUB
````

Given an assignment of level variables to concrete numbers, evaluating these expressions follows the usual rules of arithmetic.
The `imax` operation is defined as follows:

$$``\mathtt{imax}\ u\ v = \begin{cases}0 & \mathrm{when\ }v = 0\\\mathtt{max}\ u\ v&\mathrm{otherwise}\end{cases}``

`imax` is used to implement {tech}[impredicative] quantification for {lean}`Prop`.
In particular, if `A : Sort u` and `B : Sort v`, then `(x : A) → B : Sort (imax u v)`.
If `B : Prop`, then the function type is itself a {lean}`Prop`; otherwise, the function type's level is the maximum of `u` and `v`.

### Universe Variable Bindings

Universe-polymorphic definitions bind universe variables.
These bindings may be either explicit or implicit.
Explicit universe variable binding and instantiation occurs as a suffix to the definition's name.
Universe parameters are defined or provided by suffixing the name of a constant with a period (`.`) followed by a comma-separated sequence of universe variables between curly braces.

::::keepEnv
:::Manual.example "Universe-polymorphic `map`"
The following declaration of {lean}`map` declares two universe parameters (`u` and `v`) and instantiates the polymorphic {name}`List` with each in turn:
```lean
def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    List.{u} α → List.{v} β
  | [] => []
  | x :: xs => f x :: map f xs
```
:::
::::

Just as Lean automatically instantiates implicit parameters, it also automatically instantiates universe parameters.
When the {TODO}[describe this option and add xref] `autoImplicit` option is set to {lean}`true` (the default), it is not necessary to explicitly bind universe variables.
When it is set to {lean}`false`, then they must be added explicitly or declared using the `universe` command. {TODO}[xref]

:::Manual.example "Auto-implicits and universe polymorphism"
When `autoImplicit` is {lean}`true` (which is the default setting), this definition is accepted even though it does not bind its universe parameters:
```lean (keep := false)
set_option autoImplicit true
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

When `autoImplicit` is {lean}`false`, the definition is rejected because `u` and `v` are not in scope:
```lean (error := true) (name := uv)
set_option autoImplicit false
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```leanOutput uv
unknown universe level 'u'
```
```leanOutput uv
unknown universe level 'v'
```
:::

In addition to using `autoImplicit`, particular identifiers can be declared as universe variables in a particular {tech}[section scope] using the `universe` command.

:::syntax Lean.Parser.Command.universe
```grammar
universe $x:ident $xs:ident*
```

Declares one or more universe variables for the extent of the current scope.

Just as the `variable` command causes a particular identifier to be treated as a parameter with a particular type, the `universe` command causes the subsequent identifiers to be implicitly quantified as as universe parameters in declarations that mention them, even if the option `autoImplicit` is {lean}`false`.
:::

:::Manual.example "The `universe` command when `autoImplicit` is `false`"
```lean (keep := false)
set_option autoImplicit false
universe u
def id₃ (α : Type u) (a : α) := a
```
:::

Because the automatic implicit parameter feature only insert parameters that are used in the declaration's {tech}[header], universe variables that occur only on the right-hand side of a definition are not inserted as arguments unless they have been declared with `universe` even when `autoImplicit` is `true`.

:::Manual.example "Automatic universe parameters and the `universe` command"

This definition with an explicit universe parameter is accepted:
```lean (keep := false)
def L.{u} := List (Type u)
```
Even with automatic implicit parameters, this definition is rejected, because `u` is not mentioned in the header, which precedes the `:=`:
```lean (error := true) (name := unknownUni) (keep := false)
set_option autoImplicit true
def L := List (Type u)
```
```leanOutput unknownUni
unknown universe level 'u'
```
With a universe declaration, `u` is accepted as a parameter even on the right-hand side:
```lean (keep := false)
universe u
def L := List (Type u)
```
The resulting definition of `L` is universe-polymorphic, with `u` inserted as a universe parameter.

Declarations in the scope of a `universe` command are not made polymorphic if the universe variables do not occur in them or in other automatically-inserted arguments.
```lean
universe u
def L := List (Type 0)
#check L
```
:::

### Universe Unification

:::planned 99
 * Rules for unification, properties of algorithm
 * Lack of injectivity
 * Universe inference for unannotated inductive types
:::

### Universe Lifting

:::planned 174
 * When to use universe lifting?
:::

{docstring PLift}

{docstring ULift}

{include 0 Language.InductiveTypes}


# Quotients
%%%
tag := "quotients"
%%%

:::planned 51
 * Define {deftech}[quotient] type
 * Show the computation rule
:::
