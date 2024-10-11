import VersoManual

import Manual.Meta
import Manual.Language.Files
import Manual.Language.InductiveTypes

import Lean.Parser.Command

open Verso.Genre Manual
open Lean.Parser.Command (declModifiers)

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "The Lean Language" =>

{include Manual.Language.Files}

# Types

::: TODO
Basic framework of the type theory goes here.

{deftech}[Canonical] type formers, definitional equality, types as first-class entities, large elimination
:::

## Functions

::: TODO
Write this section.

Topics:
 * Dependent vs non-dependent {deftech}[function] types
 * Eta equivalence
 * Don't talk recursion (that goes in inductive types), but xref to it
 * Syntax of anonymous functions with/without pattern matching
 * Strictness
:::

## Propositions
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

  With the exception of singletons, propositions cannot be eliminated into non-proposition types.

: {deftech key:="propositional extensionality"}[Extensionality] {index subterm:="of propositions"}[extensionality]

  Any two logically equivalent propositions can be proven to be equal with the {lean}`propext` axiom.

{docstring propext}

## Universes

Types are classified by {deftech}_universes_. {index}[universe]
Each universe has a {deftech (key:="universe level")}_level_, {index subterm := "of universe"}[level] which is a natural number.
The {lean}`Sort` operator constructs a universe from a given level. {index}[`Sort`]
If the level of a universe is smaller than that of another, the universe itself is said to be smaller.
With the exception of propositions (described later in this chapter), types in a given universe may only quantify over types in smaller universes.
{lean}`Sort 0` is the type of propositions, while each `Sort (u + 1)` is a type that describes data.

Every universe is an element of every strictly larger universe, so {lean}`Sort 5` includes {lean}`Sort 4`.
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

### Predicativity

Each universe contains dependent function types, which additionally represent universal quantification and implication.
A function type's universe is determined by the universes of its argument and return types.
The specific rules depend on whether the return type of the function is a proposition.

Predicates, which are functions that return propositions (that is, where the result type of the function is some type in `Prop`) may have argument types in any universe whatsoever, but the function type itself remains in `Prop`.
In other words, propositions feature {deftech}[_impredicative_] {index}[impredicative]{index subterm := "impredicative"}[quantification] quantification, because propositions can themselves be statements about all propositions (and all other types).

:::example "Impredicativity"
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

:::example "Universe levels of function types"
Both of these types are in {lean}`Type 2`:
```lean
example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β
```
:::

:::example "Predicativity of {lean}`Type`"
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

:::example "No cumulativity"
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

### Polymorphism

Lean supports {deftech}_universe polymorphism_, {index subterm:="universe"}[polymorphism] {index}[universe polymorphism] which means that constants defined in the Lean environment can take {deftech}[universe parameters].
These parameters can then be instantiated with universe levels when the constant is used.
Universe parameters are written in curly braces following a dot after a constant name.

:::example "Universe-polymorphic identity function"
When fully explicit, the identity function takes a universe parameter `u`. Its signature is:
```signature
id.{u} {α : Sort u} (x : α) : α
```
:::

Universe variables may additionally occur in {ref "level-expressions"}[universe level expressions], which provide specific universe levels in definitions.
When the polymorphic definition is instantiated with concrete levels, these universe level expressions are also evaluated to yield concrete levels.

::::keepEnv
:::example "Universe level expressions"

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

:::example "Universe polymorhism is not first-class"

This can be seen in the following example, in which `T` is a gratuitously-universe-polymorphic definition that always returns the constructor of the unit type.
Both instantiations of `T` have the same value, and both have the same type, but their differing universe instantiations make them incompatible:
```lean (error := true) (name := uniIncomp) (keep := false)
abbrev T.{u} : Unit := (fun (α : Sort u) => ()) PUnit.{u}

set_option pp.universes true

def test.{u, v} : T.{u} = T.{v} := rfl
```
```leanOutput uniIncomp
type mismatch
  rfl.{1}
has type
  Eq.{1} T.{u} T.{u} : Prop
but is expected to have type
  Eq.{1} T.{u} T.{v} : Prop
```

```lean (error := false) (keep := false) (show := false)
-- check that the above statement stays true
abbrev T : Unit := (fun (α : Type) => ()) Unit

def test : T = T := rfl
```
:::

Auto-bound implicit arguments are as universe-polymorphic as possible.
Defining the identity function as follows:
```lean
def id' (x : α) := x
```
results in the signature:
```signature
id'.{u} {α : Sort u} (x : α) : α
```

:::example "Universe monomorphism in auto-bound implicit"
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

#### Level Expressions
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

#### Universe Variable Bindings

Universe-polymorphic definitions bind universe variables.
These bindings may be either explicit or implicit.
Explicit universe variable binding and instantiation occurs as a suffix to the definition's name.
Universe parameters are defined or provided by suffixing the name of a constant with a period (`.`) followed by a comma-separated sequence of universe variables between curly braces.

::::keepEnv
:::example "Universe-polymorphic `map`"
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

::: example "Auto-implicits and universe polymorphism"
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

In addition to using `autoImplicit`, particular identifiers can be declared as universe variables in a particular {tech}[scope] using the `universe` command.

:::syntax Lean.Parser.Command.universe
```grammar
universe $x:ident $xs:ident*
```

Declares one or more universe variables for the extent of the current scope.

Just as the `variable` command causes a particular identifier to be treated as a parameter with a particular type, the `universe` command causes the subsequent identifiers to be implicitly quantified as as universe parameters in declarations that mention them, even if the option `autoImplicit` is {lean}`false`.
:::

:::example "The `universe` command when `autoImplicit` is `false`"
```lean (keep := false)
set_option autoImplicit false
universe u
def id₃ (α : Type u) (a : α) := a
```
:::

Because automatic implicit arguments only insert parameters that are used in the declaration's {tech}[header], universe variables that occur only on the right-hand side of a definition are not inserted as arguments unless they have been declared with `universe` even when `autoImplicit` is `true`.

:::example "Automatic universe parameters and the `universe` command"

This definition with an explicit universe parameter is accepted:
```lean (keep := false)
def L.{u} := List (Type u)
```
Even with automatic implicits, this definition is rejected, because `u` is not mentioned in the header, which precedes the `:=`:
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

#### Universe Unification

:::TODO
 * Rules for unification, properties of algorithm
 * Lack of injectivity
:::

{include 2 Language.InductiveTypes}


## Quotients
%%%
tag := "quotients"
%%%

:::planned
 * Define quotient type
 * Show the computation rule
:::

# Module Structure


## Commands and Declarations

### Definition-Like Commands

The following commands in Lean are definition-like: {TODO}[Render commands as their name (a la tactic index)]
 * {syntaxKind}`def`
 * {syntaxKind}`abbrev`
 * {syntaxKind}`example`
 * {syntaxKind}`theorem`

All of these commands cause Lean to {tech key:="elaborator"}[elaborate] a term based on a signature.
With the exception of {syntaxKind}`example`, which discards the result, the resulting expression in Lean's core language is saved for future use in the environment.

:::syntax Lean.Parser.Command.declaration
```grammar
$_:declModifiers
$_:definition
```
:::

:::syntax Lean.Parser.Command.definition
```grammar
def $_ $_ := $_
```

```grammar
def $_ $_
  $[| $_ => $_]*
```

```grammar
def $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.theorem
```grammar
theorem $_ $_ := $_
```

```grammar
theorem $_ $_
  $[| $_ => $_]*
```

```grammar
theorem $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.abbrev
```grammar
abbrev $_ $_ := $_
```

```grammar
abbrev $_ $_
  $[| $_ => $_]*
```

```grammar
abbrev $_ $_ where
  $_*
```
:::


:::TODO
Move `instance` to type classes section with a backreference from here
:::

:::syntax Lean.Parser.Command.instance
```grammar
instance $_? : $_ := $_
```

```grammar
instance $_? : $_
  $[| $_ => $_]*
```

```grammar
instance $_? : $_ where
  $_*
```
:::


:::syntax Lean.Parser.Command.example
```grammar
example $_ $_ := $_
```

```grammar
example $_ $_
  $[| $_ => $_]*
```

```grammar
example $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.opaque
```grammar
opaque $_ $_
```
:::

:::syntax Lean.Parser.Command.axiom
```grammar
axiom $_ $_
```
:::


### Modifiers
%%%
tag := "declaration-modifiers"
%%%

::: planned
A description of each modifier allowed in the production `declModifiers`, including {deftech}[documentation comments].
:::

:::syntax declModifiers alias:=Lean.Parser.Command.declModifiers

```grammar
$_
$_
$_
$_
$_
$_
```

:::

### Signatures

:::planned
Describe signatures, including the following topics:
 * Explicit, implicit, instance-implicit, and strict implicit parameter binders
 * {deftech}_Automatic implicits_
 * Argument names and by-name syntax
 * Which parts can be omitted where? Why?
:::

### Headers

The {deftech}[_header_] of a definition or declaration specifies the signature of the new constant that is defined.

::: TODO
* Precision and examples; list all of them here
* Mention interaction with autoimplicits
:::

## Section Scopes
%%%
tag := "scopes"
%%%

::: planned
Many commands have an effect for the current {deftech key:="scope"}[_section scope_] (sometimes just called "scope" when clear).
A section scope ends when a namespace ends, a section ends, or a file ends.
They can also be anonymously and locally created via `in`.
Section scopes track the following:
 * The {deftech}_current namespace_
 * The {deftech}_open namespaces_
 * The values of all {deftech}_options_
 * Variable and universe declarations

This section will describe this mechanism.
:::

# Recursive Definitions

## Structural Recursion
::: planned
This section will describe the specification of the translation to recursors.
:::

### Mutual Structural Recursion

::: planned
This section will describe the specification of the translation to recursors.
:::

## Well-Founded Recursion
%%%
tag := "well-founded-recursion"
%%%

::: planned
This section will describe the translation of {deftech}[well-founded recursion].
:::

## Controlling Reduction

:::planned
This section will describe {deftech}[reducible], {deftech}[semireducible], and {deftech}[irreducible] definitions.
:::

## Partial and Unsafe Recursive Definitions
%%%
tag := "partial-unsafe"
%%%

:::planned
This section will describe `partial` and `unsafe` definitions
:::

# Type Classes

## Class Declarations

::: planned
This section will describe the syntax of `class` and `class inductive` declarations.
The desugaring of `class` to `structure` and thus `inductive` will be addressed, along with the determining of implicitness of method parameters.
:::

## Instance Declarations

::: planned
This section will describe the syntax of `instance` declarations, priorities, and names.
:::


## Instance Synthesis

::: planned
This section will specify the instance synthesis algorithm.
:::

## Deriving Instances
%%%
tag := "deriving-instances"
%%%

::: planned
This section will specify syntax of `deriving` clauses and list the valid places where they may occur.
It will also describe `deriving instance`.
It will list the deriving handlers that ship with Lean by default.
:::


### Deriving Handlers

::: planned
This section will describe deriving handlers and how they are invoked.
:::
