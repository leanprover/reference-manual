import VersoManual

import Manual.Meta
import Manual.Language.InductiveTypes.Structures

open Verso.Genre Manual

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

#doc (Manual) "Inductive Types" =>

{deftech}_Inductive types_ are the primary means of introducing new types to Lean.
While {tech}[universes] and {tech}[functions] are built-in primitives that could not be added by users, every other {tech}[canonical] {TODO}[Harmonize terminology: "type constructor" is probably better] type former in Lean is an inductive type.
Inductive types are specified by their {deftech}_type constructors_ {index}[type constructor] and their {deftech}_constructors_; {index}[constructor] their other properties are derived from these.
Each inductive type has a single type constructor, which may take both {tech}[universe parameters] and ordinary parameters.
Inductive types may have any number of constructors; these constructors introduce new values whose types are headed by the inductive type's type constructor.

Based on the type constructor and the constructors for an inductive type, Lean derives a {deftech}_recursor_{index}[recursor]{see "recursor"}[eliminator].
Logically, recursors represent induction principles or elimination rules; computationally, they represent primitive recursive computations.
The termination of recursive functions is justified by translating them into uses of the recursors, so Lean's kernel only needs to perform type checking of recursor applications, rather than including a separate termination analysis.
Lean additionally produces a number of helper constructions based on the recursor, which are used elsewhere in the system.
{TODO}[Sidebar note: "recursor" is always used, even for non-recursive types]

_Structures_ are a special case of inductive types that have exactly one constructor.
When a structure is declared, Lean generates helpers that enable additional language features to be used with the new structure.

This section describes the specific details of the syntax used to specify both inductive types and structures, the new constants and definitions in the environment that result from inductive type declarations, and the run-time representation of inductive types' values in compiled code.

# Inductive Type Declarations


:::syntax command (alias := «inductive»)
```grammar
$_:declModifiers
inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$_ $[with $_]?],*]?
```

Declares a new inductive type.
The meaning of the {syntaxKind}`declModifiers` is as described in the section {ref "declaration-modifiers"}[on declaration modifiers].
:::

After declaring an inductive type, its type constructor, constructors, and recursor are present in the environment.
New inductive types extend Lean's core logic—they are not encoded or represented by some other already-present data.
Inductive type declarations must satisfy {ref "well-formed-inductives"}[a number of well-formedness requirements] to ensure that the logic remains consistent.

The first line of the declaration, from {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`inductive` to {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`, specifies the new {tech}[type constructor]'s name and type.
If a type signature for the type constructor is provided, then its result type must be a {tech}[universe], but the parameters do not need to be types.
If no signature is provided, then Lean will infer a universe that's just big enough to contain the resulting type.

The constructor specifications follow {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`.
Constructors are not mandatory, as constructorless datatypes such as {lean}`False` and {lean}`Empty` are perfectly sensible.
Each constructor specification begins with a vertical bar (`'|'`, Unicode `'VERTICAL BAR' (U+007c)`), declaration modifiers, and a name.
The name is a {tech}[raw identifier].
A declaration signature follows the name.
The signature may specify any parameters, modulo the well-formedness requirements for inductive type declarations, but the return type of the signature must be in the inductive type being specified.
If no signature is provided, then the constructor's type is inferred by inserting sufficient implicit parameters to construct a well-formed return type.

The new inductive type's name is prefixed by the {TODO}[xref] current namespace.
Each constructor's name is prefixed by the current namespace and the inductive type's name.

## Parameters and Indices

Type constructors may take two kinds of arguments: {deftech}_parameters_ and {deftech key:="index"}_indices_.
Parameters must be used consistently in the entire definition; all occurrences of the type constructor in each constructor in the declaration must take precisely the same argument.
Indices may vary among the occurrences of the type constructor.
All parameters must precede all indices in the type constructor's signature.

Parameters that occur prior to the colon (`':'`) in the type constructor's signature are considered parameters to the entire inductive type declaration.
They are always parameters, while those that occur after the colon may by parameters or indices.
The distinction is inferred from the way in which they are used in the specifications of the constructors.

## Example Inductive Types

:::example "A constructorless type"
{lean}`Zero` is an empty datatype, equivalent to Lean's {lean}`Empty` type:
```lean
inductive Zero : Type where
```

Empty datatypes are not useless; they can be used to indicate unreachable code.
:::

:::example "A constructorless proposition"
{lean}`No` is a false {tech}[proposition], equivalent to Lean's {lean}`False`:
```lean
inductive No : Prop where
```

```lean (show := false) (keep := false)
theorem no_is_false : No = False := by
  apply propext
  constructor <;> intro h <;> cases h
```
:::

:::example "A unit type"
{lean}`One` is equivalent to Lean's {lean}`Unit` type:
```lean
inductive One where
  | one
```
It is an example of an inductive type in which the signatures have been omitted for both the type constructor and the constructor.
Lean assigns {lean}`One` to {lean}`Type`:
```lean (name := OneTy)
#check One
```
```leanOutput OneTy
One : Type
```
The constructor is named {lean}`One.one`, because constructor names are the type constructor's namespace.
Because {lean}`One` expects no arguments, the signature inferred for {lean}`One.one` is:
```lean (name := oneTy)
#check One.one
```
```leanOutput oneTy
One.one : One
```
:::


:::example "A true proposition"
{lean}`Yes` is equivalent to Lean's {lean}`True` proposition:

```lean
inductive Yes : Prop where
  | intro
```
Unlike {lean}`One`, the new inductive type {lean}`Yes` is specified to be in the {lean}`Prop` universe.
```lean (name := YesTy)
#check Yes
```
```leanOutput YesTy
Yes : Prop
```
The signature inferred for {lean}`Yes.intro` is:
```lean (name := yesTy)
#check Yes.intro
```
```leanOutput yesTy
Yes.intro : Yes
```

```lean (show := false) (keep := false)
theorem yes_is_true : Yes = True := by
  apply propext
  constructor <;> intros <;> constructor
```
:::

::::example "A type with parameter and index"

:::keepEnv
```lean (show:=false)
universe u
axiom α : Type u
axiom b : Bool
```

An {lean}`EvenOddList α b` is a list where {lean}`α` is the type of the data stored in the list and {lean}`b` is {lean}`true` when there are an even number of entries:
:::

```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```

This example is well typed because there are two entries in the list:
```lean
example : EvenOddList String true :=
  .cons "a" (.cons "b" .nil)
```

This example is not well typed because there are three entries in the list:
```lean (error := true) (name := evenOddOops)
example : EvenOddList String true :=
  .cons "a" (.cons "b" (.cons "c" .nil))
```
```leanOutput evenOddOops
type mismatch
  EvenOddList.cons "a" (EvenOddList.cons "b" (EvenOddList.cons "c" EvenOddList.nil))
has type
  EvenOddList String !!!true : Type
but is expected to have type
  EvenOddList String true : Type
```

:::keepEnv
```lean (show:=false)
universe u
axiom α : Type u
axiom b : Bool
```

In this declaration, {lean}`α` is a {tech}[parameter], because it is used consistently in all occurrences of {name}`EvenOddList`.
{lean}`b` is an {tech}[index], because different {lean}`Bool` values are used for it at different occurrences.
:::


```lean (show:=false) (keep:=false)
def EvenOddList.length : EvenOddList α b → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

theorem EvenOddList.length_matches_evenness (xs : EvenOddList α b) : b = (xs.length % 2 = 0) := by
  induction xs
  . simp [length]
  next b' _ xs ih =>
    simp [length]
    cases b' <;> simp only [Bool.true_eq_false, false_iff, true_iff] <;> simp at ih <;> omega
```
::::

:::::keepEnv
::::example "Parameters before and after the colon"

In this example, both parameters are specified before the colon in {name}`Either`'s signature.

```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | left : α → Either α β
  | right : α → Either α β
```

In this version, there are two types named `α` that might not be identical:
```lean (name := Either') (error := true)
inductive Either' (α : Type u) (β : Type v) : Type (max u v) where
  | left : {α : Type u} → {β : Type v} → α → Either' α β
  | right : α → Either' α β
```
```leanOutput Either'
inductive datatype parameter mismatch
  α
expected
  α✝
```

Placing the parameters after the colon results in parameters that can be instantiated by the constructors:
```lean (name := Either'')
inductive Either'' : Type u → Type v → Type (max u v) where
  | left : {α : Type u} → {β : Type v} → α → Either'' α β
  | right : α → Either'' α β
```
{name}`Either''.right`'s type parameters are discovered via Lean's ordinary rules for unbound implicit arguments. {TODO}[xref]
::::
:::::


## Anonymous Constructor Syntax

If an inductive type has just one constructor, then this constructor is eligible for {deftech}_anonymous constructor syntax_.
Instead of writing the constructor's name applied to its arguments, the explicit arguments can be enclosed in angle brackets (`'⟨'` and `'⟩'`, Unicode `MATHEMATICAL LEFT ANGLE BRACKET	(U+0x27e8)` and `MATHEMATICAL RIGHT ANGLE BRACKET	(U+0x27e9)`) and separated with commas.
This works in both pattern and expression contexts.
Providing arguments by name or converting all implicit parameters to explicit with `@` requires using the ordinary constructor syntax.

::::example "Anonymous constructors"

:::keepEnv
```lean (show:=false)
axiom α : Type
```
The type {lean}`AtLeastOne α` is similar to `List α`, except there's always at least one element present:
:::

```lean
inductive AtLeastOne (α : Type u) : Type u where
  | mk : α → Option (AtLeastOne α) → AtLeastOne α
```

Anonymous constructor syntax can be used to construct them:
```lean
def oneTwoThree : AtLeastOne Nat :=
  ⟨1, some ⟨2, some ⟨3, none⟩⟩⟩
```
and to match against them:
```lean
def AtLeastOne.head : AtLeastOne α → α
  | ⟨x, _⟩ => x
```

Equivalently, traditional constructor syntax could have been used:
```lean
def oneTwoThree' : AtLeastOne Nat :=
  .mk 1 (some (.mk 2 (some (.mk 3 none))))

def AtLeastOne.head' : AtLeastOne α → α
  | .mk x _ => x
```
::::


## Deriving Instances

The optional {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`deriving` clause of an inductive type declaration can be used to derive instances of type classes.
Please refer to {TODO}[write it!] the section on instance deriving for more information.

:::TODO
 * Deriving (just xref)
 * Interaction with `variable` (xref)
:::


{include 0 Manual.Language.InductiveTypes.Structures}

# Logical Model

## Recursors

Every inductive type is equipped with a {tech}[recursor].
The recursor is completely determined by the signatures of the type constructor and the constructors.
Recursors have function types, but they are primitive and are not definable using `fun`.

### Recursor Types

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
{lean}`Bool`'s recursor {lean}`Bool.rec` has the following parameters:

 * The motive computes a type in any universe, given a Bool.
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
{lean}`List`'s recursor {lean}`List.rec` has the following parameters:

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


::::example "The recursor for {name}`EvenOddList`"
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
Rather than obligating users to _prove_ that there's only one possible proof, a conservative syntactic overapproximation is used to check whether a proposition is a subsingleton.
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
{lean}`And` is a subsingleton because it has one constructor, and both of the constructor's parameters's types are propositions.
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

### Reduction

In addition to adding new constants to the logic, inductive datatype declarations also add new reduction rules.
These rules govern the interaction between recursors and constructors; specifically recursors that have constructors as their targets.
This form of reduction is called {deftech}_ι-reduction_ (iota reduction){index}[ι-reduction]{index (subterm:="ι (iota)")}[reduction].

When the recursor's target is a constructor with no recursive parameters, the recursor application reduces to an application of the constructor's case to the constructor's arguments.
If there are recursive parameters, then these arguments to the case are found by applying the recursor to the recursive occurrence.

## Well-Formedness Requirements
%%%
tag := "well-formed-inductives"
%%%

Inductive datatype declarations are subject to a number of well-formedness requirements.
These requirements ensure that Lean remains consistent as a logic when it is extended with the inductive type's new rules.
They are conservative: there exist potential inductive types that do not undermine consistency, but that these requirements nonetheless reject.

### Universe Levels

Type constructors of inductive types must either inhabit a {tech}[universe] or a function type whose return type is a universe.
Each constructor must inhabit a function type that returns a saturated application of the inductive type.
If the inductive type's universe is {lean}`Prop`, then there are no further restrictions on universes.
If the is not {lean}`Prop`, then the following must hold for each parameter to the constructor:
 * If the constructor's parameter is a parameter (in the sense of parameters vs indices) of the inductive type, then this parameter's type may be no larger than the type constructor's universe.
 * All other constructor parameters must be smaller than the type constructor's universe.


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

### Strict Positivity

All occurrences of the type being defined in the types of the parameters of the constructors must be in {deftech}_strictly positive_ positions.
A position is strictly positive if it is not in a function's argument type (no matter how many function types are nested around it) and it is not an argument of any expression other than type constructors of inductive types.
This restriction rules out unsound inductive type definitions, at the cost of also ruling out some unproblematic ones.

::::example "Non-strictly-positive inductive types"
:::keepEnv
The datatype `Bad` would make Lean inconsistent if it were not rejected:
```lean (name := Bad) (error := true)
inductive Bad where
  | bad : (Bad → Bad) → Bad
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```
This is because it would be possible to write a circular argument that proves `False` under the assumption `Bad`.
`Bad.bad` is rejected because the constructor's parameter has type `Bad → Bad`, which is a function type in which `Bad` occurs as an argument type.

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
:::
::::


### Prop vs Type

:::TODO
Explain this:
````
invalid universe polymorphic type, the resultant universe is not Prop (i.e., 0), but it may be Prop for some parameter values (solution: use 'u+1' or 'max 1 u'){indentD u}"
````
:::


# Constructions for Termination Checking

In addition to the type constructor, constructors, and recursors that Lean's core type theory prescribes for inductive types, Lean constructs a number of useful helpers.
First, the equation compiler (which translates recursive functions with pattern matching in to applications of recursors) makes use of these additional constructs:
 * `recOn` is a version of the recursor in which the target is prior to the cases for each constructor.
 * `casesOn` is a version of the recursor in which the target is prior to the cases for each constructor, and recursive arguments do not yield induction hypotheses. It expresses case analysis rather than primitive recursion.
 * `below` computes a type that, for some motive, expresses that _all_ inhabitants of the inductive type that are subtrees of the target satisfy the motive. It transforms a motive for induction or primitive recursion into a motive for strong recursion or strong induction.
 * `brecOn` is a version of the recursor in which `below` is used to provide access to all subtrees, rather than just immediate recursive parameters. It represents strong induction.
 * `noConfusion` is a general statement from which injectivity and disjointness of constructors can be derived.
 * `noConfusionType` is the motive used for `noConfusion` that determines what the consequences of two constructors being equal would be. For separate constructors, this is {lean}`False`; if both constructors are the same, then the consequence is the equality of their respective parameters.


For well-founded recursion{TODO}[xref], it is frequently useful to have a generic notion of size available.
This is captured in the {name}`SizeOf` class.

{docstring SizeOf}


# Run-Time Representation

An inductive type's run-time representation depends both on how many constructors it has, how many arguments each constructor takes, and whether these arguments are {tech}[relevant].

## Exceptions

Not every inductive type is represented as indicated here—some inductive types have special support from the Lean compiler:
:::keepEnv
````lean (show := false)
axiom α : Prop
````

 * The fixed-width integer types {lean}`UInt8`, ..., {lean}`UInt64`, and {lean}`USize` are represented by the C types `uint8_t`, ..., `uint64_t`, and `size_t`, respectively.

 * {lean}`Char` is represented by `uint32_t`

 * {lean}`Float` is represented by `double`

 * An {deftech}_enum inductive_ type of at least 2 and at most $`2^32` constructors, each of which has no parameters, is represented by the first type of `uint8_t`, `uint16_t`, `uint32_t` that is sufficient to assign a unique value to each constructor. For example, the type {lean}`Bool` is represented by `uint8_t`, with values `0` for {lean}`false` and `1` for {lean}`true`. {TODO}[Find out whether this should say "no relevant parameters"]

 * {lean}`Decidable α` is represented the same way as `Bool` {TODO}[Aren't Decidable and Bool just special cases of the rules for trivial constructors and irrelevance?]

 * {lean}`Nat` is represented by `lean_object *`. Its run-time value is either a pointer to an opaque bignum object or, if the lowest bit of the "pointer" is `1` (checked by `lean_is_scalar`), an encoded unboxed natural number (`lean_box`/`lean_unbox`). {TODO}[Move these to FFI section or Nat chapter]
:::

## Relevance

Types and proofs have no run-time representation.
That is, if an inductive type is a `Prop`, then its values are erased prior to compilation.
Similarly, all theorem statements and types are erased.
Types with run-time representations are called {deftech}_relevant_, while types without run-time representations are called {deftech}_irrelevant_.

:::example "Types are irrelevant"
Even though {name}`List.cons` has the following signature, which indicates three parameters:
```signature
List.cons.{u} {α : Type u} : α → List α → List α
```
its run-time representation has only two, because the type argument is run-time irrelevant.
:::

:::example "Proofs are irrelevant"
Even though {name}`Fin.mk` has the following signature, which indicates three parameters:
```signature
Fin.mk {n : Nat} (val : Nat) : val < n → Fin n
```
its run-time representation has only two, because the proof is erased.
:::

In most cases, irrelevant values simply disappear from compiled code.
However, in cases where some representation is required (such as when they are arguments to polymorphic constructors), they are represented by a trivial value.

## Trivial Wrappers

If an inductive type has exactly one constructor, and that constructor has exactly one run-time relevant parameter, then the inductive type is represented identically to its parameter.

:::example "Zero-Overhead Subtypes"
The structure {name}`Subtype` bundles an element of some type with a proof that it satisfies a predicate.
Its constructor takes four arguments, but three of them are irrelevant:
```signature
Subtype.mk.{u} {α : Sort u} {p : α → Prop}
  (val : α) (property : p val) : Subtype p
```
Thus, subtypes impose no runtime overhead in compiled code, and are represented identically to the type of the {name Subtype.val}`val` field.
:::

## Other Inductive Types

If an inductive type doesn't fall into one of the categories above, then its representation is determined by its constructors.
Constructors without relevant parameters are represented by their index into the list of constructors, as unboxed unsigned machine integers (scalars).
Constructors with relevant parameters are represented as an object with a header, the constructor's index, an array of pointers to other objects, and then arrays of scalar fields sorted by their types.
The header tracks the object's reference count and other necessary bookkeeping.

Recursive functions are compiled as they are in most programming languages, rather than by using the inductive type's recursor.
Elaborating recursive functions to recursors serves to provide reliable termination evidence, not executable code.

### FFI

From the perspective of C, these other inductive types are represented by `lean_object *`.
Each constructor is stored as a `lean_ctor_object`, and `lean_is_ctor` will return true.
A `lean_ctor_object` stores the constructor index in its header, and the fields are stored in the `m_objs` portion of the object.

The memory order of the fields is derived from the types and order of the fields in the declaration. They are ordered as follows:

* Non-scalar fields stored as `lean_object *`
* Fields of type {lean}`USize`
* Other scalar fields, in decreasing order by size

Within each group the fields are ordered in declaration order. **Warning**: Trivial wrapper types still count toward a field being treated as non-scalar for this purpose.

* To access fields of the first kind, use `lean_ctor_get(val, i)` to get the `i`th non-scalar field.
* To access {lean}`USize` fields, use `lean_ctor_get_usize(val, n+i)` to get the `i`th usize field and `n` is the total number of fields of the first kind.
* To access other scalar fields, use `lean_ctor_get_uintN(val, off)` or `lean_ctor_get_usize(val, off)` as appropriate. Here `off` is the byte offset of the field in the structure, starting at `n*sizeof(void*)` where `n` is the number of fields of the first two kinds.

For example, a structure such as
```lean
structure S where
  ptr_1 : Array Nat
  usize_1 : USize
  sc64_1 : UInt64
  ptr_2 : { x : UInt64 // x > 0 } -- wrappers don't count as scalars
  sc64_2 : Float -- `Float` is 64 bit
  sc8_1 : Bool
  sc16_1 : UInt16
  sc8_2 : UInt8
  sc64_3 : UInt64
  usize_2 : USize
  ptr_3 : Char -- trivial wrapper around `UInt32`
  sc32_1 : UInt32
  sc16_2 : UInt16
```
would get re-sorted into the following memory order:

* {name}`S.ptr_1` - `lean_ctor_get(val, 0)`
* {name}`S.ptr_2` - `lean_ctor_get(val, 1)`
* {name}`S.ptr_3` - `lean_ctor_get(val, 2)`
* {name}`S.usize_1` - `lean_ctor_get_usize(val, 3)`
* {name}`S.usize_2` - `lean_ctor_get_usize(val, 4)`
* {name}`S.sc64_1` - `lean_ctor_get_uint64(val, sizeof(void*)*5)`
* {name}`S.sc64_2` - `lean_ctor_get_float(val, sizeof(void*)*5 + 8)`
* {name}`S.sc64_3` - `lean_ctor_get_uint64(val, sizeof(void*)*5 + 16)`
* {name}`S.sc32_1` - `lean_ctor_get_uint32(val, sizeof(void*)*5 + 24)`
* {name}`S.sc16_1` - `lean_ctor_get_uint16(val, sizeof(void*)*5 + 28)`
* {name}`S.sc16_2` - `lean_ctor_get_uint16(val, sizeof(void*)*5 + 30)`
* {name}`S.sc8_1` - `lean_ctor_get_uint8(val, sizeof(void*)*5 + 32)`
* {name}`S.sc8_2` - `lean_ctor_get_uint8(val, sizeof(void*)*5 + 33)`

::: TODO
Figure out how to test/validate/CI these statements
:::


# Mutual Inductive Types

::: TODO
1. Explain syntax

2. Generalize the following:
 * Recursor spec
 * Positivity condition

3. What doesn't change?
 * FFI/cost model is the same

:::
