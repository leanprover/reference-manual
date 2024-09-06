import VersoManual

import Manual.Meta
import Manual.Language.InductiveTypes.LogicalModel
import Manual.Language.InductiveTypes.Structures

open Verso.Genre Manual

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800

#doc (Manual) "Inductive Types" =>

{deftech}_Inductive types_ are the primary means of introducing new types to Lean.
While {tech}[universes] and {tech}[functions] are built-in primitives that could not be added by users, every other type in Lean is either an inductive type or defined in terms universes, functions, and inductive types..
Inductive types are specified by their {deftech}_type constructors_ {index}[type constructor] and their {deftech}_constructors_; {index}[constructor] their other properties are derived from these.
Each inductive type has a single type constructor, which may take both {tech}[universe parameters] and ordinary parameters.
Inductive types may have any number of constructors; these constructors introduce new values whose types are headed by the inductive type's type constructor.

Based on the type constructor and the constructors for an inductive type, Lean derives a {deftech}_recursor_{index}[recursor]{see "recursor"}[eliminator].
Logically, recursors represent induction principles or elimination rules; computationally, they represent primitive recursive computations.
The termination of recursive functions is justified by translating them into uses of the recursors, so Lean's kernel only needs to perform type checking of recursor applications, rather than including a separate termination analysis.
Lean additionally produces a number of helper constructions based on the recursor,{margin}[The term _recursor_ is always used, even for non-recursive datatypes.] which are used elsewhere in the system.


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
If no signature is provided, then Lean will attempt to infer a universe that's just big enough to contain the resulting type.
In some situations, this process may fail to find a minimal universe or fail to find one at all, necessitating an annotation.

The constructor specifications follow {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`.
Constructors are not mandatory, as constructorless datatypes such as {lean}`False` and {lean}`Empty` are perfectly sensible.
Each constructor specification begins with a vertical bar (`'|'`, Unicode `'VERTICAL BAR' (U+007c)`), declaration modifiers, and a name.
The name is a {tech}[raw identifier].
A declaration signature follows the name.
The signature may specify any parameters, modulo the well-formedness requirements for inductive type declarations, but the return type in the signature must be a saturated application of the type constructor of the inductive type being specified.
If no signature is provided, then the constructor's type is inferred by inserting sufficient implicit parameters to construct a well-formed return type.

The new inductive type's name is defined in the {tech}[current namespace].
Each constructor's name is in the inductive type's namespace.{index subterm:="of inductive type"}[namespace]

## Parameters and Indices

Type constructors may take two kinds of arguments: {deftech}_parameters_ {index subterm:="of inductive type"}[parameter] and {deftech key:="index"}_indices_.{index subterm:="of inductive type"}[index]
Parameters must be used consistently in the entire definition; all occurrences of the type constructor in each constructor in the declaration must take precisely the same argument.
Indices may vary among the occurrences of the type constructor.
All parameters must precede all indices in the type constructor's signature.

Parameters that occur prior to the colon (`':'`) in the type constructor's signature are considered parameters to the entire inductive type declaration.
They are always parameters that must be uniform throughout the type's definition.
Generally speaking, parameters that occur after the colon are indices that may vary throughout the definition of the type.
However, if the option {option}`inductive.autoPromoteIndices` is {lean}`true`, then syntactic indices that could have been parameters are made into parameters.
An index could have been a parameter if all of its type dependencies are themselves parameters and it is used uniformly as an uninstantiated variable in all occurrences of the inductive type's type constructor in all constructors.

{optionDocs inductive.autoPromoteIndices}

Indices can be seen as defining a _family_ of types.
Each choice of indices selects a type from the family, which has its own set of available constructors.
Type constructors that take index parameters are referred to as {deftech}_indexed families_ {index subterm:="of types"}[indexed family] of types.

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
{name}`Either''.right`'s type parameters are discovered via Lean's ordinary rules for {tech}[automatic implicit] parameters.
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
Please refer to {ref "deriving-instances"}[the section on instance deriving] for more information.


{include 0 Manual.Language.InductiveTypes.Structures}

{include 0 Manual.Language.InductiveTypes.LogicalModel}

# Run-Time Representation
%%%
tag := "run-time-inductives"
%%%

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

Inductive types may be mutually recursive.
Mutually recursive definitions of inductive types are specified by defining the types in a `mutual ... end` block.

:::example "Mutually Defined Inductive Types"
The type {name}`EvenOddList` in a prior example used a Boolean index to select whether the list in question should have an even or odd number of elements.
This distinction can also be expressed by the choice of one of two mutually inductive datatypes {name}`EvenList` and {name}`OddList`:

```lean
mutual
  inductive EvenList (α : Type u) : Type u where
    | nil : EvenList α
    | cons : α → OddList α → EvenList α
  inductive OddList (α : Type u) : Type u where
    | cons : α → EvenList α → OddList α
end

example : EvenList String := .cons "x" (.cons "y" .nil)
example : OddList String := .cons "x" (.cons "y" (.cons "z" .nil))
```
```lean (error := true) (name := evenOddMut)
example : OddList String := .cons "x" (.cons "y" .nil)
```
```leanOutput evenOddMut
invalid dotted identifier notation, unknown identifier `OddList.nil` from expected type
  OddList String
```
:::

## Requirements

The inductive types declared in a `mutual` block are considered as a group; they must collectively satisfy generalized versions of the well-formedness criteria for non-mutually-recursive inductive types.
This is true even if they could be defined without the `mutual` block, because they are not in fact mutually recursive.

### Mutual Dependencies

Each type constructor's signature must be able to be elaborated without reference to the other inductive types in the `mutual` group.
In other words, the inductive types in the `mutual` group may not take each other as arguments.
The constructors of each inductive type may mention the other type constructors in the group in their parameter types, with restrictions that are a generalization of those for recursive occurrences in non-mutual inductive types.

:::example "Mutual inductive type constructors may not mention each other"
These inductive types are not accepted by Lean:
```lean (error:=true) (name := mutualNoMention)
mutual
  inductive FreshList (α : Type) (r : α → α → Prop) : Type where
    | nil : FreshList α r
    | cons (x : α) (xs : FreshList α r) (fresh : Fresh r x xs)
  inductive Fresh (r : α → FreshList α → Prop) : α → FreshList α r → Prop where
    | nil : Fresh r x .nil
    | cons : r x y → (f : Fresh r x ys) → Fresh r x (.cons y ys f)
end
```

The type constructors may not refer to the other type constructors in the `mutual` group, so `FreshList` is not in scope in the type constructor of `Fresh`:
```leanOutput mutualNoMention
unknown identifier 'FreshList'
```
:::


### Parameters Must Match

All inductive types in the `mutual` group must have the same {tech}[parameters].
Their indices may differ.

::::keepEnv
::: example "Differing numbers of parameters"
Even though `Both` and `OneOf` are not mutually recursive, they are declared in the same `mutual` block and must therefore have identical parameters:
```lean (name := bothOptional) (error := true)
mutual
  inductive Both (α : Type u) (β : Type v) where
    | mk : α → β → Both α β
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput bothOptional
invalid inductive type, number of parameters mismatch in mutually inductive datatypes
```
:::
::::

::::keepEnv
::: example "Differing parameter types"
Even though `Many` and `OneOf` are not mutually recursive, they are declared in the same `mutual` block and must therefore have identical parameters.
They both have exactly one parameter, but `Many`'s parameter is not necessarily in the same universe as `Optional`'s:
```lean (name := manyOptional) (error := true)
mutual
  inductive Many (α : Type) : Type u where
    | nil : Many α
    | cons : α → Many α → Many α
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput manyOptional
invalid mutually inductive types, parameter 'α' has type
  Type u : Type (u + 1)
but is expected to have type
  Type : Type 1
```
:::
::::

### Universe Levels

The universe levels of each inductive type in a mutual group must obey the same requirements as non-mutually-recursive inductive types.
Additionally, all the inductive types in a mutual group must be in the same universe, which implies that their constructors are similarly limited with respect to their parameters' universes.

::::example "Universe mismatch"
:::keepEnv
These mutually-inductive types are a somewhat complicated way to represent run-length encoding of a list:
```lean
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) : n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Type where
  | zero (noMore : ¬∃zs, xs = x :: zs := by simp) : PrefixRunOf 0 x xs xs
  | succ : PrefixRunOf n x xs ys → PrefixRunOf (n + 1) x (x :: xs) ys
end

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] :=
  .run 1 2 (by decide) (.succ (.succ .zero)) <|
  .run 2 2 (by decide) (.succ (.succ .zero)) <|
  .run 3 1 (by decide) (.succ .zero) <|
  .run 1 3 (by decide) (.succ (.succ (.succ (.zero)))) <|
  .nil
```

Specifying {name}`PrefixRunOf` as a {lean}`Prop` would be sensible, but it cannot be done because the types would be in different universes:
:::

:::keepEnv
```lean (error :=true) (name := rleBad)
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) : n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Prop where
  | zero (noMore : ¬∃zs, xs = x :: zs := by simp) : PrefixRunOf 0 x xs xs
  | succ : PrefixRunOf n x xs ys → PrefixRunOf (n + 1) x (x :: xs) ys
end
```
```leanOutput rleBad
invalid mutually inductive types, resulting universe mismatch, given
  Prop
expected type
  Type
```
:::

:::keepEnv
This particular property can be expressed by separately defining the well-formedness condition and using a subtype:
```lean
def RunLengths α := List (α × Nat)
def NoRepeats : RunLengths α → Prop
  | [] => True
  | [_] => True
  | (x, _) :: ((y, n) :: xs) =>
    x ≠ y ∧ NoRepeats ((y, n) :: xs)
def RunsMatch : RunLengths α → List α → Prop
  | [], [] => True
  | (x, n) :: xs, ys =>
    ys.take n = List.replicate n x ∧
    RunsMatch xs (ys.drop n)
  | _, _ => False
def NonZero : RunLengths α → Prop
  | [] => True
  | (_, n) :: xs => n ≠ 0 ∧ NonZero xs
structure RLE (xs : List α) where
  rle : RunLengths α
  noRepeats : NoRepeats rle
  runsMatch : RunsMatch rle xs
  nonZero : NonZero rle

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] where
  rle := [(1, 2), (2, 2), (3, 1), (1, 3)]
  noRepeats := by simp [NoRepeats]
  runsMatch := by simp [RunsMatch]
  nonZero := by simp [NonZero]
```
:::
::::


### Positivity
Each inductive type that is defined in the `mutual` group may occur only strictly positively in the types of the parameters of the constructors of all the types in the group.
In other words, in the type of each parameter to each constructor in all the types of the group, none of the type constructors in the group occur to the left of any arrows, and none of them occur in argument positions unless they are an argument to an inductive datatype's type constructor.

::: example "Mutual strict positivity"
In the following mutual group, `Tm` occurs in a negative position in the argument to `Binding.scope`:
```lean (error := true) (name := mutualHoas)
mutual
  inductive Tm where
    | app : Tm → Tm → Tm
    | lam : Binding → Tm
  inductive Binding where
    | scope : (Tm → Tm) → Binding
end
```
Because `Tm` is part of the same mutual group, it must occur only strictly positively in the arguments to the constructors of `Binding`.
It occurs, however, negatively:
```leanOutput mutualHoas
(kernel) arg #1 of 'Binding.scope' has a non positive occurrence of the datatypes being declared
```
:::

::: example "Nested positions"
The definitions of {name}`LocatedStx` and {name}`Stx` satisfy the positivity condition because the recursive occurrences are not to the left of any arrows and, when they are arguments, they are arguments to inductive type constructors.

```lean
mutual
  inductive LocatedStx where
    | mk (line col : Nat) (val : Stx)
  inductive Stx where
    | atom (str : String)
    | node (kind : String) (args : List LocatedStx)
end
```
:::

## Recursors

Mutual inductive types are provided with primitive recursors, just like non-mutually-defined inductive types.
These recursors take into account that they must process the other types in the group, and thus will have a motive for each inductive type.
Because all inductive types in the `mutual` group are required to have identical parameters, the recursors still take the parameters first, abstracting them over the motives and the rest of the recursor.
Additionally, because the recursor must process the group's other types, it will require cases for each constructor of each of the types in the group.
The actual dependency structure between the types is not taken into account; even if an additional motive or constructor case is not really required due to there being fewer mutual dependencies than there could be, the generated recursor still requires them.

::: example "Even and odd"
```lean
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end
```

```signature
Even.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : {n : Nat} → (a : Odd n) → motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) →
  ∀ {a : Nat} (t : Even a), motive_1 a t
```

```signature
Odd.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : ∀ {n : Nat} (a : Odd n), motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) → ∀ {a : Nat} (t : Odd a), motive_2 a t
```

:::

:::example "Spuriously mutual types"
The types {name}`Two` and {name}`Three` are defined in a mutual block, even though they do not refer to each other:
```lean
mutual
  inductive Two (α : Type) where
    | mk : α → α → Two α
  inductive Three (α : Type) where
    | mk : α → α → α → Three α
end
```
{name}`Two`'s recursor, {name}`Two.rec`, nonetheless requires a motive and a case for {name}`Three`:
```signature
Two.rec.{u} {α : Type}
  {motive_1 : Two α → Sort u}
  {motive_2 : Three α → Sort u}
  (mk : (a a_1 : α) → motive_1 (Two.mk a a_1)) :
  ((a a_1 a_2 : α) → motive_2 (Three.mk a a_1 a_2)) → (t : Two α) → motive_1 t
```

:::

## Run-Time Representation

Mutual inductive types are represented identically to {ref "run-time-inductives"}[non-mutual inductive types] in compiled code and in the runtime.
The restrictions on mutual inductive types exist to ensure Lean's consistency as a logic, and do not impact compiled code.
