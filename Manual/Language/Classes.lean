/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Language.Functions
import Manual.Language.Files
import Manual.Language.InductiveTypes
import Manual.Language.Classes.InstanceDecls
import Manual.Language.Classes.InstanceSynth
import Manual.Language.Classes.DerivingHandlers
import Manual.Language.Classes.BasicClasses

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Lean.Parser.Command (declModifiers)

set_option pp.rawOnError true

set_option linter.unusedVariables false

def wadlerBlott89 : InProceedings where
  title := .concat (inlines!"How to make ad-hoc polymorphism less ad hoc")
  authors := #[.concat (inlines!"Philip Wadler"), .concat (inlines!"Stephen Blott")]
  year := 1980
  booktitle := .concat (inlines!"Proceedings of the 16th Symposium on Principles of Programming Languages")

set_option maxRecDepth 100000
#doc (Manual) "Type Classes" =>
%%%
tag := "type-classes"
%%%

An operation is _polymorphic_ if it can be used with multiple types.
In Lean, polymorphism comes in three varieties:

 1. {tech}[universe polymorphism], where the sorts in a definition can be instantiated in various ways,
 2. functions that take types as (potentially implicit) parameters, allowing a single body of code to work with any type, and
 3. {deftech}_ad-hoc polymorphism_, implemented with type classes, in which operations to be overloaded may have different implementations for different types.

Because Lean does not allow case analysis of types, polymorphic functions implement operations that are uniform for any choice of type argument; for example, {name}`List.map` does not suddenly compute differently depending on whether the input list contains {name}`String`s or {name}`Nat`s.
Ad-hoc polymorphic operations are useful when there is no “uniform” way to implement an operation; the canonical use case is for overloading arithmetic operators so that they work with {name}`Nat`, {name}`Int`, {name}`Float`, and any other type that has a sensible notion of addition.
Ad-hoc polymorphism may also involve multiple types; looking up a value at a given index in a collection involves the collection type, the index type, and the type of member elements to be extracted.
A {deftech}_type class_{margin}[Type classes were first described in {citehere wadlerBlott89}[]] describes a collection of overloaded operations (called {deftech}_methods_) together with the involved types.

Type classes are very flexible.
Overloading may involve multiple types; operations like indexing into a data structure can be overloaded for a specific choice of data structure, index type, element type, and even a predicate that asserts the presence of the key in the structure.
Due to Lean's expressive type system, overloading operations is not restricted only to types; type classes may be parameterized by ordinary values, by families of types, and even by predicates or propositions.
All of these possibilities are used in practice:

: Natural number literals

  The {name}`OfNat` type class is used to interpret natural number literals.
  Instances may depend not only on the type being instantiated, but also on the number literal itself.

: Computational effects

  Type classes such as {name}`Monad`, whose parameter is a function from one type to another, are used to provide {ref "monads-and-do"}[special syntax for programs with side effects.]
  The “type” for which operations are overloaded is actually a type-level function, such as {name}`Option`, {name}`IO`, or {name}`Except`.

: Predicates and propositions

  The {name}`Decidable` type class allows a decision procedure for a proposition to be found automatically by Lean.
  This is used as the basis for {keywordOf termIfThenElse}`if`-expressions, which may branch on any decidable proposition.

While ordinary polymorphic definitions simply expect instantiation with arbitrary parameters, the operators overloaded with type classes are to be instantiated with {deftech}_instances_ that define the overloaded operation for some specific set of parameters.
These {deftech}[instance-implicit] parameters are indicated in square brackets.
At invocation sites, Lean either {deftech key:="synthesis"}_synthesizes_ {index}[instance synthesis] {index subterm:="of type class instances"}[synthesis] a suitable instance from the available candidates or signals an error.
Because instances may themselves have instance parameters, this search process may be recursive and result in a final composite instance value that combines code from a variety of instances.
Thus, type class instance synthesis is also a means of constructing programs in a type-directed manner.

Here are some typical use cases for type classes:
 * Type classes may represent overloaded operators, such as arithmetic that can be used with a variety of types of numbers or a membership predicate that can be used for a variety of data structures. There is often a single canonical choice of operator for a given type—after all, there is no sensible alternative definition of addition for {lean}`Nat`—but this is not an essential property, and libraries may provide alternative instances if needed.
 * Type classes can represent an algebraic structure, providing both the extra structure and the axioms required by the structure. For example, a type class that represents an Abelian group may contain methods for a binary operator, a unary inverse operator, an identity element, as well as proofs that the binary operator is associative and commutative, that the identity is an identity, and that the inverse operator yields the identity element on both sides of the operator. Here, there may not be a canonical choice of structure, and a library may provide many ways to instantiate a given set of axioms; there are two equally canonical monoid structures over the integers.
 * A type class can represent a relation between two types that allows them to be used together in some novel way by a library.
   The {lean}`Coe` class represents automatically-inserted coercions from one type to another, and {lean}`MonadLift` represents a way to run operations with one kind of effect in a context that expects another kind.
 * Type classes can represent a framework of type-driven code generation, where instances for polymorphic types each contribute some portion of a final program.
    The {name}`Repr` class defines a canonical pretty-printer for a type, and polymorphic types end up with polymorphic {name}`Repr` instances.
    When pretty printing is finally invoked on an expression with a known concrete type, such as {lean}`List (Nat × (String ⊕ Int))`, the resulting pretty printer contains code assembled from the {name}`Repr` instances for {name}`List`, {name}`Prod`, {name}`Nat`, {name}`Sum`, {name}`String`, and {name}`Int`.

# Class Declarations
%%%
tag := "class"
%%%

Type classes are declared with the {keywordOf Lean.Parser.Command.declaration}`class` keyword.

:::syntax command
```grammar
$_:declModifiers
class $d:declId $_:bracketedBinder*
    $[extends $_,*]? $[: $_]? where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$x:ident],*]?
```

Declares a new type class.
:::

:::keepEnv
```lean (show := false)
-- Just make sure that the `deriving` clause is legit
class A (n : Nat) where
  k : Nat
  eq : n = k
deriving DecidableEq
```
:::


The {keywordOf Lean.Parser.Command.declaration}`class` declaration creates a new single-constructor inductive type, just as if the {keywordOf Lean.Parser.Command.declaration}`structure` command had been used instead.
In fact, the results of the {keywordOf Lean.Parser.Command.declaration}`class` and {keywordOf Lean.Parser.Command.declaration}`structure` commands are almost identical, and features such as default values may be used the same way in both.
Please refer to {ref "structures"}[the documentation for structures] for more information about default values, inheritance, and other features of structures.
The differences between structure and class declarations are:

: Methods instead of fields

  Instead of creating field projections that take a value of the structure type as an explicit parameter, {tech}[methods] are created. Each method takes the corresponding instance as an instance-implicit parameter.

: Instance-implicit parent classes

  The constructor of a class that extends other classes takes its class parents' instances as instance-implicit parameters, rather than explicit parameters.
  When instances of this class are defined, instance synthesis is used to find the values of inherited fields.
  Parents that are not classes are still explicit parameters to the underlying constructor.

: Parent projections via instance synthesis

  Structure field projections make use of {ref "structure-inheritance"}[inheritance information] to project parent structure fields from child structure values.
  Classes instead use instance synthesis: given a child class instance, synthesis will construct the parent; thus, methods are not added to child classes in the same way that projections are added to child structures.

: Registered as class

  The resulting inductive type is registered as a type class, for which instances may be defined and that may be used as the type of instance-implicit arguments.

: Out and semi-out parameters are considered

  The {name}`outParam` and {name}`semiOutParam` {tech}[gadgets] have no meaning in structure definitions, but they are used in class definitions to control instance search.

While {keywordOf Lean.Parser.Command.declaration}`deriving` clauses are allowed for class definitions to maintain the parallel between class and structure elaboration, they are not frequently used and should be considered an advanced feature.

:::example "No Instances of Non-Classes"

Lean rejects instance-implicit parameters of types that are not classes:
```lean (error := true) (name := notClass)
def f [n : Nat] : n = n := rfl
```

```leanOutput notClass
invalid binder annotation, type is not a class instance
  Nat
use the command `set_option checkBinderAnnotations false` to disable the check
```

:::

::::example "Class vs Structure Constructors"
A very small algebraic hierarchy can be represented either as structures ({name}`S.Magma`, {name}`S.Semigroup`, and {name}`S.Monoid` below), a mix of structures and classes ({name}`C1.Monoid`), or only using classes ({name}`C2.Magma`, {name}`C2.Semigroup`, and {name}`C2.Monoid`):
````lean
namespace S
structure Magma (α : Type u) where
  op : α → α → α

structure Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

structure Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end S

namespace C1
class Monoid (α : Type u) extends S.Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C1

namespace C2
class Magma (α : Type u) where
  op : α → α → α

class Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

class Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C2
````


{name}`S.Monoid.mk` and {name}`C1.Monoid.mk` have identical signatures, because the parent of the class {name}`C1.Monoid` is not itself a class:
```signature
S.Monoid.mk.{u} {α : Type u}
  (toSemigroup : S.Semigroup α)
  (ident : α)
  (ident_left : ∀ (x : α), toSemigroup.op ident x = x)
  (ident_right : ∀ (x : α), toSemigroup.op x ident = x) :
  S.Monoid α
```
```signature
C1.Monoid.mk.{u} {α : Type u}
  (toSemigroup : S.Semigroup α)
  (ident : α)
  (ident_left : ∀ (x : α), toSemigroup.op ident x = x)
  (ident_right : ∀ (x : α), toSemigroup.op x ident = x) :
  C1.Monoid α
```

Similarly, because neither `S.Magma` nor `C2.Magma` inherits from another structure or class, their constructors are identical:
```signature
S.Magma.mk.{u} {α : Type u} (op : α → α → α) : S.Magma α
```
```signature
C2.Magma.mk.{u} {α : Type u} (op : α → α → α) : C2.Magma α
```

{name}`S.Semigroup.mk`, however, takes its parent as an ordinary parameter, while {name}`C2.Semigroup.mk` takes its parent as an instance implicit parameter:
```signature
S.Semigroup.mk.{u} {α : Type u}
  (toMagma : S.Magma α)
  (op_assoc : ∀ (x y z : α),
    toMagma.op (toMagma.op x y) z = toMagma.op x (toMagma.op y z)) :
  S.Semigroup α
```
```signature
C2.Semigroup.mk.{u} {α : Type u} [toMagma : C2.Magma α]
  (op_assoc : ∀ (x y z : α),
    toMagma.op (toMagma.op x y) z = toMagma.op x (toMagma.op y z)) :
  C2.Semigroup α
```

Finally, {name}`C2.Monoid.mk` takes its semigroup parent as an instance implicit parameter.
The references to `op` become references to the method {name}`C2.Magma.op`, relying on instance synthesis to recover the implementation from the {name}`C2.Semigroup` instance-implicit parameter via its parent projection:
```signature
C2.Monoid.mk.{u} {α : Type u}
  [toSemigroup : C2.Semigroup α]
  (ident : α)
  (ident_left : ∀ (x : α), C2.Magma.op ident x = x)
  (ident_right : ∀ (x : α), C2.Magma.op x ident = x) :
  C2.Monoid α
```
::::

Parameters to type classes may be marked with {deftech}_gadgets_, which are special versions of the identity function that cause the elaborator to treat a value differently.
Gadgets never change the _meaning_ of a term, but they may cause it to be treated differently in elaboration-time search procedures.
The gadgets {name}`outParam` and {name}`semiOutParam` affect {ref "instance-synth"}[instance synthesis], so they are documented in that section.

Whether a type is a class or not has no effect on definitional equality.
Two instances of the same class with the same parameters are not necessarily identical and may in fact be very different.

::::example "Instances are Not Unique"

This implementation of binary heap insertion is buggy:
````lean
structure Heap (α : Type u) where
  contents : Array α
deriving Repr

def Heap.bubbleUp [Ord α] (i : Nat) (xs : Heap α) : Heap α :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if Ord.compare xs.contents[i] xs.contents[j] == .lt then
      Heap.bubbleUp j {xs with contents := xs.contents.swap ⟨i, by omega⟩ ⟨j, by omega⟩}
    else xs

def Heap.insert [Ord α] (x : α) (xs : Heap α) : Heap α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
````

The problem is that a heap constructed with one {name}`Ord` instance may later be used with another, leading to the breaking of the heap invariant.

One way to correct this is to making the heap type depend on the selected `Ord` instance:
```lean

structure Heap' (α : Type u) [Ord α] where
  contents : Array α

def Heap'.bubbleUp [inst : Ord α] (i : Nat) (xs : @Heap' α inst) : @Heap' α inst :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if inst.compare xs.contents[i] xs.contents[j] == .lt then
      Heap'.bubbleUp j {xs with contents := xs.contents.swap ⟨i, by omega⟩ ⟨j, by omega⟩}
    else xs

def Heap'.insert [Ord α] (x : α) (xs : Heap' α) : Heap' α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
end A
```

In the improved definitions, {name}`Heap'.bubbleUp` is needlessly explicit; the instance does not need to be explicitly named here because Lean would select the indicated instances nonetheless, but it does bring the correctness invariant front and center for readers.
::::

## Sum Types as Classes
%%%
tag := "class inductive"
%%%

Most type classes follow the paradigm of a set of overloaded methods from which clients may choose freely.
This is naturally modeled by a product type, from which the overloaded methods are projections.
Some classes, however, are sum types: they require that the recipient of the synthesized instance first check _which_ of the available instance constructors was provided.
To account for these classes, a class declaration may consist of an arbitrary {tech}[inductive type], not just an extended form of structure declaration.

:::syntax Lean.Parser.Command.declaration
```grammar
$_:declModifiers
class inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$x:ident],*]?
```
:::

Class inductive types are just like other inductive types, except they may participate in instance synthesis.
The paradigmatic example of a class inductive is {name}`Decidable`: synthesizing an instance in a context with free variables amounts to synthesizing the decision procedure, but if there are no free variables, then the truth of the proposition can be established by instance synthesis alone (as is done by the {tactic (show:="decide")}`Lean.Parser.Tactic.decide` tactic).

## Class Abbreviations
%%%
tag := "class-abbrev"
%%%

In some cases, many related type classes may co-occur throughout a codebase.
Rather than writing all the names repeatedly, it would be possible to define a class that extends all the classes in question, contributing no new methods itself.
However, this new class has a disadvantage: its instances must be declared explicitly.

The {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev` command allows the creation of {deftech}_class abbreviations_ in which one name is short for a number of other class parameters.
Behind the scenes, a class abbreviation is represented by a class that extends all the others.
Its constructor is additionally declared to be an instance so the new class can be constructed by instance synthesis alone.

::::keepEnv

:::example "Class Abbreviations"
Both {name}`plusTimes1` and {name}`plusTimes2` require that their parameters' type have {name}`Add` and {name}`Mul` instances:

```lean
class abbrev AddMul (α : Type u) := Add α, Mul α

def plusTimes1 [AddMul α] (x y z : α) := x + y * z

class AddMul' (α : Type u) extends Add α, Mul α

def plusTimes2 [AddMul' α] (x y z : α) := x + y * z
```

Because {name}`AddMul` is a {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev`, no additional declarations are necessary to use {name}`plusTimes1` with {lean}`Nat`:

```lean (name := plusTimes1)
#eval plusTimes1 2 5 7
```
```leanOutput plusTimes1
37
```

However, {name}`plusTimes2` fails, because there is no {lean}`AddMul' Nat` instance—no instances whatsoever have yet been declared:
```lean (name := plusTimes2a) (error := true)
#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2a
failed to synthesize
  AddMul' ?m.22
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
Declaring an very general instance takes care of the problem for {lean}`Nat` and every other type:
```lean (name := plusTimes2b)
instance [Add α] [Mul α] : AddMul' α where

#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2b
37
```
:::
::::

{include 0 Manual.Language.Classes.InstanceDecls}

{include 0 Manual.Language.Classes.InstanceSynth}

# Deriving Instances
%%%
tag := "deriving-instances"
%%%

Lean can automatically generate instances for many classes, a process known as {deftech}_deriving_ instances.
Instance deriving can be invoked either when defining a type or as a stand-alone command.

:::syntax Lean.Parser.Command.optDeriving (open := false)
As part of a command that creates a new inductive type, a {keywordOf Lean.Parser.Command.declaration}`deriving` clause specifies a comma-separated list of class names for which instances should be generated:
```grammar
$[deriving $[$_],*]?
```
:::

:::syntax Lean.Parser.Command.deriving
The stand-alone {keywordOf Lean.Parser.Command.deriving}`deriving` command specifies a number of class names and subject names.
Each of the specified classes are derived for each of the specified subjects.
```grammar
deriving instance $[$_],* for $_,*
```
:::

::::keepEnv
:::example "Deriving Multiple Classes"
After specifying multiple classes to derive for multiple types, as in this code:
```lean
structure A where
structure B where

deriving instance BEq, Repr for A, B
```
all the instances exist for all the types, so all four {keywordOf Lean.Parser.Command.synth}`#synth` commands succeed:
```lean
#synth BEq A
#synth BEq B
#synth Repr A
#synth Repr B
```
:::
::::

{include 2 Manual.Language.Classes.DerivingHandlers}

{include 0 Manual.Language.Classes.BasicClasses}
