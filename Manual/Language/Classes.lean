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
import Manual.Language.Classes.InstanceSynth

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Lean.Parser.Command (declModifiers)

set_option pp.rawOnError true

set_option linter.unusedVariables false

-- TODO figure out why this is needed.
set_option maxRecDepth 100000
#doc (Manual) "Type Classes" =>
%%%
tag := "type-classes"
%%%

Type classes are a structured approach to {deftech}_ad-hoc polymorphism_, in which operations to be overloaded may have different implementations for different types.
Ordinary polymorphic definitions implement operations that are uniform for any choice of parameters; for example, {name}`List.map` does not suddenly compute a different result depending on whether the input list contains {name}`String`s or {name}`Nat`s.
Ad-hoc polymorphic operations are useful when there is no “uniform” way to implement an operation; the canonical use case is for overloading arithmetic operators so that they work with {name}`Nat`, {name}`Int`, {name}`Float`, and any other suitable type.
A type class describes a collection of overloaded operations (called {deftech}_methods_) together with the involved types.

Type classes are very flexible.
Overloading may involve multiple types; operations like indexing into a data structure can be overloaded for a specific choice of data structure, index type, element type, and even a predicate that asserts the presence of the key in the structure.
Due to Lean's expressive type system, overloading is not restricted even to types; type classes may be parameterized over ordinary values, over functions or indexed families of types, and predicates or propositions.
All of these possibilities are used in practice, from overloading natural number notation using {name}`OfNat`, contexts in which certain computational effects may occur using {name}`Monad`, and predicates using {name}`Decidable`.

While ordinary polymorphic definitions simply expect instantiation with arbitrary parameters, the operators overloaded with type classes are to be instantiated with {deftech}_instances_ that define the overloaded operation for some specific set of parameters.
These instance parameters are indicated in square brackets, and the values that are suitable for selection as instance parameters are tracked in internal tables.
At invocation sites, Lean either {deftech key:="synthesis"}_synthesizes_ {index}[instance synthesis] {index subterm:="of instances"}[synthesis] a suitable instance from the available candidates or signals an error.
Because instances may themselves have instance parameters, this search process may be recursive and result in a final composite instance value that combines code from a variety of instances.
Thus, type class instance synthesis is also a means of constructing programs in a type-directed manner.

Here are some typical use cases for type classes:
 * Type classes may represent overloaded operators, such as arithmetic that works on a variety of types of numbers or a membership predicate that can be used for a variety of data structures. There is often a single canonical choice of operator for a given type.
 * Type classes can represent an algebraic structure, provided both the extra structure and the axioms required by the structure. For example, a type class that represents an Abelian group may contain methods for a binary operator, a unary inverse operator, an identity element, as well as proofs that the binary operator is associative and commutative, that the identity is an identity, and that the inverse operator yields the identity element on both sides of the operator. Here, there may not be a canonical choice of structure, and a library may provide many ways to instantiate a given set of axioms.
 * Type classes can represent a framework of type-drive code generation, where polymorphic types each contribute some portion of a final program.
    The {name}`Repr` class defines a canonical pretty-printer for a datatype, and polymorphic types end up with polymorphic {name}`Repr` instances.
    When pretty printing is finally invoked on a concrete type, such as {lean}`List (Nat × (String ⊕ Int))`, the resulting pretty printer contains code assembled from the instances for {name}`List`, {name}`Prod`, {name}`Nat`, {name}`Sum`, {name}`String`, and {name}`Int`.

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
$[deriving $[$_ $[with $_]?],*]?
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

  Instead of creating field projections that take a value of the structure type as an explicit parameter, methods are created. Each method takes the corresponding instance as an instance-implicit parameter.

: Instance-implicit parent classes

  The constructor of a class that extends other classes takes its class parents' instances as instance-implicit parameters, rather than explicit parameters. Parents that are not classes are still explicit parameters.

: Parent projections via instance synthesis

  Structure field projections make use of {ref "structure-inheritance"}[inheritance information] to project parent structure fields from children. Classes instead use instance synthesis: given a child class instance, synthesis will construct the parent; thus, methods are not added to child classes as projections are added to child structures.

: Registered as class

  The resulting datatype is registered as a type class, for which instances may be defined and that may be used as the type of instance-implicit arguments.

: Out and semi-out parameters are considered

  The {name}`outParam` and {name}`semiOutParam` {tech}[gadgets] have no meaning in structure definitions, but they are used in class definitions to control instance search.

While {keywordOf Lean.Parser.Command.declaration}`deriving` clauses are allowed for class definitions to maintain the parallel between class and structure elaboration, they are not frequently used and should be considered an advanced feature.

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
Similarly, the references to {name}`C2.Magma.op` refer directly to {name}`C2.Magma.op`, relying on instance synthesis to recover the implementation from the {name}`C2.Semigroup` instance-implicit parameter:
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
As the gadgets {name}`outParam` and {name}`semiOutParam` affect {ref "instance-synth"}[instance synthesis], they are documented in that section.

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

One way to correct this is to making the heap datatype depend on the selected `Ord` instance:
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

Most type classes follow the paradigm of a set of overloaded methods from which clients may choose freely by applying the appropriate projection to the underlying product type.
Some classes, however, are sum types: they require that the recipient of the synthesized instance first check _which_ of the kinds of instance were available.
To account for these classes, a class declaration may consist of an arbitrary inductive datatype, not just a form of structures.

:::syntax Lean.Parser.Command.declaration
```grammar
$_:declModifiers
class inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$_ $[with $_]?],*]?
```
:::

Class inductive types are just like other inductive types, except they may participate in instance synthesis.
The paradigmatic example of a class inductive is {name}`Decidable`.

## Class Abbreviations
%%%
tag := "class-abbrev"
%%%

In some cases, many related type classes may co-occur throughout a codebase.
Rather than writing all the names repeatedly, it would be possible to define a class that extends all the classes in question, contributing no new methods itself.
However, this new class has a disadvantage: its instances must be declared explicitly.

The {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev` command allows the creation of {deftech}_class abbreviations_ in which one name is short for a number of other class parameters.
Behind the scenes, a class abbreviation is represented by a class that extends all the others; its constructor is additionally added to the instance synthesis table so that an instance need not be added manually.

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

# Instance Declarations
%%%
tag := "instance-declarations"
%%%


The syntax of instance declarations is almost identical to that of definitions.
The only syntactic differences are that the keyword {keywordOf Lean.Parser.Command.declaration}`def` is replaced by {keywordOf Lean.Parser.Command.declaration}`instance` and the name is optional:

:::syntax Lean.Parser.Command.instance

Most instances define each method using {keywordOf Lean.Parser.Command.declaration}`where` syntax:

```grammar
instance $[(priority := $p:prio)]? $name? $_ where
  $_*
```

However, type classes are inductive types, so instances can be constructed using any expression with an appropriate type:

```grammar
instance $[(priority := $p:prio)]? $_? $_ :=
  $_
```

Instances may also be defined by cases; however, this feature is rarely used outside of {name}`Decidable` instances:

```grammar
instance $[(priority := $p:prio)]? $_? $_
  $[| $_ => $_]*
```

:::



Elaboration of instances is almost identical to the elaboration of ordinary definitions, with the exception of the caveats documented below.
If no name is provided, then one is created automatically.
It is possible to refer to this generated name directly, but the algorithm used to generate the names has changed in the past and may change in the future.
It's better to explicitly name instances that will be referred to directly.
After elaboration, the new instance is registered as a candidate for instance search.
Adding the attribute {attr}`instance` to a name can be used to mark any other defined name as a candidate.

:::example "Instance Name Generation"

Following these declarations:
```lean
structure NatWrapper where
  val : Nat

instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y
```

the name {lean}`instBEqNatWrapper` refers to the new instance.
:::

## Recursive Instances
%%%
tag := "recursive-instances"
%%%

Functions defined in {keywordOf Lean.Parser.Command.declaration}`where` structure syntax are not recursive.
Furthermore, instances are not available for instance synthesis during their own definitions, which could be quite error-prone.
However, instances for recursive inductive types are common, and frequently necessary.
There are two standard ways to work around these challenges:
 1. Define a recursive function independently of the instance, and then refer to it in the instance definition.
    By convention, these recursive functions have the name of the corresponding method, but are defined in the datatype's namespace.
 2. Create a local instance in a recursively-defined function that includes a reference to the function being defined, taking advantage of the fact that instance synthesis considers every binding the local context as a candidate.


::: example "Instances are not recursive"
Given this definition of {lean}`NatTree`:
```lean
inductive NatTree where
  | leaf
  | branch (left : NatTree) (val : Nat) (right : NatTree)
```
the following {name}`BEq` instance fails:
```lean (error := true) (name := beqNatTreeFail)
instance : BEq NatTree where
  beq
    | .leaf, .leaf => true
    | .branch l1 v1 r1, .branch l2 v2 r2 => l1 == l2 && v1 == v2 && r1 == r2
    | _, _ => false
```
with errors in both the left and right recursive calls that read:
```leanOutput beqNatTreeFail
failed to synthesize
  BEq NatTree
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
Given a suitable recursive function, such as {lean}`NatTree.beq`:
```lean
def NatTree.beq : NatTree → NatTree → Bool
  | .leaf, .leaf => true
  | .branch l1 v1 r1, .branch l2 v2 r2 => l1 == l2 && v1 == v2 && r1 == r2
  | _, _ => false
```
the instance can be created in a second step:
```lean
instance : BEq NatTree where
  beq := NatTree.beq
```
or, equivalently, using anonymous constructor syntax:
```lean
instance : BEq NatTree := ⟨NatTree.beq⟩
```
:::

::: example "Instances for nested types"
Given this definition of {lean}`NatRoseTree` in which the type being defined occurs nested under another inductive type constructor:
```lean
inductive NatRoseTree where
  | node (val : Nat) (children : Array NatRoseTree)

```
defining instances may require appealing to existing instances.
However, instances are not typically available for instance synthesis during their own definitions, so the following definition fails:
```lean (error := true) (name := natRoseTreeBEqFail) (keep := false)
def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    val1 == val2 &&
    children1 == children2
```
```leanOutput natRoseTreeBEqFail
failed to synthesize
  BEq (Array NatRoseTree)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

Instances may be `let`-bound, allowing a recursively-defined function to be used in its own definition:

```lean
partial def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    let _ : BEq NatRoseTree := ⟨NatRoseTree.beq⟩
    val1 == val2 &&
    children1 == children2
```
The use of array equality on the children finds the recursively-defined instance during instance synthesis.
:::

## Instances of `class inductive`s
%%%
tag := "class-inductive-instances"
%%%

Many instances have function types: any instance that itself recursively invokes instance search is a function, as is any instance with implicit parameters.
Defining instances of class inductives typically means defining a function that pattern-matches one or more of its arguments, allowing it to select a constructor.
This is done using ordinary Lean function syntax.
If the function in question is recursive, then it will not be available for instance synthesis in its own definition.
::::keepEnv
:::example "An instance for a sum class"
```lean (show := false)
axiom α : Type
```
Because {lean}`DecidableEq α` is an abbreviation for {lean}`(a b : α) → Decidable (Eq a b)`, its arguments can be used directly, as in this example:

```lean
inductive ThreeChoices where
  | yes | no | maybe

instance : DecidableEq ThreeChoices
  | .yes, .yes => .isTrue rfl
  | .no, .no => .isTrue rfl
  | .maybe, .maybe => .isTrue rfl
  | .yes, .maybe | .yes, .no
  | .maybe, .yes | .maybe, .no
  | .no, .yes | .no, .maybe => .isFalse nofun

```

:::
::::

::::keepEnv
:::example "A recursive instance for a sum class"
Given this type of lists of strings:
```lean
inductive StringList where
  | nil
  | cons (hd : String) (tl : StringList)
```
a {name}`DecidableEq` instance is not automatically available for instance search in its own definition:
```lean (error := true) (name := stringListNoRec)
instance : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    if h : h1 = h2 then
      if h' : t1 = t2 then
        _
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
```leanOutput stringListNoRec
failed to synthesize
  Decidable (t1 = t2)
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
However, because it is an ordinary Lean function, it can recursively refer to its own explicit name:
```lean
instance instDecidableEqStringList : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    if h : h1 = h2 then
      if h' : instDecidableEqStringList t1 t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
:::
::::


## Instance Priorities


::: planned 62
This section will describe the specification of priorities, but not their function in the synthesis algorithm.
:::

Instances may be assigned {deftech}_priorities_.
During instance synthesis, higher-priority instances are preferred; see {TODO}[ref] for details of instance synthesis.

:::syntax prio open:=false
Priorities may be numeric:
```grammar
$n:num
```

If no priority is specified, the default priority that corresponds to {evalPrio}`default` is used:
```grammar
default
```

Three named priorities are available when numeric values are too fine-grained, corresponding to {evalPrio}`low`, {evalPrio}`mid`, and {evalPrio}`high` respectively.
The {keywordOf prioMid}`mid` priority is lower than {keywordOf prioDefault}`default`.
```grammar
low
```
```grammar
mid
```
```grammar
high
```

Finally, priorities can be added and subtracted, so `default + 2` is a valid priority, corresponding to {evalPrio}`default + 2`:
```grammar
($_)
```
```grammar
$_ + $_
```
```grammar
$_ - $_
```

:::

## The Instance Attribute

The {attr}`instance` attribute declares a name to be an instance, with the specified priority.
Like other attributes, {attr}`instance` can be applied globally, locally, or only when the current namespace is opened.
The {keywordOf Lean.Parser.Command.declaration}`instance` declaration is a form of definition that automatically applies the {attr}`instance` attribute.

:::syntax attr
```grammar
instance $p?
```
:::

{include 0 Manual.Language.Classes.InstanceSynth}

# Deriving Instances
%%%
tag := "deriving-instances"
%%%

::: planned 64
This section will specify syntax of `deriving` clauses and list the valid places where they may occur.
It will also describe `deriving instance`.
It will list the deriving handlers that ship with Lean by default.
:::


## Deriving Handlers

::: planned 65
This section will describe deriving handlers and how they are invoked.
:::
