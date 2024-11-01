/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual

#doc (Manual) "Instance Declarations" =>
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

Instances defined with explicit terms often consist of either anonymous constructors ({keywordOf Lean.Parser.Term.anonymousCtor}`⟨...⟩`) wrapping method implementations or of invocations of {name}`inferInstanceAs` on definitionally equal types.

Elaboration of instances is almost identical to the elaboration of ordinary definitions, with the exception of the caveats documented below.
If no name is provided, then one is created automatically.
It is possible to refer to this generated name directly, but the algorithm used to generate the names has changed in the past and may change in the future.
It's better to explicitly name instances that will be referred to directly.
After elaboration, the new instance is registered as a candidate for instance search.
Adding the attribute {attr}`instance` to a name can be used to mark any other defined name as a candidate.

::::keepEnv
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
::::

::::keepEnv
:::example "Variations in Instance Definitions"

Given this structure type:
```lean
structure NatWrapper where
  val : Nat
```
all of the following ways of defining a {name}`BEq` instance are equivalent:
```lean
instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```

Aside from introducing different names into the environment, the following are also equivalent:
```lean
@[instance]
def instBeqNatWrapper : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```
:::
::::

# Recursive Instances
%%%
tag := "recursive-instances"
%%%

Functions defined in {keywordOf Lean.Parser.Command.declaration}`where` structure definition syntax are not recursive.
Because instance declaration is a version of structure definition, type class methods are also not recursive by default.
Instances for recursive inductive types are common, however.
There is a standard idiom to work around this limitation: define a recursive function independently of the instance, and then refer to it in the instance definition.
By convention, these recursive functions have the name of the corresponding method, but are defined in the datatype's namespace.

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

Furthermore, instances are not available for instance synthesis during their own definitions.
They are first marked as being available for instance synthesis after they are defined.
Nested inductive types, in which the recursive occurrence of the type occurs as a parameter to some other inductive type, may require an instance to be available to write even the recursive function.
The standard idiom to work around this limitation is to create a local instance in a recursively-defined function that includes a reference to the function being defined, taking advantage of the fact that instance synthesis may use every binding in the local context with the right type.


::: example "Instances for nested types"
In this definition of {lean}`NatRoseTree`, the type being defined occurs nested under another inductive type constructor ({name}`Array`):
```lean
inductive NatRoseTree where
  | node (val : Nat) (children : Array NatRoseTree)

```
Checking the equality of rose trees requires checking equality of of arrays.
However, instances are not typically available for instance synthesis during their own definitions, so the following definition fails, even though {lean}`NatRoseTree.beq` is a recursive function and is in scope in its own definition.
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

To solve this, a local {lean}`BEq NatRoseTree` instance may be `let`-bound:

```lean
partial def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    let _ : BEq NatRoseTree := ⟨NatRoseTree.beq⟩
    val1 == val2 &&
    children1 == children2
```
The use of array equality on the children finds the let-bound instance during instance synthesis.
:::

# Instances of `class inductive`s
%%%
tag := "class-inductive-instances"
%%%

Many instances have function types: any instance that itself recursively invokes instance search is a function, as is any instance with implicit parameters.
While most instances only project method implementations from their own instance parameters, instances of class inductives typically pattern-match one or more of their arguments, allowing the instance to select the appropriate constructor.
This is done using ordinary Lean function syntax.
Just as with other instances, the function in question is not available for instance synthesis in its own definition.
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
  | .yes,   .yes   =>
    .isTrue rfl
  | .no,    .no    =>
    .isTrue rfl
  | .maybe, .maybe =>
    .isTrue rfl
  | .yes,   .maybe | .yes,   .no
  | .maybe, .yes   | .maybe, .no
  | .no,    .yes   | .no,    .maybe =>
    .isFalse nofun

```

:::
::::

::::keepEnv
:::example "A recursive instance for a sum class"
The type {lean}`StringList` represents monomorphic lists of strings:
```lean
inductive StringList where
  | nil
  | cons (hd : String) (tl : StringList)
```
In the following attempt at defining a {name}`DecidableEq` instance, instance synthesis invoked while elaborating the inner {keywordOf termIfThenElse}`if` fails because the instance is not available for instance synthesis in its own definition:
```lean (error := true) (name := stringListNoRec) (keep := false)
instance : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    if h : h1 = h2 then
      if h' : t1 = t2 then
        .isTrue (by simp [*])
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
However, because it is an ordinary Lean function, it can recursively refer to its own explicitly-provided name:
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


# Instance Priorities
%%%
tag := "instance-priorities"
%%%

Instances may be assigned {deftech}_priorities_.
During instance synthesis, higher-priority instances are preferred; see {ref "instance-synth"}[the section on instance synthesis] for details of instance synthesis.

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

# Default Instances
%%%
tag := "default-instances"
%%%

The {attr}`default_instance` attribute specifies that an instance {ref "default-instance-synth"}[should be used as a fallback in situations where there is not enough information to select it otherwise].
If no priority is specified, then the default priority `default` is used.

:::syntax attr
```grammar
default_instance $p?
```
:::

:::::keepEnv
::::example "Default Instances"
A default instance of {lean}`OfNat Nat` is used to select {lean}`Nat` for natural number literals in the absence of other type information.
It is declared in the Lean standard library with priority 100.
Given this representation of even numbers, in which an even number is represented by half of it:
```lean
structure Even where
  half : Nat
```

the following instances allow numeric literals to be used for small {lean}`Even` values (a limit on the depth of type class instance search prevents them from being used for arbitrarily large literals):
```lean (name := insts)
instance ofNatEven0 : OfNat Even 0 where
  ofNat := ⟨0⟩

instance ofNatEvenPlusTwo [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := ⟨(OfNat.ofNat n : Even).half + 1⟩

#eval (0 : Even)
#eval (34 : Even)
#eval (254 : Even)
```
```leanOutput insts
{ half := 0 }
```
```leanOutput insts
{ half := 17 }
```
```leanOutput insts
{ half := 127 }
```

Specifying them as default instances with a priority greater than or equal to 100 causes them to be used instead of {lean}`Nat`:
```lean
attribute [default_instance 100] ofNatEven0
attribute [default_instance 100] ofNatEvenPlusTwo
```
```lean (name := withDefaults)
#eval 0
#eval 34
```
```leanOutput withDefaults
{ half := 0 }
```
```leanOutput withDefaults
{ half := 17 }
```

Non-even numerals still use the {lean}`OfNat Nat` instance:
```lean (name := stillNat)
#eval 5
```
```leanOutput stillNat
5
```
::::
:::::

# The Instance Attribute
%%%
tag := "instance-attribute"
%%%

The {attr}`instance` attribute declares a name to be an instance, with the specified priority.
Like other attributes, {attr}`instance` can be applied globally, locally, or only when the current namespace is opened.
The {keywordOf Lean.Parser.Command.declaration}`instance` declaration is a form of definition that automatically applies the {attr}`instance` attribute.

:::syntax attr

Declares the definition to which it is applied to be an instance.
If no priority is provided, then the default priority `default` is used.

```grammar
instance $p?
```


:::
