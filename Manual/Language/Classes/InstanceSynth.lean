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

#doc (Manual) "Instance Synthesis" =>
%%%
tag := "instance-synth"
%%%

::: planned 63
This section will specify the instance synthesis algorithm.
:::

Instance synthesis is a recursive search procedure that either finds an instance for a given type class or fails.
In other words, given a type that is registered as a type class, instance synthesis attempts constructs a term with said type.
It respects {tech}[reducibility]: {tech}[semireducible] or {tech}[irreducible] definitions are not unfolded, so instances for a definition are not automatically treated as instances for its unfolding unless it is {tech}[reducible].
There may be multiple possible instances for a given class; in this case, declared priorities and order of declaration are used as tiebreakers, in that order, with more recent instances taking precedence over earlier ones with the same priority.

This search procedure is efficient in the presence of diamonds and does not loop indefinitely when there are cycles.
{deftech}_Diamonds_ occur when there is more than one route to a given goal, and {deftech}_cycles_ are situations when two instances each could be solved if the other were solved.
Diamonds occur regularly in practice when encoding mathematical concepts using type classes, and Lean's coercion feature {TODO}[link] naturally leads to cycles, e.g. between finite sets and finite multisets.

Instance synthesis can be tested using the {keywordOf Lean.Parser.Command.synth}`#synth` command.
:::syntax command
The {keywordOf Lean.Parser.Command.synth}`#synth` command attempts to synthesize an instance for the provided class.
If it succeeds, then the resulting term is output.
```grammar
#synth $t
```
:::

# Instance Search Problems

Instance search occurs during the elaboration of (potentially nullary) function applications.
Some of the implicit parameters' values are forced by others; for instance, an implicit type parameter may be solved using the type of a later value argument that is explicitly provided.
Implicit parameters may also be solved using information from the expected type at that point in the program.
The search for instance implicit arguments may make use of the implicit argument values that have been found, and may additionally solve others.

Instance implicit search begins with the type of the instance implicit parameter.
This type must be the application of a type class to zero or more arguments; these argument values may be known or unknown when search begins.
If an argument to a class is unknown, the search process will not instantiate it unless the corresponding parameter is {ref "class-output-parameters"}[marked as an output parameter], explicitly making it an output of the instance synthesis routine.

Search may succeed, fail, or get stuck; a stuck search may occur when an unknown argument value becoming known might enable progress to be made.
Stuck searches may be re-invoked when the elaborator has discovered one of the previously-unknown implicit arguments.
If this does not occur, stuck searches become failures.


# Candidate Instances

Instance synthesis uses both local and global instances in its search.
{deftech}_Local instances_ are those available in the local context; they may be either parameters to a function or locally defined with `let`. {TODO}[xref to docs for `let`]
Local instances do not need to be indicated specially; any local variable whose type is a type class is a candidate for instance search.
{deftech}_Global instances_ are those available in the global environment; every global instance is a defined name with the {attr}`instance` attribute applied.{margin}[{keywordOf Lean.Parser.Command.declaration}`instance` declarations automatically apply the {attr}`instance` attribute.]

::::keepEnv
:::example "Local Instances"
In this example, {lean}`addPairs` contains a locally-defined instance of {lean}`Add NatPair`:
```lean
structure NatPair where
  x : Nat
  y : Nat

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun ⟨x1, y1⟩ ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩⟩
  p1 + p2
```
The local instance is used to synthesize the instance used for the addition.
:::
::::

::::keepEnv
:::example "Local Instances Have Priority"
Here, {lean}`addPairs` contains a locally-defined instance of {lean}`Add NatPair`, even though there is a global instance:
```lean
structure NatPair where
  x : Nat
  y : Nat

instance : Add NatPair where
  add
    | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun _ _ => ⟨0, 0⟩⟩
  p1 + p2
```
The local instance is selected instead of the global one:
```lean (name:=addPairsOut)
#eval addPairs ⟨1, 2⟩ ⟨5, 2⟩
```
```leanOutput addPairsOut
{ x := 0, y := 0 }
```
:::
::::

# Instance Parameters and Synthesis

The search process for instances is largely governed by class parameters.
Type classes take a certain number of parameters, and instances are tried during the search when their choice of parameters is compatible with those in the class type for which the instance is being synthesized.
Here, classes can be seen as relations between types, and instances as governing which types are related.
An instance synthesis problem consists of instantiations of parameters to a class.

Parameters are not limited to classes.
Instances themselves may also take parameters, but the role of instances' parameters in instance synthesis is very different.
Instances' parameters represent either variables that may be instantiated by instance synthesis or further synthesis work to be done before the instance can be used.
In particular, parameters to instances may be explicit, implicit, or instance-implicit.
If they are instance implicit, then they induce further recursive instance searching, while explicit or implicit parameters must be solved by unification.

::::keepEnv
:::example "Implicit and Explicit Parameters to Instances"
While instances typically take parameters either implicitly or instance implicitly, explicit parameters may be filled out as if they were implicit during instance synthesis.
In this example, {name}`aNonemptySumInstance` is found by synthesis, applied explicitly to {lean}`Nat`, which is needed to make it type-correct.
```lean
instance aNonemptySumInstance (α : Type) {β : Type} [inst : Nonempty α] : Nonempty (α ⊕ β) :=
  let ⟨x⟩ := inst
  ⟨.inl x⟩
```

```lean (name := instSearch)
set_option pp.explicit true in
#synth Nonempty (Nat ⊕ Empty)
```
In the output, both the explicit argument {lean}`Nat` and the implicit argument {lean}`Empty` were found by unification with the search goal, while the {lean}`Nonempty Nat` instance was found via recursive instance synthesis.
```leanOutput instSearch
@aNonemptySumInstance Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
:::
::::

# Output Parameters
%%%
tag := "class-output-parameters"
%%%

By default, the parameters of a type class are considered to be _inputs_ to the search process.
If the parameters are not known, then the search process gets stuck, because choosing an instance would require the parameters to have values that match those in the instance.
In some cases, the choice of one parameter should cause an automatic choice of another; for example, the overloaded membership predicate type class {name}`Membership` treats the type of elements of a data structure as an output, so that the type of element can be determined by the type of data structure at a use site, instead of requiring that there be sufficient type annotations to determine both types prior to starting instance synthesis.

```signature (show := false)
-- Test the above claim
Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)
```

Type class parameters can be declared as outputs by wrapping their types in the {name}`outParam` {tech}[gadget].
When a class parameter is an output, instance synthesis will not require that it be known.
If it is unknown, and a candidate instance matches the input parameters, then that instance is selected; the instance's assignment of the output parameter becomes its value.
If it is known, then only instances that match the already-known value are considered.

{docstring outParam}


::::example "Output Parameters and Stuck Search"
:::keepEnv
This serialization framework provides a way to convert values to some underlying storage type:
```lean
class Serialize (input output : Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```

In this example, the output type is unknown.
```lean (error := true) (name := noOutputType)
example := ser (2, 3)
```
Instance synthesis can't select the {lean}`Serialize Nat String` instance, and thus the {lean}`Append String` instance, because that would require instantiating the output type as {lean}`String`, so the search gets stuck:
```leanOutput noOutputType
typeclass instance problem is stuck, it is often due to metavariables
  Serialize (Nat × Nat) ?m.16
```
One way to fix the problem is to supply an expected type:
```lean
example : String := ser (2, 3)
```
:::
:::keepEnv
The other is to make the output type into an output parameter:
```lean
class Serialize (input : Type) (output : outParam Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```
Now, instance synthesis is free to select the {lean}`Serialize Nat String` instance, which solves the unknown implicit `output` parameter of {name}`ser`:
```lean
example := ser (2, 3)
```
:::
::::

{docstring semiOutParam}


# "Morally Canonical" Instances

# Options

{optionDocs synthInstance.maxHeartbeats}

{optionDocs synthInstance.maxSize}

{optionDocs backward.synthInstance.canonInstances}
