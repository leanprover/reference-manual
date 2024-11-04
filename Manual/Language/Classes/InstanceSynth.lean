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

def tabledRes : ArXiv where
  title := .concat (inlines!"Tabled typeclass resolution")
  authors := #[.concat (inlines!"Daniel Selsam"), .concat (inlines!"Sebastian Ullrich"), .concat (inlines!"Leonardo de Moura")]
  year := 2020
  id := "2001.04301"

#doc (Manual) "Instance Synthesis" =>
%%%
tag := "instance-synth"
%%%


Instance synthesis is a recursive search procedure that either finds an instance for a given type class or fails.
In other words, given a type that is registered as a type class, instance synthesis attempts constructs a term with said type.
It respects {tech}[reducibility]: {tech}[semi-reducible] or {tech}[irreducible] definitions are not unfolded, so instances for a definition are not automatically treated as instances for its unfolding unless it is {tech}[reducible].
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

Additionally, {name}`inferInstance` and {name}`inferInstanceAs` can be used to synthesize an instance in a position where the instance itself is needed.

{docstring inferInstance}

{docstring inferInstanceAs}

# Instance Search Summary

Generally speaking, instance synthesis is a recursive search procedure that may, in general, backtrack arbitrarily.
Synthesis may _succeed_ with an instance term, _fail_ if no such term can be found, or get _stuck_ if there is insufficient information.
A detailed description of the instance synthesis algorithm is available in {citet tabledRes}[].
An instance search problem is given by a type class applied to concrete arguments; these argument values may or may not be known.
Instance search attempts every locally-bound variable whose type is a class, as well as each registered instance, in order of priority and definition.
When candidate instances themselves have instance-implicit parameters, they impose further synthesis tasks.

A problem is only attempted when all of the input parameters to the type class are known.
When a problem cannot yet be attempted, then that branch is stuck; progress in other subproblems may result in the problem becoming solvable.
Output or semi-output parameters may be either known or unknown at the start of instance search.
Output parameters are ignored when checking whether an instance matches the problem, while semi-output parameters are considered.

Every candidate solution for a given problem is saved in a table; this prevents infinite regress in case of cycles as well as exponential search overheads in the presence of diamonds (that is, multiple paths by which the same goal can be achieved).
A branch of the search fails when any of the following occur:
 * All potential instances have been attempted, and the search space is exhausted.
 * The instance size limit specified by the option {option}`synthInstance.maxSize` is reached.
 * The synthesized value of an output parameter does not match the specified value in the search problem.
Failed branches are not retried.

If search would otherwise fail or get stuck, the search process attempts to use matching {tech}[default instances] in order of priority.
For default instances, the input parameters do not need to be fully known, and may be instantiated by the instances parameter values.
Default instances may take instance-implicit parameters, which induce further recursive search.

Successful branches in which the problem is fully known (that is, in which there are no unsolved metavariables) are pruned, and further potentially-successful instances are not attempted, because no later instance could cause the previously-succeeding branch to fail.

# Instance Search Problems

Instance search occurs during the elaboration of (potentially nullary) function applications.
Some of the implicit parameters' values are forced by others; for instance, an implicit type parameter may be solved using the type of a later value argument that is explicitly provided.
Implicit parameters may also be solved using information from the expected type at that point in the program.
The search for instance implicit arguments may make use of the implicit argument values that have been found, and may additionally solve others.

Instance synthesis begins with the type of the instance-implicit parameter.
This type must be the application of a type class to zero or more arguments; these argument values may be known or unknown when search begins.
If an argument to a class is unknown, the search process will not instantiate it unless the corresponding parameter is {ref "class-output-parameters"}[marked as an output parameter], explicitly making it an output of the instance synthesis routine.

Search may succeed, fail, or get stuck; a stuck search may occur when an unknown argument value becoming known might enable progress to be made.
Stuck searches may be re-invoked when the elaborator has discovered one of the previously-unknown implicit arguments.
If this does not occur, stuck searches become failures.


# Candidate Instances

Instance synthesis uses both local and global instances in its search.
{deftech}_Local instances_ are those available in the local context; they may be either parameters to a function or locally defined with `let`. {TODO}[xref to docs for `let`]
Local instances do not need to be indicated specially; any local variable whose type is a type class is a candidate for instance synthesis.
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
The local instance is used for the addition, having been found by instance synthesis.
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
%%%
tag := "instance-synth-parameters"
%%%

The search process for instances is largely governed by class parameters.
Type classes take a certain number of parameters, and instances are tried during the search when their choice of parameters is _compatible_ with those in the class type for which the instance is being synthesized.

Instances themselves may also take parameters, but the role of instances' parameters in instance synthesis is very different.
Instances' parameters represent either variables that may be instantiated by instance synthesis or further synthesis work to be done before the instance can be used.
In particular, parameters to instances may be explicit, implicit, or instance-implicit.
If they are instance implicit, then they induce further recursive instance searching, while explicit or implicit parameters must be solved by unification.

::::keepEnv
:::example "Implicit and Explicit Parameters to Instances"
While instances typically take parameters either implicitly or instance-implicitly, explicit parameters may be filled out as if they were implicit during instance synthesis.
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
If the parameters are not known, then the search process gets stuck, because choosing an instance would require the parameters to have values that match those in the instance, which cannot be determined on the basis of incomplete information.
In most cases, guessing instances would make instance synthesis unpredictable.

In some cases, however, the choice of one parameter should cause an automatic choice of another.
For example, the overloaded membership predicate type class {name}`Membership` treats the type of elements of a data structure as an output, so that the type of element can be determined by the type of data structure at a use site, instead of requiring that there be sufficient type annotations to determine _both_ types prior to starting instance synthesis.
An element of a {lean}`List Nat` can be concluded to be a {lean}`Nat` simply on the basis of its membership in the list.

```signature (show := false)
-- Test the above claim
Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)
```

Type class parameters can be declared as outputs by wrapping their types in the {name}`outParam` {tech}[gadget].
When a class parameter is an output, instance synthesis will not require that it be known; in fact, any existing value is ignored completely.
The first instance that matches the input parameters is selected, and that instance's assignment of the output parameter becomes its value.
If there was a pre-existing value, then it is compared with the assignment after synthesis is complete, and it is an error if they do not match.

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

::::keepEnv
:::example "Output Parameters with Pre-Existing Values"
The class {name}`OneSmaller` represents a way to transform non-maximal elements of a type into elements of a type that has one fewer elements.
There are two separate instances that can match an input type {lean}`Option Bool`, with different outputs:
```lean
class OneSmaller (α : Type) (β : outParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```
Because instance synthesis selects the most recently defined instance, the following code is an error:
```lean (error := true) (name := nosmaller)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller
failed to synthesize
  OneSmaller (Option Bool) Bool
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
The {lean}`OneSmaller (Option Bool) (Option Unit)` instance was selected during instance synthesis, without regard to the supplied value of `β`.
:::
::::

Semi-output parameters are like output parameters in that they are not required to be known prior to synthesis commencing; unlike output parameters, their values are taken into account when selecting instances.

{docstring semiOutParam}

Semi-output parameters impose a requirement on instances: each instance of a class with semi-output parameters should determine the values of its semi-output parameters.
:::TODO
What goes wrong if they can't?
:::

::::keepEnv
:::example "Semi-Output Parameters with Pre-Existing Values"
The class {name}`OneSmaller` represents a way to transform non-maximal elements of a type into elements of a type that one fewer elements.
It has two separate instances that can match an input type {lean}`Option Bool`, with different outputs:
```lean
class OneSmaller (α : Type) (β : semiOutParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```

Because instance synthesis takes semi-output parameters into account when selecting instances, the {lean}`OneSmaller (Option Bool) (Option Unit)` instance is passed over due to the supplied value for `β`:
```lean (name := nosmaller2)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller2
OneSmaller.shrink (some false) ⋯ : Bool
```
:::
::::

# Default Instances
%%%
tag := "default-instance-synth"
%%%

When instance synthesis would otherwise fail, having not selected an instance, the {deftech}_default instances_ specified using the {attr}`default_instance` attribute are attempted in order of priority.
When priorities are equal, more recently-defined default instances are chosen before earlier ones.
The first default instance that causes the search to succeed is chosen.

Default instances may induce further recursive instance search if the default instances themselves have instance-implicit parameters.
If the recursive search fails, the search process backtracks and the next default instance is tried.

# “Morally Canonical” Instances

During instance synthesis, if a goal is fully known (that is, contains no metavariables) and search succeeds, no further instances will be attempted for that same goal.
In other words, when search succeeds for a goal in a way that can't be refuted by a subsequent increase in information, the goal will not be attempted again, even if there are other instances that could potentially have been used.
This optimization can prevent a failure in a later branch of an instance synthesis search from causing spurious backtracking that replaces a fast solution from an earlier branch with a slow exploration of a large state space.

The optimization relies on the assumption that instances are {deftech}_morally canonical_.
Even if there is more than one potential implementation of a given type class's overloaded operations, or more than one way to synthesize an instance due to diamonds, _any discovered instance should be considered as good as any other_.
In other words, there's no need to consider _all_ potential instances so long as one of them has been guaranteed to work.
The optimization may be disabled with the backwards-compatibility option {option}`backward.synthInstance.canonInstances`, which may be removed in a future version of Lean.

Code that uses instance-implicit parameters should be prepared to consider all instances as equivalent.
In other words, it should be robust in the face of differences in synthesized instances.
When the code relies on instances _in fact_ being equivalent, it should either explicitly manipulate instances (e.g. via local definitions, by saving them in structure fields, or having a structure inherit from the appropriate class) or it should make this dependency explicit in the type, so that different choices of instance lead to incompatible types.

# Options

{optionDocs backward.synthInstance.canonInstances}

{optionDocs synthInstance.maxHeartbeats}

{optionDocs synthInstance.maxSize}
