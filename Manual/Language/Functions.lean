/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

#doc (Manual) "Functions" =>
%%%
tag := "functions"
%%%


Function types are a built-in feature of Lean.
{deftech}[Functions] map the values of one type (the {deftech}_domain_) into those of another type (the {deftech}_range_), and {deftech}_function types_ specify the domain and range of functions.

There are two kinds of function type:

 : {deftech}[Dependent]

   Dependent function types explicitly name the parameter, and the function's range may refer explicitly to this name.
   Because types can be computed from values, a dependent function may return values from any number of different types, depending on its argument.{margin}[Dependent functions are sometimes referred to as {deftech}_dependent products_, because they correspond to an indexed product of sets.]

 : {deftech}[Non-Dependent]

   Non-dependent function types do not include a name for the parameter, and the range does not vary based on the specific argument provided.


::::keepEnv
:::example "Dependent Function Types"

The function {lean}`two` returns values in different types, depending on which argument it is called with:

```lean
def two : (b : Bool) → if b then Unit × Unit else String :=
  fun b =>
    match b with
    | true => ((), ())
    | false => "two"
```

The body of the function cannot be written with `if...then...else...` because it does not refine types the same way that {keywordOf Lean.Parser.Term.match}`match` does.
:::
::::

In Lean's core language, all function types are dependent: non-dependent function types are dependent function types in which the parameter name does not occur in the range.
Additionally, two dependent function types that have different parameter names may be definitionally equal if renaming the parameter makes them equal.
However, the Lean elaborator does not introduce a local binding for non-dependent functions' parameters.

:::example "Definitional Equality of Dependent and Non-Dependent Functions"
The types {lean}`(x : Nat) → String` and {lean}`Nat → String` are definitionally equal:
```lean
example : ((x : Nat) → String) = (Nat → String) := rfl
```
Similarly, the types {lean}`(n : Nat) → n + 1 = 1 + n` and {lean}`(k : Nat) → k + 1 = 1 + k` are definitionally equal:
```lean
example : ((n : Nat) → n + 1 = 1 + n) = ((k : Nat) → k + 1 = 1 + k) := rfl
```
:::

:::::keepEnv
::::example "Non-Dependent Functions Don't Bind Variables"

:::keepEnv
A dependent function is required in the following statement that all elements of an array are non-zero:
```lean
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (lt : i < xs.size) → xs[i] ≠ 0
```
:::

:::keepEnv
This is because the elaborator for array access requires a proof that the index is in bounds.
The non-dependent version of the statement does not introduce this assumption:
```lean (error := true) (name := nondepOops)
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (i < xs.size) → xs[i] ≠ 0
```
```leanOutput nondepOops
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array Nat
i : Nat
⊢ i < xs.size
```
:::
::::
:::::

While the core type theory does not feature {tech}[implicit] parameters, function types do include an indication of whether the parameter is implicit.
This information is used by the Lean elaborator, but it does not affect type checking or definitional equality in the core theory and can be ignored when thinking only about the core type theory.

:::example "Definitional Equality of Implicit and Explicit Function Types"
The types {lean}`{α : Type} → (x : α) → α` and {lean}`(α : Type) → (x : α) → α` are definitionally equal, even though the first parameter is implicit in one and explicit in the other.
```lean
example :
    ({α : Type} → (x : α) → α)
    =
    ((α : Type) → (x : α) → α)
  := rfl
```

:::

# Function Abstractions

In Lean's type theory, functions are created using {deftech}_function abstractions_ that bind a variable.
{margin}[In various communities, function abstractions are also known as _lambdas_, due to Alonzo Church's notation for them, or _anonymous functions_ because they don't need to be defined with a name in the global environment.]
When the function is applied, the result is found by {tech key:="β"}[β-reduction]: substituting the argument for the bound variable.
In compiled code, this happens strictly: the argument must already be a value.
When type checking, there are no such restrictions; the equational theory of definitional equality allows β-reduction with any term.

In Lean's {ref "function-terms"}[term language], function abstractions may take multiple parameters or use pattern matching.
These features are translated to simpler operations in the core language, where all functions abstractions take exactly one parameter.
Not all functions originate from abstractions: {tech}[type constructors], {tech}[constructors], and {tech}[recursors] may have function types, but they cannot be defined using function abstractions alone.


# Currying
%%%
tag := "currying"
%%%


In Lean's core type theory, every function maps each element of the domain to a single element of the range.
In other words, every function expects exactly one parameter.
Multiple-parameter functions are implemented by defining higher-order functions that, when supplied with the first parameter, return a new function that expects the remaining parameters.
This encoding is called {deftech}_currying_, popularized by and named after Haskell B. Curry.
Lean's syntax for defining functions, specifying their types, and applying them creates the illusion of multiple-parameter functions, but the result of elaboration contains only single-parameter functions.



# Extensionality
%%%
tag := "function-extensionality"
%%%


Definitional equality of functions in Lean is {deftech}_intensional_.
This means that definitional equality is defined _syntactically_, modulo renaming of bound variables and {tech}[reduction].
To a first approximation, this means that two functions are definitionally equal if they implement the same algorithm, rather than the usual mathematical notion of equality that states that two functions are equal if they map equal elements of the domain to equal elements of the range.


Definitional equality is used by the type checker, so it's important that it be predictable.
The syntactic character of intensional equality means that the algorithm to check it can be feasibly specified.
Checking extensional equality involves proving essentially arbitrary theorems about equality of functions, and there is no clear specification for an algorithm to check it.
This makes extensional equality a poor choice for a type checker.
Function extensionality is instead made available as a reasoning principle that can be invoked when proving the {tech}[proposition] that two functions are equal.


::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : α → Type
axiom f : (x : α) → β x

-- test claims in next para
example : (fun x => f x) = f := by rfl
```

In addition to reduction and renaming of bound variables, definitional equality does support one limited form of extensionality, called {deftech}_η-equivalence_, in which functions are equal to abstractions whose bodies apply them to the argument.
Given {lean}`f` with type {lean}`(x : α) → β x`, {lean}`f` is definitionally equal to {lean}`fun x => f x`.
::::

When reasoning about functions, the theorem {lean}`funext`{margin}[Unlike some intensional type theories, {lean}`funext` is a theorem in Lean. It can be proved using {tech}[quotient] types.] or the corresponding tactics {tactic}`funext` or {tactic}`ext` can be used to prove that two functions are equal if they map equal inputs to equal outputs.

{docstring funext}

# Totality and Termination
%%%
tag := "totality"
%%%


Functions can be defined recursively using {keywordOf Lean.Parser.Command.declaration}`def`.
From the perspective of Lean's logic, all functions are {deftech}_total_, meaning that they map each element of the domain to an element of the range in finite time.{margin}[Some programming language communities use the term _total_ in a different sense, where functions are considered total if they do not crash due to unhandled cases but non-termination is ignored.]
The values of total functions are defined for all type-correct arguments, and they cannot fail to terminate or crash due to a missing case in a pattern match.

While the logical model of Lean considers all functions to be total, Lean is also a practical programming language that provides certain "escape hatches".
Functions that have not been proven to terminate can still be used in Lean's logic as long as their range is proven nonempty.
These functions are treated as uninterpreted functions by Lean's logic, and their computational behavior is ignored.
In compiled code, these functions are treated just like any others.
Other functions may be marked unsafe; these functions are not available to Lean's logic at all.
The section on {ref "partial-unsafe"}[partial and unsafe function definitions] contains more detail on programming with recursive functions.

Similarly, operations that should fail at runtime in compiled code, such as out-of-bounds access to an array, can only be used when the resulting type is known to be inhabited.
These operations result in an arbitrarily chosen inhabitant of the type in Lean's logic (specifically, the one specified in the type's {name}`Inhabited` instance).

:::example "Panic"
The function {name}`thirdChar` extracts the third element of an array, or panics if the array has two or fewer elements:
```lean
def thirdChar (xs : Array Char) : Char := xs[2]!
```
The (nonexistent) third elements of {lean}`#['!']` and {lean}`#['-', 'x']` are equal, because they result in the same arbitrarily-chosen character:
```lean
example : thirdChar #['!'] = thirdChar #['-', 'x'] := rfl
```
Indeed, both are equal to {lean}`'A'`, which happens to be the default fallback for {lean}`Char`:
```lean
example : thirdChar #['!'] = 'A' := rfl
example : thirdChar #['-', 'x'] = 'A' := rfl
```
:::
