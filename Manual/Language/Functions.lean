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

:::syntax term title:="Function types"
Dependent function types include an explicit name:
```grammar
($x:ident : $t) → $t2
```

Non-dependent function types do not:
```grammar
$t1:term → $t2
```
:::

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

:::example "Equivalence of Dependent and Non-Dependent Functions"
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

# Functions
%%%
tag := "function-terms"
%%%


Terms with function types can be created via abstractions, introduced with the {keywordOf Lean.Parser.Term.fun}`fun` keyword.

:::syntax term title:="Function Abstraction"
The most basic function abstraction introduces a variable to stand for the function's parameter:

```grammar
fun $x:ident => $t
```

At elaboration time, Lean must be able to determine the function's domain.
A type ascription is one way to provide this information:

```grammar
fun $x:ident : term => $t
```
:::

Function definitions defined with keywords such as {keywordOf Lean.Parser.Command.declaration parser:=Lean.Parser.Command.definition}`def` desugar to {keywordOf Lean.Parser.Term.fun}`fun`.
However, not all functions originate from abstractions: {tech}[type constructors], {tech}[constructors], and {tech}[recursors] may have function types, but they cannot be defined using function abstractions alone.

# Currying
%%%
tag := "currying"
%%%


In Lean's core type theory, every function maps each element of the domain to a single element of the range.
In other words, every function expects exactly one parameter.
Multiple-parameter functions are implemented by defining higher-order functions that, when supplied with the first parameter, return a new function that expects the remaining parameters.
This encoding is called {deftech}_currying_, popularized by and named after Haskell B. Curry.
Lean's syntax for defining functions, specifying their types, and applying them creates the illusion of multiple-parameter functions, but the result of elaboration contains only single-parameter functions.

:::syntax term title:="Curried Functions"

Dependent Function types may include multiple parameters that have the same type in a single set of parentheses:
```grammar
($x:ident* : $t) → $t
```
This is equivalent to repeating the type annotation for each parameter name in a nested function type.

Multiple parameter names are accepted after after {keywordOf Lean.Parser.Term.fun}`fun`:
```grammar
fun $x:ident* => $t
```

```grammar
fun $x:ident* : $t:term => $t
```

These are equivalent to writing nested {keywordOf Lean.Parser.Term.fun}`fun` terms.
:::


# Implicit Functions
%%%
tag := "implicit-functions"
%%%


Lean supports implicit parameters to functions.
This means that Lean itself can supply arguments to functions, rather than requiring users to supply all needed arguments.
Implicit parameters come in three varieties:

  : Ordinary implicit parameters

    Ordinary implicit parameters are function parameters that Lean should determine values for via unification.
    In other words, each call site should have exactly one potential argument value that would cause the function call as a whole to be well-typed.
    The Lean elaborator attempts to find values for all implicit arguments at each occurrence of a function.
    Ordinary implicit parameters are written in curly braces (`{` and `}`).

  : Strict implicit parameters

    Strict implicit parameters are identical to ordinary implicit parameters, except Lean will only attempt to find argument values when subsequent explicit arguments are provided at a call site.
    Strict implicit parameters are written in double curly braces (`⦃` and `⦄`, or `{{` and `}}`).

  : Instance implicit parameters

    Arguments for instance implicit parameters are found via {ref "instance-synth"}[type class synthesis].
    Instance implicit parameters are written in square brackets (`[` and `]`), and in most cases omit the parameter name because instances synthesized as parameters to functions are already available in the functions' bodies, even without being named explicitly.

::::keepEnv
:::example "Ordinary vs Strict Implicit Parameters"
The difference between the functions {lean}`f` and {lean}`g` is that `α` is strictly implicit in {lean}`f`:
```lean
def f ⦃α : Type⦄ : α → α := fun x => x
def g {α : Type} : α → α := fun x => x
```

These functions are elaborated identically when applied to concrete arguments:
```lean
example : f 2 = g 2 := rfl
```

However, when the explicit argument is not provided, uses of {lean}`f` do not require the implicit `α` to be solved:
```lean
example := f
```
However, uses of `g` do require it to be solved, and fail to elaborate if there is insufficient information available:
```lean (error := true) (name := noAlpha)
example := g
```
```leanOutput noAlpha
don't know how to synthesize implicit argument 'α'
  @g ?m.6
context:
⊢ Type
```
:::
::::


:::syntax term title := "Functions with Varying Binders"
The most general syntax for {keywordOf Lean.Parser.Term.fun}`fun` accepts a sequence of binders:
```grammar
fun $p:funBinder* => $t
```
:::


:::syntax Lean.Parser.Term.funBinder title:="Function Binders"
Function binders may be identifiers:
```grammar
$x:ident
```
sequences of identifiers with a type ascription:
```grammar
($x:ident $y:ident* : $t)
```
implicit parameters, with or without a type ascription:
```grammar
{$x:ident*}
```
```grammar
{$x:ident* : $t}
```
instance implicits, anonymous or named:
```grammar
[$t]
```
```grammar
[$x:ident : $t]
```
or strict implicit parameters, with or without a type ascription:
```grammar
⦃$t⦄
```
```grammar
⦃$x:ident* : $t⦄
```
:::


Lean's core language does not distinguish between implicit, instance, and explicit parameters: the various kinds of function and function type are definitionally equal.
The differences can be observed only during elaboration.

```lean (show := false)
-- Evidence of claims in next paragraph
example : ({x : Nat} → Nat) = (Nat → Nat) := rfl
example : (fun {x} => 2 : {x : Nat} → Nat) = (fun x => 2 : Nat → Nat) := rfl
example : ([x : Repr Nat] → Nat) = (Repr Nat → Nat) := rfl
example : (⦃x : Nat⦄ → Nat) = (Nat → Nat) := rfl
```

# Pattern Matching

:::syntax term
Functions may be specified via pattern matching by writing a sequence of patterns after {keywordOf Lean.Parser.Term.fun}`fun`, each preceded by a vertical bar (`|`).
```grammar
fun
  $[| $pat,* => $term]*
```
This desugars to a function that immediately pattern-matches on its arguments.
:::

::::keepEnv
:::example "Pattern-Matching Functions"
{lean}`isZero` is defined using a pattern-matching function abstraction, while {lean}`isZero'` is defined using a pattern match expression:
```lean
def isZero : Nat → Bool :=
  fun
    | 0 => true
    | _ => false

def isZero' : Nat → Bool :=
  fun n =>
    match n with
    | 0 => true
    | _ => false
```
Because the former is syntactic sugar for the latter, they are definitionally equal:
```lean
example : isZero = isZero' := rfl
```
The desugaring is visible in the output of {keywordOf Lean.Parser.Command.print}`#print`:
```lean (name := isZero)
#print isZero
```
outputs
```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
while
```lean (name := isZero')
#print isZero'
```
outputs
```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
:::
::::

# Extensionality
%%%
tag := "function-extensionality"
%%%


Definitional equality of functions in Lean is {deftech}_intensional_.
This means that definitional equality is defined _syntactically_, modulo renaming of bound variables and {tech}[reduction].
To a first approximation, this means that two functions are definitionally equal if they implement the same algorithm, rather than the usual mathematical notion of equality that states that two functions are equal if they map equal elements of the domain to equal elements of the range.

Intensional equality is mechanically decidable; Lean's type checker can decide whether two functions are intensionally equal.
Extensional equality is not decidable, so it is instead made available as a reasoning principle when proving the {tech}[proposition] that two functions are equal.

::::keepEnv
```lean (show := false)
axiom α : Type
axiom β : α → Type
axiom f : (x : α) → β x

-- test claims in next para
example : (fun x => f x) = f := by rfl
```

In addition to reduction and renaming of bound variables, definitional equality does support one limited form of extensionality, called {deftech}_η-equivalence_, in which functions are equal to abstractions whose bodies apply them to the argument.
Given {lean}`f` with type {lean}`(x : α) → β x`, {lean}`f` is definitionally equal to {lean}`fun x => f x`
::::

When reasoning about functions, the theorem {lean}`funext`{margin}[Unlike some intensional type theories, {lean}`funext` is a theorem in Lean. It can be proved using {tech}[quotient] types.] or the corresponding tactics {tactic}`funext` or {tactic}`ext` can be used to prove that two functions are equal if they map equal inputs to equal outputs.

{docstring funext}

# Totality and Termination
%%%
tag := "totality"
%%%


Functions can be defined recursively using {keywordOf Lean.Parser.Command.declaration}`def`.
From the perspective of Lean's logic, all functions are {deftech}_total_, meaning that they map each element of the domain to an element of the range in finite time.{margin}[Some programming language communities use the term _total_ in a more restricted sense, where functions are considered total if they do not crash but non-termination is ignored.]
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
