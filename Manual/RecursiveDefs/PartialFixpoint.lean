/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Meta.Monotonicity

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

set_option maxRecDepth 600

#doc (Manual) "Partial Fixpoint Recursion" =>
%%%
tag := "partial-fixpoint"
%%%

All definitions are fundamentally equations: the new constant being defined is equal to the right-hand side of the definition.
For functions defined by {ref "structural-recursion"}[structural recursion], this equation holds {tech key:="definitional equality"}[definitionally], and there is a unique value returned by application of the function.
For functions defined by {ref "well-founded-recursion"}[well-founded recursion], the equation may hold only {tech key:="proposition"}[propositionally], but all type-correct applications of the function to arguments are equal to the respective values prescribed by the definition.
In both cases, the fact that the function terminates for all inputs means that the value computed by applying the function is always uniquely determined.


In some cases where a function does not terminate for all arguments, the equation may not _uniquely_ determine the function's return value for each input, but there are nonetheless functions for which the defining equation holds.
In these cases, a definition as a {deftech}_partial fixpoint_ may still be possible.
Any function that satisfies the defining equation can be used to demonstrate that the equation does not create a logical contradiction, and the equation can then be proven as a theorem about this function.
As with the other strategies for defining recursive functions, compiled code uses the function as it was originally written; like definitions in terms of eliminators or recursion over accessibility proofs, the function used to define the partial fixpoint is used only to justify the function's equations in Lean's logic for purposes of mathematical reasoning.

The term {tech}_partial fixpoint_ is specific to Lean.
Functions declared {keywordOf Lean.Parser.Command.declaration}`partial` do not require termination proofs, so long as the type of their return values is inhabited, but they are completely opaque from the perspective of Lean's logic.
Partial fixpoints, on the other hand, can be rewritten using their defining equations while writing proofs.
Logically speaking, partial fixpoints are total functions that don't reduce {tech key:="definitional equality"}[definitionally] when applied, but for which equational rewrite rule are provided.
They are _partial_ in the sense that the defining equation does not necessarily specify a value for all possible arguments.


While partial fixpoints do allow functions to be defined that cannot be expressed using structural or well-founded recursion, the technique is also useful in other cases.
Even in cases where the defining equation fully describes the function's behavior and a termination proof using {ref "well-founded-recursion"}[well-founded recursion] would be possible, it may simply be more convenient to define the function as a partial fixpoint to avoid a having to write a termination proof.

Defining recursive functions as partial fixpoints only occurs when explicitly requested by annotating the definition with {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`.

:::paragraph
There are two classes of functions that can be defined as partial fixpoints:

 * Tail-recursive functions whose return type is inhabited type

 * Functions that return values in a suitable monad, such as the {name}`Option` monad

Both classes are backed by the same theory and construction: least fixpoints of monotone equations in chain-complete partial orders.

:::

Just as with structural and well-founded recursion, Lean allows {tech}[mutually recursive] functions to be defined as partial fixpoints.
To use this feature, every function definition in a {tech}[mutual block] must be annotated with the {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` modifier.

```lean (show := false)
section
variable (p : Nat → Bool)
```

:::example "Definition by Partial Fixpoint"

The following function finds the least natural number for which the predicate {lean}`p` holds.
If `p` never holds, then this equation does not specify the behavior: the function {lean}`find` could return {lean type:="Nat"}`42` or any other {lean}`Nat` in that case and still satisfy the equation.

```lean
def find (p : Nat → Bool) (i : Nat := 0) : Nat :=
  if p i then
    i
  else
    find p (i + 1)
partial_fixpoint
```

The elaborator can prove that functions satisfying the equation exist.
Within Lean's logic, {lean}`find` is defined to be an arbitrary such function.
:::

```lean (show := false)
end
```

# Tail-Recursive Functions
%%%
tag := "partial-fixpoint-tailrec"
%%%

:::paragraph

A recursive function can be defined as a partial fixpoint if the following two conditions hold:

 1. The function's return type is inhabited (as with {ref "partial-unsafe"}[functions marked {keywordOf Lean.Parser.Command.declaration}`partial`]) - either a {name}`Nonempty` or {name}`Inhabited` instance works.
 2. All recursive calls are in {tech}[tail position] of the function.

An expression is in {deftech}_tail position_ in the function body if it is:

 * the function body itself,
 * the branches of a {keywordOf Lean.Parser.Term.match}`match` expression that is in tail position,
 * the branches of an {keywordOf termIfThenElse}`if` expression that is in tail position, and
 * the body of a {keywordOf Lean.Parser.Term.let}`let` expression that is in tail position.

In particular, the {tech key:="match discriminant"}[discriminant] of a {keywordOf Lean.Parser.Term.match}`match` expression, the condition of an {keywordOf termIfThenElse}`if` expression and the arguments of functions are not tail positions.

:::

```lean (show := false)
-- Test that nonempty is enough
inductive A : Type where
  | mkA
  | mkA'

instance : Nonempty A := ⟨.mkA⟩

def getA (n : Nat) : A :=
  getA (n + 1)
partial_fixpoint

example (n : Nat) : getA n = getA (n + 3) := by
  conv => lhs; rw [getA, getA, getA]
```

:::example "Loops are Tail Recursive Functions"

Because the function body itself is a {tech}[tail position], the infinitely looping function {lean}`loop` is tail recursive.
It can be defined as a partial fixpoint.

```lean
def loop (x : Nat) : Nat := loop (x + 1)
partial_fixpoint
```

:::

:::example "Tail Recursion with Branching"

{lean}`Array.find` could also be constructed using well-founded recursion with a termination proof, but may be more convenient to define using {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`, where no termination proof is needed.

```lean
def Array.find (xs : Array α) (p : α → Bool)
    (i : Nat := 0) : Option α :=
  if h : i < xs.size then
    if p xs[i] then
      some xs[i]
    else
      Array.find xs p (i + 1)
  else
    none
partial_fixpoint
```

If the result of the recursive call is not just returned, but passed to another function, it is not in tail position and this definition fails.

```lean (keep := false) (error := true) (name := nonTailPos)
def List.findIndex (xs : List α) (p : α → Bool) : Int :=
  match xs with
  | [] => -1
  | x::ys =>
    if p x then
      0
    else
      have r := List.findIndex ys p
      if r = -1 then -1 else r + 1
partial_fixpoint
```
The error message on the recursive call is:
```leanOutput nonTailPos
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    if ys✝.findIndex p = -1 then -1 else ys✝.findIndex p + 1
  Tried to apply 'monotone_ite', but failed.
  Possible cause: A missing `MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
```

:::

# Monadic functions
%%%
tag := "partial-fixpoint-monadic"
%%%


Defining a function as a partial fixpoint is more powerful if the function's return type is a monad that is an instance of {name}`Lean.Order.MonoBind`, such as {name}`Option`.
In this case, recursive call are not restricted to tail-positions, but may also occur inside higher-order monadic functions such as {name}`bind` and {name}`List.mapM`.

The set of higher-order functions for which this works is {ref "partial-fixpoint-theory"}[extensible], so no exhaustive list is given here.
The aspiration is that a monadic recursive function definition that is built using abstract monadic operations like {name}`bind`, but that does not open the abstraction of the monad (e.g. by matching on the {name}`Option` value), is accepted.
In particular, using {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation] should work.

:::example "Monadic functions"

The following function implements the Ackermann function in the {name}`Option` monad, and is accepted without an (explicit or implicit) termination proof:

```lean (keep := false)
def ack : (n m : Nat) → Option Nat
  | 0,   y   => some (y+1)
  | x+1, 0   => ack x 1
  | x+1, y+1 => do ack x (← ack (x+1) y)
partial_fixpoint
```

Recursive calls may also occur within higher-order functions such as {name}`List.mapM`, if they are set up appropriately, and {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation]:

```lean (keep := false)
structure Tree where cs : List Tree

def Tree.rev (t : Tree) : Option Tree := do
  Tree.mk (← t.cs.reverse.mapM (Tree.rev ·))
partial_fixpoint

def Tree.rev' (t : Tree) : Option Tree := do
  let mut cs := []
  for c in t.cs do
    cs := (← c.rev') :: cs
  return Tree.mk cs
partial_fixpoint
```

Pattern matching on the result of the recursive call will prevent the definition by partial fixpoint from going through:

```lean (keep := false) (error := true) (name := monoMatch)
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      match List.findIndex ys p with
      | none => none
      | some r => some (r + 1)
partial_fixpoint
```
```leanOutput monoMatch
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    match ys✝.findIndex p with
    | none => none
    | some r => some (r + 1)
```

In this particular case, using {name}`Functor.map` instead of explicit pattern matching helps:

```lean
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint
```
:::

# Partial Correctness Theorems
%%%
tag := "partial-correctness-theorem"
%%%


For every function defined as a partial fixpoint, Lean proves that the defining equation is satisfied.
This enables proofs by rewriting.
However, these equational theorems are not sufficient for reasoning about the behavior of the function on arguments for which the function specification does not terminate.
Code paths that lead to infinite recursion at runtime would end up as infinite chains of rewrites in a potential proof.

Partial fixpoints in suitable monads, on the other hand, provide additional theorems that map the undefined values from non-termination to suitable values in the monad.
In the {name}`Option` monad, then partial fixpoint equals {name}`Option.none` on all function inputs for which the defining equation specifies non-termination.
From this fact, Lean proves a {deftech}_partial correctness theorem_ for the function which allows facts to be concluded when the function's result is {name}`Option.some`.


::::example "Partial Correctness Theorem"

Recall {lean}`List.findIndex` from an earlier example:

```lean
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint
```

With this function definition, Lean automatically proves the following partial correctness theorem:

```signature
List.findIndex.partial_correctness.{u_1} {α : Type u_1}
  (p : α → Bool)
  (motive : List α → Nat → Prop)
  (h :
    ∀ (findIndex : List α → Option Nat),
      (∀ (xs : List α) (r : Nat), findIndex xs = some r → motive xs r) →
        ∀ (xs : List α) (r : Nat),
          (match xs with
              | [] => none
              | x :: ys =>
                if p x = true then some 0
                else (fun x => x + 1) <$> findIndex ys) = some r →
            motive xs r)
  (xs : List α) (r : Nat) :
  xs.findIndex p = some r →
    motive xs r
```

:::paragraph
Here, the motive is a relation between the parameter and return types of {lean}`List.findIndex`, with the {name}`Option` removed from the return type.
If, when given an arbitrary partial function with a signature that's compatible with {lean}`List.findIndex`, the following hold:

 * the motive is satisfied for all inputs for which the arbitrary function returns a value (rather than {name}`none`),

 * taking one rewriting step with the defining equation, in which the recursive calls are replaced by the arbitrary function, also implies the satisfaction of the motive

then the motive is satsified for all inputs for which the {lean}`List.findIndex` returns {name}`some`.

:::

The partial correctness theorem is a reasoning principle.
It can be used to prove that the resulting number is a valid index in the list and that the predicate holds for that index:

```lean
theorem List.findIndex_implies_pred
    (xs : List α) (p : α → Bool) :
    xs.findIndex p = some i →
    ∃x, xs[i]? = some x ∧ p x := by
  apply List.findIndex.partial_correctness
          (motive := fun xs i => ∃ x, xs[i]? = some x ∧ p x)
  intro findIndex ih xs r hsome
  split at hsome
  next => contradiction
  next x ys =>
    split at hsome
    next =>
      have : r = 0 := by simp_all
      simp_all
    next =>
      simp only [Option.map_eq_map, Option.map_eq_some'] at hsome
      obtain ⟨r', hr, rfl⟩ := hsome
      specialize ih _ _ hr
      simpa
```

::::

# Mutual Recursion with Partial Fixpoints
%%%
tag := "mutual-partial-fixpoint"
%%%

Lean supports the definition of {tech}[mutually recursive] functions using {tech}[partial fixpoint].
Mutual recursion may be introduced using a {tech}[mutual block], but it also results from {keywordOf Lean.Parser.Term.letrec}`let rec` expressions and {keywordOf Lean.Parser.Command.declaration}`where` blocks.
The rules for mutual well-founded recursion are applied to a group of actually mutually recursive, lifted definitions, that results from the {ref "mutual-syntax"}[elaboration steps] for mutual groups.

If all functions in the mutual group have the {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` clause, then this strategy is used.

# Theory and Construction
%%%
tag := "partial-fixpoint-theory"
%%%

The construction builds on a variant of the Knaster–Tarski theorem: In a chain-complete partial order, every monotone function has a least fixed point.

The necessary theory is found in the `Lean.Order` namespace.
This is not meant to be a general purpose library of order theoretic results.
Instead, the definitions and theorems in `Lean.Order` are only intended as implementation details of the {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` feature, and they should be considered a private API that may change without notice.

The notion of a partial order, and that of a chain-complete partial order, are represented by the type classes {name}`Lean.Order.PartialOrder` and {name}`Lean.Order.CCPO`, respectively.

{docstring Lean.Order.PartialOrder (allowMissing := true)}

{docstring Lean.Order.CCPO (allowMissing := true)}

```lean (show := false)
section
open Lean.Order
variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β] (f : α → β) (x y : α)
```

A function is monotone if it preserves partial orders.
That is, if {lean}`x ⊑ y` then {lean}`f x ⊑ f y`.
The operator `⊑` represent {name}`Lean.Order.PartialOrder.rel`.

{docstring Lean.Order.monotone}

The fixpoint of a monotone function can be taken using {name}`fix`, which indeed constructs a fixpoint, as shown by {name}`fix_eq`,

{docstring Lean.Order.fix}

{docstring Lean.Order.fix_eq}

:::paragraph

To construct the partial fixpoint, Lean first synthesizes a suitable {name}`CCPO` instance.

```lean (show := false)
section
universe u v
variable (α : Type u)
variable (β : α → Sort v) [∀ x, CCPO (β x)]
variable (w : α)
```

* If the function's result type has a dedicated instance, like {name}`Option` has with {name}`instCCPOOption`, this is used together with the instance for the function type, {name}`instCCPOPi`, to construct an instance for the whole function's type.

* Otherwise, if the function's type can be shown to be inhabited by a witness {lean}`w`, then the instance {name}`FlatOrder.instCCPO` for the wrapper type {lean}`FlatOrder w` is used. In this order, {lean}`w` is a least element and all other elements are incomparable.

```lean (show := false)
end
```

:::

Next, the recursive calls in the right-hand side of the function definitions are abstracted; this turns into the argument `f` of {name}`fix`. The monotonicity requirement is solved by the {tactic}`monotonicity` tactic, which applies compositional monotonicity lemmas in a syntax-driven way.

```lean (show := false)
section
set_option linter.unusedVariables false
variable {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β] (more : (x : α) → β) (x : α)

local macro "…" x:term:arg "…" : term => `(more $x)
```

The tactic solves goals of the form {lean}`monotone (fun x => … x …)` using the following steps:

* Applying {name}`monotone_const` when there is no dependency on {lean}`x` left.
* Splitting on {keywordOf Lean.Parser.Term.match}`match` expressions.
* Splitting on {keywordOf termIfThenElse}`if` expressions.
* Moving {keywordOf Lean.Parser.Term.let}`let` expression to the context, if the value and type do not depend on {lean}`x`.
* Zeta-reducing a {keywordOf Lean.Parser.Term.let}`let` expression when value and type do depend on {lean}`x`.
* Applying lemmas annotated with {attr}`partial_fixpoint_monotone`

```lean (show := false)
end
```

The following monotonicity lemmas are registered, and should allow recursive calls under the given higher-order functions in the arguments indicated by `·` (but not the other arguments, shown as `_`).

{monotonicityLemmas}
