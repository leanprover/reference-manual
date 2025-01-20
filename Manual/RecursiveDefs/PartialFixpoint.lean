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
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

#doc (Manual) "Partial Fixpoint Recursion" =>
%%%
tag := "partial-fixpoint"
%%%

A function definition can be understood as a request to Lean to construct a function of the given type that satisfies the given equation.
One purpose of the termination proof in {ref "structural-recursion"}[structural recursion] or {ref "well-founded-recursion"}[well-founded recursion] is to guarantee the existence and uniqueness the constructed functions.

In some cases, the equation may not uniquely determine the function's (extensional) behavior, because it
does not terminate for all arguments in the above sense, but there still exist functions for which the defining equation holds.
In these cases, a definition by {deftech}_partial fixpoint_ may be possible.

Even in cases where the defining equation fully describes the function's behavior and a termination proof using {ref "well-founded-recursion"}[well-founded recursion] would be possible it may simply be more convenient to define the function using partial fixpoint, to avoid a possible tedious termination proof.

Definition by partial fixpoint is only used when explicitly requested by the user, by annotating the definition with {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`.

There are two classes of functions for which a definition by partial fixpoint works:

* tail-recursive functions of inhabited type, and
* monadic functions in a suitable monad, such as the {name}`Option` monad.

Both classes are backed by the same theory and construction: least fixpoints of monotone equations in chain-complete partial orders.

Lean supports {tech}[mutually recursive] functions to be defined by partial fixpoint.
For this, every function definition in a mutual block has to be annotated with {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`.

:::example "Definition by Partial Fixpoint"

The following function find the least natural number for which the predicate `p` holds.
If `p` never holds then this equation does not specify the behavior: the function `find` could return 42 in that case, and still satisfy the equation.

```lean (keep := false)
def find (p : Nat → Bool) (i : Nat := 0) : Nat :=
  if p i then
    i
  else
    find p (i + 1)
partial_fixpoint
```

The elaborator can prove that functions satisfying the equation exist, and defined `find` to be an arbitrary such function.
:::

# Tail-recursive functions
%%%
tag := "partial-fixpoint-tailrec"
%%%

Definition by partial fixpoint will succeed if the following two conditions hold:

1. The function's type is inhabited (as with {ref "partial-unsafe"}[functions marked {keywordOf Lean.Parser.Command.declaration}`partial`]).
2. All recursive calls are in {tech}[tail position] of the function.

A {deftech}_tail position_ of the function body is

* the function body itself,
* the branches of a {keywordOf Lean.Parser.Term.match}`match` expression in tail position,
* the branches of an {keywordOf termIfThenElse}`if` expression in tail position, and
* the body of a {keywordOf Lean.Parser.Term.let}`let` expression in tail position.

In particular, the {tech key:="match discriminant"}[discriminant] of a {keywordOf Lean.Parser.Term.match}`match` expression, the condition of an {keywordOf termIfThenElse}`if` expression and the arguments of functions are not tail-positions.

:::example "Tail recursive functions"

Because the function body itself is a tail-position, clearly looping definitions are accepted:

```lean (keep := false)
def loop (x : Nat) : Nat := loop (x + 1)
partial_fixpoint
```

More useful function definitions tend to have some branching.
The following example could also be constructed using well-founded recursion with a termination proof, but may be more convenient to define using  {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`, where no termination proof is needed.

```lean (keep := false)
def Array.find (xs : Array α) (p : α → Bool) (i : Nat := 0) : Option α :=
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
```leanOutput nonTailPos
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    let_fun r := ys✝.findIndex p;
    if r = -1 then -1 else r + 1
```

:::

# Monadic functions
%%%
tag := "partial-fixpoint-monadic"
%%%


Definition by partial fixpoint is more powerful if the function's type is monadic and the monad is an instance of {name}`Lean.Order.MonoBind`, such as {name}`Option`.
In this case, recursive call are not restricted to tail-positions, but can also be inside higher-order monadic functions such as {name}`bind` and {name}`List.mapM`.

The set of higher-order functions for which this works is extensible (see TODO below), so no exhaustive list is given here.
The aspiration is that a monadic recursive function definition that is built using abstract monadic operations like {name}`bind`, but not open the abstraction of the monad (e.g. by matching on the {name}`Option` value), is accepted.
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

Pattern matching on the result of the recursive call will prevent the definition by partial fixpoint to go through:

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

In this particular case, using the {name}`Functor.map` function instead of explicit pattern matching helps:

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

# Partial Correctness Theorem
%%%
tag := "partial-correctness-theorem"
%%%

In general, for functions defined by partial fixpoint we only obtain the equational theorems that prove that the function indeed satisfies the given equation, and enables proofs by rewriting.
But these do not allow reasoning about the behavior of the function on arguments for which the function specification does not terminate.

If the monad happens to be the {name}`Option` monad, then by construction the function equals {name}`Option.none` on all function inputs for which the defining equation is not terminating.
From this fact, Lean proves a {deftech}_partial correctness theorem_ for the function which allows concluding facts from the function's result being {name}`Option.some`.


:::example "Partial correctness theorem"

Recall this function from an earlier example:

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

With this function definition, Lean proves the following partial correctness theorem:

{TODO}[using `signature` causes max recursion error]

```
List.findIndex.partial_correctness {α : Type _} (motive : List α → (α → Bool) → Nat → Prop)
  (h :
    ∀ (findIndex : List α → (α → Bool) → Option Nat),
      (∀ (xs : List α) (p : α → Bool) (r : Nat), findIndex xs p = some r → motive xs p r) →
        ∀ (xs : List α) (p : α → Bool) (r : Nat),
          (match xs with
              | [] => none
              | x :: ys => if p x = true then some 0 else (fun x => x + 1) <$> findIndex ys p) =
              some r →
            motive xs p r)
  (xs : List α) (p : α → Bool) (r : Nat) : xs.findIndex p = some r → motive xs p r
```

We can use this theorem to prove that the resulting number is a valid index in the list and that the predicate holds for that index:

```lean
theorem List.findIndex_implies_pred (xs : List α) (p : α → Bool) :
    xs.findIndex p = some i → xs[i]?.any p := by
  apply List.findIndex.partial_correctness
          (motive := fun xs p i => xs[i]?.any p)
  intro findIndex ih xs p r hsome
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
      specialize ih _ _ _ hr
      simpa
```

:::

# Mutual Well-Founded Recursion
%%%
tag := "mutual-well-founded-recursion"
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
Instead, the definitions and theorems therein are only intended to back the
{keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` feature.

The notion of a partial order, and that of a chain-complete partial order, are represented as type classes:

{docstring Lean.Order.PartialOrder}

{docstring Lean.Order.CCPO}

The fixpoint of a monotone function can be taken using {name}`fix`, which indeed constructs a fixpoint, as shown by {name}`fix_eq`,

{docstring Lean.Order.fix}

{docstring Lean.Order.fix_eq}

So to construct the function, Lean first infers a suitable {name}`CCPO` instance.

```lean (show := false)
section
universe u v
variable (α : Type u)
variable (β : α → Sort v) [∀ x, CCPO (β x)]
variable (w : α)
```

* If the function's result type has a dedicated instance, like {name}`Option` has with {name}`instCCPOOption`, this is used together with the instance for the function type, {name}`instCCPOPi`, to construct an instance for the whole function's type.

* Else, if the function's type can be shown to be inhabited by a witness {lean}`w`, then the instance {name}`FlatOrder.instCCPO` for the wrapper type {lean}`FlatOrder w` is used. In this order, {lean}`w` is a least element and all other elements are incomparable.

```lean (show := false)
end
```

Next, the recursive calls in the right-hand side of the function definitions are abstracted; this turns into the argument `f` of {name}`fix`. The monotonicity requirement is solved by the {tactic}`monotonicity` tactic, which applies compositional monotonicity lemmas in a syntax-driven way

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


{TODO}[I wonder if this needs to be collapsible. I at some point I had it in an example, but it's not really an example. Should be this collapsible? Is there a better way than to use example?]

{TODO}[This table probably needs some styling? Less vertical space maybe?]

{TODO}[How can we I pretty-print these pattern expressions so that hovers work?]

The following monotonicity lemmas are registered, and should allow recursive calls under the given higher-order functions in the arguments indicated by `·` (but not the other arguments, shown as `_`).

{monotonicityLemmas}
