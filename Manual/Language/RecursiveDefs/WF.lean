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
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Well-Founded recursion" =>
%%%
tag := "well-founded-recursion"
%%%

Functions defined by {deftech}_well-founded recursion_ are those in which each recursive call has arguments that are _smaller_ (in a suitable sense) than the functions' parameters.

In contrast to {ref "structural-recursion"}[stuctural recursion], which applies syntactic requirements, for well-founded recursion the requirements are _semantic_. This allows a larger class of recursive definitions.


To explicitly use well-founded recursion recursion, a function or theorem definition can be annotated with a {keywordOf Lean.Parser.Command.declaration}`termination_by` clause that specifies the {deftech}_termination argument_.

:::syntax Lean.Parser.Termination.terminationBy (title := "Explicit Well-Founded Recursion")

The `termination_by` clause introduces the termination argument.

```grammar
termination_by $[$_:ident* =>]? $term
```

The identifiers before the optional `=>` can bring function parameters into scope that are not
already bound in the declaration header, and the mandatory term must indicate one of the function's parameters, whether introduced in the header or locally in the clause.
:::

The termination argument's type must be equipped with a {tech}_well-founded relation_, which determines when function arguments are to be considered _smaller_.

# Well-founded relations

A relation ≺ is a {deftech}_well-founded relation_ if there exists no infinitely descending chain

$$`` x_0 ≻ x_1 ≻ \cdots``

In Lean, types that are equipped with a canonical well-founded relation are instances of the {name}`WellFoundedRelation` type class.

The most important instances are

* {name}[`Nat`], ordered by `<`

* {name}[`Prod`], ordered lexicographically: `(a₁, b₁) ≺ (a₂,b₂)` if and only if `a₁ ≺ a₂` or `a₁ = a₂` and `b₁ ≺ b₂`.

* Every type that is an instance of the {name}`SizeOf` type class, which provides a method {name}`SizeOf.sizeOf`, has a well-founded order defined by `x₁ ≺ x₂` if and only if `sizeOf x₁ < sizeOf x₂`. For {tech}[inductive types], a `SizeOf` instance is automatically derived by lean.


  Note that there exists a low-priority instance {name}`instSizeOfDefault` that provides a `sizeOf` instance for any type, and always returning `0`. If this instance is picked up for well-founded recursion, a termination proof will not be possible.

  :::example "Default Size Instance"

  Function types in general do not have a useful well-founded order instance, so if the termination argument has function type, the default {name}`SizeOf` instance is picked up:

  ```lean (keep := false)
  def fooInst (b : Bool → Bool) : Unit := fooInst (b ∘ b)
  termination_by b
  decreasing_by
    guard_target = @sizeOf (Bool → Bool) (instSizeOfDefault _) (b ∘ b) < sizeOf b
    simp
    guard_target = False
    sorry
  ```
  :::

# Termination proofs

Once a {tech}[termination argument] is specified and it's {tech}[well-founded relation] is inferred, Lean determines the termination proof obligation for every recursive call.

The proof obligation is of the form `h a₁ a₂ … ≺ h p₁ p₂ …`, where `h` is the termination argument, `≺` the inferred well-founded relation , `a₁ a₂ …` the arguments of the recursive call and `p₁ p₂ …` the parameters of the function. The context of the proof obligation is the context of the recursive call. In particular, local assumptions (such as introduced by `if h : _`, `match h : _ with ` or `have`) are available. If a function parameter is the {tech key:="match discriminant"}[discriminant] of a {keywordOf Lean.Parser.Term.match}`match` expression, then this parameter is refined to the matched pattern in the proof obligation.


All proof obligations are passed as separate goals to the tactic proof specified in the in the {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause, which comes after the {keywordOf Lean.Parser.Command.declaration}`termination_by` clause..

:::example "Termination proof obligations"

The following recursive definition of the Fibonacci numbers has two recursive calls, which translates into two goals:

```lean (error := true) (keep := false) (name := fibGoals)
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```

```leanOutput fibGoals (whitespace := lax)
unsolved goals
   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 2 < n
```

Here, the termination argument is simply the parameter itself, and the well-founded order is the less-then relation on Natural numbers. The first proof goal requires the user to prove that the argument of the first recursive call, namely `n - 1`, is strictly smaller than the functions' parameter, `n`.

These termination proofs can be easily discharged using the {tactic}`omega` tactic.

```lean (keep := false)
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  · omega
  · omega
```
:::

:::example "Refined parameter"

If a parameter of the function is pattern-matched, then the proof obligations mention the refined parameter:

```lean (error := true) (keep := false) (name := fibGoals2)
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) => fib (n + 1) + fib n
termination_by n => n
decreasing_by
  skip
```
```leanOutput fibGoals2 (whitespace := lax)
unsolved goals
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
```
:::

Additionally, in the branches of {ref "if-then-else"}[if-then-else] expressions a hypothesis  asserting the current branch's condition is brought into scope, much as if the dependent if-then-else syntax was used.


:::example "If-then-else"

Here, the {keywordOf termIfThenElse}`if` does not bring a local assumption about the condition into scope. Nevertheless, it is available in the context of the termination proof:

```lean (error := true) (keep := false) (name := fibGoals3)
def fib (n : Nat) :=
  if n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```

```leanOutput fibGoals3 (whitespace := lax)
unsolved goals
   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 2 < n
```
:::

# Default termination proof tactic

If no {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause is given, then the {tactic}`decreasing_tactic` is used, and applied to each proof obligation separately.

:::tactic "decreasing_tactic"

The {tactic}`decreasing_tactic` mainly deals with lexicographic ordering of tuples, applying {name}`Prod.Lex.right` if the left components of the product are {tech (key := "definitional equality")}`definitionally equal`, and {name}`Prod.Lex.left` otherwise. After handling tuples this way, it calls the {tactic}`decreasing_tactic` tactic.

:::


:::tactic "decreasing_trivial"

The {tactic}`decreasing_trivial` is an extensible tactic that applies a few common heuristics to solve a termination goal. In particular, it tries the following tactics and theorems:

* {tactic}`simp_arith`.
* {tactic}`assumption`.
* theorems {name}`Nat.sub_succ_lt_self`, {name}`Nat.pred_lt'`, {name}`Nat.pred_lt`, which handle common arithmetic goals.
* {tactic}`omega`.
* {tactic}`array_get_dec` and {tactic}`array_mem_dec`, which prove that the size of array elements is less than the size of the array.
* {tactic}`sizeOf_list_dec` that the size of list elements is less than the size of the list.
* {name}`String.Iterator.sizeOf_next_lt_of_hasNext` and {name}`String.Iterator.sizeOf_next_lt_of_atEnd`, to handle iteration through a string using  {keywordOf Lean.Parser.Term.doFor}`for`.

This tactic is intended to be extended by further heuristics using {keywordOf Lean.Parser.Command.macro_rules}`macro_rules`.

:::


:::example "No Backtracking of Lexicographic Order"

TODO

:::

# Inferring well-founded recursion

# Mutual recursion
