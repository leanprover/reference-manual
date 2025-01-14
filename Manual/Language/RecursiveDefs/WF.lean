/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
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

In contrast to {ref "structural-recursion"}[structural recursion], which applies syntactic requirements, for well-founded recursion the requirements are _semantic_. This allows a larger class of recursive definitions.


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

A classic example of a recursive function that needs a more complex termination argument is the Ackermann function:

```lean (keep := false)
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
```

The termination argument is a tuple, so every recursive call has to be on arguments that are lexicographically smaller than the parameter. The default {tactic}`decreasing_tactic` can handle this.

In particular, note that the third recursive call has a second argument that is smaller than the second paramter and a first argument that is syntactically equal to the first parameter. This allowed  {tactic}`decreasing_tactic` to apply {name}`Prod.Lex.right`.

```signature
Prod.Lex.right {α β} {ra : α → α → Prop} {rb : β → β → Prop}
  (a : α) {b₁ b₂ : β}
  (h : rb b₁ b₂) :
  Prod.Lex ra rb (a, b₁) (a, b₂)
```

It fails, however, with the following modified function definition, where the third recursive call's first argument is smaller or equal to the first parameter:

```lean (keep := false) (error := true) (name := synack)
def synack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
```
```leanOutput synack (whitespace := lax)
failed to prove termination, possible solutions:
     - Use `have`-expressions to prove the remaining goals
     - Use `termination_by` to specify a different well-founded relation
     - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
case h
m n : Nat
⊢ m / 2 + 1 < m + 1
```

Because {name}`Prod.Lex.right` as not applicable, the tactic used {name}`Prod.Lex.left`, which resulted in the unprovable goal above.

This function definition may require a manual proof that uses the more general theorem {name}`Prod.Lex.right'`, which allows the first component of the tuple (which has to be a {name}`Nat`) to be less or equal:
```signature
Prod.Lex.right' {β} (rb : β → β → Prop)
  {a₂ : Nat} {b₂ : β} {a₁ : Nat} {b₁ : β}
  (h₁ : a₁ ≤ a₂) (h₂ : rb b₁ b₂) :
  Prod.Lex Nat.lt rb (a₁, b₁) (a₂, b₂)
```

```lean (keep := false)
def synack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
decreasing_by
  · apply Prod.Lex.left
    decreasing_trivial
  -- the next goal corresponds to the third recursive call
  · apply Prod.Lex.right'
    · omega
    · omega
  · apply Prod.Lex.left
    omega
```

The {tactic}`decreasing_tactic` tactic does not use the stronger {name}`Prod.Lex.right'` because it would require backtracking if it fails.

:::

# Inferring well-founded recursion

If a recursive function definition does not indicate a termination argument, Lean will attempt to infer one.

If neither {keywordOf Lean.Parser.Command.declaration}`termination_by` nor {keywordOf Lean.Parser.Command.declaration}`decreasing_by` is provided, Lean will try to {ref "inferring-structural-recursion"}[infer structural recursion], before attempting well-founded recursion. If a {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause is present, only well-founded recursion is attempted.

To infer a suitable termination argument, Lean considers a number of {deftech}_termination measures_, which are termination arguments of type {name}`Nat`, and then considers all tuples of these measures.

The termination measures considered are

* all parameters whose type have a with a non-trivial {name}`SizeOf` instance
* the expression `e₂ - e₁` whenever the local context of a recursive call has an assumption of type `e₁ < e₂`, where `e₁` and `e₂` are of type {name}`Nat` and depend only on the function's parameters. {TODO}[Cite “Termination Analysis with Calling Context Graphs” by Panagiotis Manolios &
Daron Vroon, `https://doi.org/10.1007/11817963_36`.]

If using any of the measures, or a tuple thereof, cause all proof obligations to be discharged by {tactic}`decreasing_trivial` or the tactic specified by {keywordOf Lean.Parser.Command.declaration}`decreasing_by`, that is used as the termination argument.

To avoid the combinatoric explosion of trying all tuples of measures, Lean investigates for each measure and each recursive call whether that measure is decreasing or strictly decreasing, tabulates these results and picks a suitable tuple based on that table. This implementation strategy shows up in the error message when no termination argument could be found.
{TODO}[Cite  “Finding Lexicographic Orders for Termination Proofs in Isabelle/HOL”
by Lukas Bulwahn, Alexander Krauss, and Tobias Nipkow, `10.1007/978-3-540-74591-4_5`, `https://www21.in.tum.de/~nipkow/pubs/tphols07.pdf`].

:::example "Termination failure"

If we omit the {keywordOf Lean.Parser.Command.declaration}`termination_by` clause, Lean attempts to infer termination, and if it fails prints the table mentioned above. We include a  {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause simply to prevent Lean from also attempting structural recursion, to keep the error message to the point.

```lean (error := true) (keep := false) (name := badwf)
def f : (n m l : Nat) → Nat
  | n+1, m+1, l+1 => [
      f (n+1) (m+1) (l+1),
      f (n+1) (m-1) (l),
      f (n)   (m+1) (l) ].sum
  | _, _, _ => 0
decreasing_by all_goals decreasing_tactic
```
```leanOutput badwf (whitespace := lax)
Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            n m l
1) 308:6-25 = = =
2) 309:6-23 = < _
3) 310:6-23 < _ _
Please use `termination_by` to specify a decreasing measure.
```

This message conveys the following facts:

* In the first recusive call, all arguments are (provably) equal to the parameters
* In the second recursive call, the first argument is equal and the second argument is provably smaller than the second parameter. The third parameter was not investigated for this recursive call, because it was not necessary to determine that no suitable termination argument exists.
* In the third recursive cal, the first argument decreases strictly.

To investigate why these termination proofs failed it is recommended to write the expected termination argument using {keywordOf Lean.Parser.Command.declaration}`termination_by`. This will surface the messages from the failing tactic.

:::

:::example "Array index idiom"

TODO: Explain the purpose of the complex measure, example of a typical array index iterating function.

:::

:::example "Inference and decreasing tactic"

TODO: Point out that infernce applies the tactic on each goal individually, but then the actual construction on all goals, including lexicographic ordering.

:::

:::example "Inference too powerful"

Due to the issue described above, where {tactic}`decreasing_tactic` is incomplete with regard to lexicographic ordering, it can happen that Lean infers a termination argument hat would work if the tactic would do backtracking, but then the tactic fails. In this case one does not see an error about no termination measure found, but rather sees the error from discharing the failing tactic:

```lean (keep := false) (error := true) (name := badInfer)
def synack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
decreasing_by all_goals decreasing_tactic
```
```leanOutput badInfer
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
case h
m n : Nat
⊢ m / 2 + 1 < m + 1
```

:::



# Mutual recursion
