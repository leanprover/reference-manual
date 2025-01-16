/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Language.RecursiveDefs.WF.GuessLexExample

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Well-Founded Recursion" =>
%%%
tag := "well-founded-recursion"
%%%

Functions defined by {deftech}_well-founded recursion_ are those in which each recursive call has arguments that are _smaller_ (in a {ref "wf-rel"}[suitable sense]) than the functions' parameters.
In contrast to {ref "structural-recursion"}[structural recursion], in which recursive definitions must satisfy particular _syntactic_ requirements, definitions that use well-founded recursion employ _semantic_ arguments.
This allows a larger class of recursive definitions to be accepted.
Furthermore, when Lean's automation fails to construct a termination proof, it is possible to specify one manually.

All definitions are treated identically by the Lean compiler.
In Lean's logic, definitions that use well-founded recursion do not necessarily reduce {tech key:="definitional equality"}[definitionally].
The reductions do hold as propositional equalities, however, and Lean automatically proves them.
This does not typically make it more difficult to prove properties of definitions that use well-founded recursion, because the propositional reductions can be used to reason about the behavior of the function.
It does mean, however, that using these functions in types typically does not work well.
When the reduction behavior does hold definitionally, it is often much slower than structurally recursive definitions in the kernel, which must unfold the termination argument along with the definition.
When possible, recursive function that are intended for use in types or in other situations where definitional equality is important should be defined with structural recursion.

To explicitly use well-founded recursion recursion, a function or theorem definition can be annotated with a {keywordOf Lean.Parser.Command.declaration}`termination_by` clause that specifies the {deftech}_termination argument_.

:::syntax Lean.Parser.Termination.terminationBy (title := "Explicit Well-Founded Recursion")

The {keywordOf Lean.Parser.Command.declaration}`termination_by` clause introduces the termination argument.

```grammar
termination_by $[$_:ident* =>]? $term
```

The identifiers before the optional `=>` can bring function parameters into scope that are not
already bound in the declaration header, and the mandatory term must indicate one of the function's parameters, whether introduced in the header or locally in the clause.
:::

The termination argument's type must be equipped with a {tech}[well-founded relation], which determines when function arguments are considered _smaller_.

# Well-founded relations
%%%
tag := "wf-rel"
%%%

A relation ≺ is a {deftech}_well-founded relation_ if there exists no infinitely descending chain

$$`` x_0 ≻ x_1 ≻ \cdots``

In Lean, types that are equipped with a canonical well-founded relation are instances of the {name}`WellFoundedRelation` type class.

{docstring WellFoundedRelation}

```lean (show := false)
section
variable {α : Type u} {β : Type v} (a₁ a₂ : α) (b₁ b₂ : β) [WellFoundedRelation α] [WellFoundedRelation β]
variable {γ : Type u} (x₁ x₂ : γ) [SizeOf γ]
local notation x " ≺ " y => WellFoundedRelation.rel x y
```

The most important instances are:

* {name}[`Nat`], ordered by {lean type:="Nat → Nat → Prop"}`(· < ·)`.

* {name}[`Prod`], ordered lexicographically: {lean}`(a₁, b₁) ≺ (a₂, b₂)` if and only if {lean}`a₁ ≺ a₂` or {lean}`a₁ = a₂` and {lean}`b₁ ≺ b₂`.

* Every type that is an instance of the {name}`SizeOf` type class, which provides a method {name}`SizeOf.sizeOf`, has a well-founded relation.
  For these types, {lean}`x₁ ≺ x₂` if and only if {lean}`sizeOf x₁ < sizeOf x₂`. For {tech}[inductive types], a {lean}`SizeOf` instance is automatically derived by Lean.

```lean (show := false)
end
```

Note that there exists a low-priority instance {name}`instSizeOfDefault` that provides a {lean}`SizeOf` instance for any type, and always returns {lean}`0`.
This instance cannot be used to prove that a function terminates using well-founded recursion because {lean}`0 < 0` is false.

```lean (show := false)

-- Check claims about instSizeOfDefault

example {α} (x : α) : sizeOf x = 0 := by rfl

/-- info: instSizeOfDefault.{u} (α : Sort u) : SizeOf α -/
#guard_msgs in
#check instSizeOfDefault

```

:::example "Default Size Instance"

Function types in general do not have a well-founded relation that's useful for termination proofs.
{tech}[Instance synthesis] thus selects {name}`instSizeOfDefault` and the corresponding well-founded relation.
If the parameter selected termination argument has function type, the default {name}`SizeOf` instance is picked up, and the proof cannot succeed.

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

Once a {tech}[termination argument] is specified and its {tech}[well-founded relation] is inferred, Lean determines the termination proof obligation for every recursive call.

The proof obligation is of the form `g a₁ a₂ … ≺ g p₁ p₂ …`, where
 * `g` is the termination argument,
 *  `≺` is the inferred well-founded relation,
 * `a₁ a₂ …` are the arguments of the recursive call and
 * `p₁ p₂ …` are the parameters of the function definition.

The context of the proof obligation is the context of the recursive call. In particular, local assumptions (such as introduced by `if h : _`, `match h : _ with ` or `have`) are available. If a function parameter is the {tech key:="match discriminant"}[discriminant] of a {keywordOf Lean.Parser.Term.match}`match` expression, then in the proof obligation this parameter is refined to the matched pattern.

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

Here, the termination argument is simply the parameter itself, and the well-founded order is the less-than relation on natural numbers. The first proof goal requires the user to prove that the argument of the first recursive call, namely `n - 1`, is strictly smaller than the function's parameter, `n`.

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

:::example "Nested Recursion in Higher-order Functions"

When recursive calls are nested in higher-order functions, sometimes the function definition has to be adjusted so that the termination proof obligations can be discharged. This often happens when defining functions recursively over {ref "nested-inductive-types"}[nested inductive types], such as the following tree structure:

```lean
structure Tree where
  children : List Tree
```

A naive attempt to define a recursive function over this data structure will fail:
```lean (keep := false) (name := nestedBad) (error := true)
def Tree.depth (t : Tree) : Nat :=
  let depths := t.children.map (fun c => Tree.depth c)
  match depths.max? with
  | some d => d+1
  | none => 0
termination_by t
```
```leanOutput nestedBad
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
t c : Tree
⊢ sizeOf c < sizeOf t
```

The shown proof obligation is not provable, as nothing ties `c` to `t`. Lean does not see that the {name}`List.map` function applies its function arguments only to elements of the given list.

Because the termination proof goal provides access to the local context of the recursive call, it helps to bring facts into scope in the function definition that indicate that `c` is indeed an element of the list `t.children`. This can be achieved by annotating the elements of that list with a proof that they are in the list, using the function {name}`List.attach`, and bringing this proof into scope in the function passed to `List.map`:

```lean (keep := false)
def Tree.depth (t : Tree) : Nat :=
  let depths := t.children.attach.map (fun ⟨c, hc⟩ => Tree.depth c)
  match depths.max? with
  | some d => d+1
  | none => 0
termination_by t
decreasing_by
  decreasing_tactic
```

Note that the proof goal after {keywordOf Lean.Parser.Command.declaration}`decreasing_by` now includes the assumption `c ∈ t.children`, which suffices for {tactic}`decreasing_tactic` to go through.

:::

::::TODO

:::example "Nested recursive calls and subtypes"

I wanted to include a good example where recursive calls are nested inside each other, and one likely needs to introduce a subtype in the result to make it go through. But can't think of something nice and natural right now.

:::

::::

# Default termination proof tactic

If no {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause is given, then the {tactic}`decreasing_tactic` is used implicitly, and applied to each proof obligation separately.

::::TODO
Below the manual prose I included is appended to the docstring. Can I use `:::tactic` and only show my text, ignoring the docstring? (If only until the docstring is massaged to work both here and on its own?)
::::

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

The termination argument is a tuple, so every recursive call has to be on arguments that are lexicographically smaller than the parameters. The default {tactic}`decreasing_tactic` can handle this.

In particular, note that the third recursive call has a second argument that is smaller than the second parameter and a first argument that is syntactically equal to the first parameter. This allowed  {tactic}`decreasing_tactic` to apply {name}`Prod.Lex.right`.

```signature
Prod.Lex.right {α β} {ra : α → α → Prop} {rb : β → β → Prop}
  (a : α) {b₁ b₂ : β}
  (h : rb b₁ b₂) :
  Prod.Lex ra rb (a, b₁) (a, b₂)
```

It fails, however, with the following modified function definition, where the third recursive call's first argument is provably smaller or equal to the first parameter, but not syntactically equal:

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

This function definition may require a manual proof that uses the more general theorem {name}`Prod.Lex.right'`, which allows the first component of the tuple (which has to be of type {name}`Nat`) to be less or equal:
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
    omega
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
%%%
tag := "inferring-well-founded-recursion"
%%%

If a recursive function definition does not indicate a termination argument, Lean will attempt to infer one.

If neither {keywordOf Lean.Parser.Command.declaration}`termination_by` nor {keywordOf Lean.Parser.Command.declaration}`decreasing_by` is provided, Lean will try to {ref "inferring-structural-recursion"}[infer structural recursion], before attempting well-founded recursion. If a {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause is present, only well-founded recursion is attempted.

To infer a suitable termination argument, Lean considers multiple {deftech}_termination measures_, which are termination arguments of type {name}`Nat`, and then tries all tuples of these measures.

The termination measures considered are

* all parameters whose type have a non-trivial {name}`SizeOf` instance
* the expression `e₂ - e₁` whenever the local context of a recursive call has an assumption of type `e₁ < e₂` or `e₁ ≤ e₂`, where `e₁` and `e₂` are of type {name}`Nat` and depend only on the function's parameters. {TODO}[Cite “Termination Analysis with Calling Context Graphs” by Panagiotis Manolios &
Daron Vroon, `https://doi.org/10.1007/11817963_36`.]

If using any of the measures, or a tuple thereof, allows all proof obligations to be discharged by {tactic}`decreasing_trivial` or the tactic specified by {keywordOf Lean.Parser.Command.declaration}`decreasing_by`, that is used as the termination argument.

A {keyword}`termination_by?` clause causes the inferred termination annotation to be shown.
It can be automatically added to the source file using the offered suggestion or code action.

To avoid the combinatorial explosion of trying all tuples of measures, Lean investigates for each measure and each recursive call whether that measure is decreasing or strictly decreasing, tabulates these results and picks a suitable tuple based on that table. This implementation strategy shows up in the error message when no termination argument could be found.
{TODO}[Cite  “Finding Lexicographic Orders for Termination Proofs in Isabelle/HOL”
by Lukas Bulwahn, Alexander Krauss, and Tobias Nipkow, `10.1007/978-3-540-74591-4_5`, `https://www21.in.tum.de/~nipkow/pubs/tphols07.pdf`].

{spliceContents Manual.Language.RecursiveDefs.WF.GuessLexExample}

:::example "Array index idiom"

The purpose of considering expressions of the form `e₂ - e₁` as measures is to support the common idiom of counting up to some upper bound, in particular when traversing arrays in possibly interesting ways. In the following function, which performs binary search on a sorted array, this heuristic helps Lean to find the `j - i` measure.

```lean (keep := false)
def binarySearch (x : Int) (xs : Array Int) : Option Nat :=
  go 0 xs.size
where
  go (i j : Nat) (hj : j ≤ xs.size := by omega) :=
    if h : i < j then
      let mid := (i + j) / 2
      let y := xs[mid]
      if x = y then
        some mid
      else if x < y then
        go i mid
      else
        go (mid + 1) j
    else
      none
  termination_by?
```

:::

:::example "Inference and decreasing tactic"

The tactic indicated by {keywordOf Lean.Parser.Command.declaration}`decreasing_by` is used slightly differently when inferring the termination argument, and in the actual termination proof.

* During inference, it is applied to a _single_ goal attempting to prove `<` or `≤` on {name}`Nat`.
* During the termination proof, it is applied to possibly goals (one per recursive call), and the goals may involve the lexicographic ordering of pairs.

A consequence is that a {keywordOf Lean.Parser.Command.declaration}`decreasing_by` block that addresses goals individually and which works successfully with an explicit termination argument will cause inference of the termination argument to fail:

```lean (keep := false) (error := true)
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
decreasing_by
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    omega
```

It is advisable to always include a {keywordOf Lean.Parser.Command.declaration}`termination_by` clause whenever an explicit {keywordOf Lean.Parser.Command.declaration}`decreasing_by` proof is given.

:::

:::example "Inference too powerful"

Due to the issue described above, where {tactic}`decreasing_tactic` is incomplete with regard to lexicographic ordering, it can happen that Lean infers a termination argument hat would work if the tactic would do backtracking, but then the tactic fails. In this case one does not see an error about no termination measure found, but rather sees the error from discharging the failing tactic:

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

In this case, explicitly stating the termination argument helps.

:::

# Mutual well-founded recursion
%%%
tag := "mutual-well-founded-recursion"
%%%

Lean supports the definition of {tech}[mutually recursive] functions using well-founded recursion.
Mutual recursion may be introduced using a {tech}[mutual block], but it also results from {keywordOf Lean.Parser.Term.letrec}`let rec` expressions and {keywordOf Lean.Parser.Command.declaration}`where` blocks.
The rules for mutual well-founded recursion are applied to a group of actually mutually recursive, lifted definitions, that results from the {ref "mutual-syntax"}[elaboration steps] for mutual groups.

If any function in the mutual group has {keywordOf Lean.Parser.Command.declaration}`termination_by` or {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause, well-founded recursion is attempted.

If a termination argument is specified using {keywordOf Lean.Parser.Command.declaration}`termination_by` for any function, then all functions must specify a termination argument, and they have to have the same type.

If no termination argument is specified, the termination argument is {ref "inferring-well-founded-recursion"}[inferred, as described above]. In the case of mutual recursion, a third class of measures is considered during inference, namely for each function in the mutual group the measure that is `1` for that function and `0` for the others. This allows Lean to order the functions so that some calls from one function to another are allowed even if the parameters do not decrease.

:::example "Mutual recursion without parameter decrease"

In the following mutual function definitions, the parameter does not decrease in the call from `g` to `f`. Still, the definition is accepted by ordering the functions themselves:

```lean (keep := false)
mutual
def f : (n : Nat) → Nat
  | 0 => 0
  | n+1 => g n
termination_by?

def g (n : Nat) : Nat := (f n) + 1
termination_by?
end
```

:::

# Theory and construction

This section gives a very brief glimpse into the construction well-founded recursion, which may surface occasionally.

The elaboration of functions defined by well-founded recursion is based on the {name}`WellFounded.fix` operator.

{docstring WellFounded.fix}

The type `α` is instantiated with the function's (varying) parameters, packed into one type using {name}`PSigma`. The {name}`WellFounded` relation is constructed from the {tech}[termination argument] via {name}`invImage`.

The function's body is passed to {name}`WellFounded.fix`, with parameters suitable packed and unpacked, and recursive calls are replaced with a call to the value provided by {name}`WellFounded.fix`. The termination proofs generated by the {keywordOf Lean.Parser.Command.declaration}`decreasing_by` are inserted in the right place.

Finally, the equational and unfolding theorems for the recursive function are proved from {name}`WellFounded.fix_eq`, undoing the argument mangling.

In the case of mutual recursion, an equivalent non-mutual function is constructed by combining the function's arguments using {name}`PSum`, and pattern-matching on that sum type in the result type and the body.

The definition of {name}`WellFounded` builds on the notion of _accessible elements_ of the relation:

{docstring WellFounded}

{docstring Acc}
