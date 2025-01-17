/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Papers
import Manual.RecursiveDefs.WF.GuessLexExample

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
In Lean's logic, definitions that use well-founded recursion typically do not reduce {tech key:="definitional equality"}[definitionally].
The reductions do hold as propositional equalities, however, and Lean automatically proves them.
This does not typically make it more difficult to prove properties of definitions that use well-founded recursion, because the propositional reductions can be used to reason about the behavior of the function.
It does mean, however, that using these functions in types typically does not work well.
Even when the reduction behavior happens to hold definitionally, it is often much slower than structurally recursive definitions in the kernel, which must unfold the termination proof along with the definition.
When possible, recursive function that are intended for use in types or in other situations where definitional equality is important should be defined with structural recursion.

To explicitly use well-founded recursion recursion, a function or theorem definition can be annotated with a {keywordOf Lean.Parser.Command.declaration}`termination_by` clause that specifies the {deftech}_measure_ by which the function terminates.
The measure should be a term that decreases at each recursive call; it may be one of the function's parameters or a tuple of the parameters, but it may also be any other term.
The measure's type must be equipped with a {tech}[well-founded relation], which determines what it means for the measure to decrease.

:::syntax Lean.Parser.Termination.terminationBy (title := "Explicit Well-Founded Recursion")

The {keywordOf Lean.Parser.Command.declaration}`termination_by` clause introduces the termination argument.

```grammar
termination_by $[$_:ident* =>]? $term
```

The identifiers before the optional `=>` can bring function parameters into scope that are not
already bound in the declaration header, and the mandatory term must indicate one of the function's parameters, whether introduced in the header or locally in the clause.
:::

:::example "Division by Iterated Subtraction"
Division can be specified as the number of times the divisor can be subtracted from the dividend.
This operation cannot be elaborated using structural recursion because subtraction is not pattern matching.
The value of `n` does decrease with each recursive call, so well-founded recursion can be used to justify the definition of division by iterated subtraction.

```lean
def div (n k : Nat) : Nat :=
  if k = 0 then 0
  else if k > n then 0
  else 1 + div (n - k) k
termination_by n
```
:::

# Well-Founded Relations
%%%
tag := "wf-rel"
%%%

A relation `≺` is a {deftech}_well-founded relation_ if there exists no infinitely descending chain

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
{ref "instance-synth"}[Instance synthesis] thus selects {name}`instSizeOfDefault` and the corresponding well-founded relation.
If the measure is a function, the default {name}`SizeOf` instance is selected and the proof cannot succeed.

```lean (keep := false)
def fooInst (b : Bool → Bool) : Unit := fooInst (b ∘ b)
termination_by b
decreasing_by
  guard_target =
    @sizeOf (Bool → Bool) (instSizeOfDefault _) (b ∘ b) < sizeOf b
  simp only [sizeOf, default.sizeOf]
  guard_target = 0 < 0
  simp
  guard_target = False
  sorry
```
:::

# Termination proofs

Once a {tech}[measure] is specified and its {tech}[well-founded relation] is determined, Lean determines the termination proof obligation for every recursive call.

```lean (show := false)
section
variable {α : Type u} {β : α → Type v} {β' : Type v} (more : β') (g : (x : α) → (y : β x) → β' → γ) [WellFoundedRelation γ] (a₁ p₁ : α) (a₂ : β a₁) (p₂ : β p₁)

local notation (name := decRelStx) x " ≺ " y => WellFoundedRelation.rel x y
local notation "…" => more

```

The proof obligation for each recursive call is of the form {lean}`g a₁ a₂ … ≺ g p₁ p₂ …`, where:
 * {lean}`g` is the measure as a function of the parameters,
 * {name WellFoundedRelation.rel}`≺` is the inferred well-founded relation,
 * {lean}`a₁` {lean}`a₂` {lean}`…` are the arguments of the recursive call and
 * {lean}`p₁` {lean}`p₂` {lean}`…` are the parameters of the function definition.

The context of the proof obligation is the local context of the recursive call.
In particular, local assumptions (such as those introduced by `if h : _`, `match h : _ with ` or `have`) are available.
If a function parameter is the {tech key:="match discriminant"}[discriminant] of a pattern match (e.g. by a {keywordOf Lean.Parser.Term.match}`match` expression), then this parameter is refined to the matched pattern in the proof obligation.

```lean (show := false)
end
```

The overall termination proof obligation consists of one goal for each recursive call.
By default, the tactic {tactic}`decreasing_trivial` is used to prove each proof obligation.
A custom tactic script can be provided using the optional {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause, which comes after the {keywordOf Lean.Parser.Command.declaration}`termination_by` clause.
This tactic script is run once, with one goal for each proof obligation, rather than separately on each proof obligation.

```lean (show := false)
section
variable {n : Nat}
```

::::example "Termination Proof Obligations"

The following recursive definition of the Fibonacci numbers has two recursive calls, which results in two goals in the termination proof.

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

```leanOutput fibGoals (whitespace := lax) (show := false)
unsolved goals
   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 2 < n
```

```proofState
∀ (n : Nat), (h : ¬ n ≤ 1) → n - 1 < n ∧ n - 2 < n := by
  intro n h
  apply And.intro ?_ ?_
/--
n : Nat
h : ¬n ≤ 1
⊢ n - 1 < n

n : Nat
h : ¬n ≤ 1
⊢ n - 2 < n
-/

```



Here, the {tech}[measure] is simply the parameter itself, and the well-founded order is the less-than relation on natural numbers.
The first proof goal requires the user to prove that the argument of the first recursive call, namely {lean}`n - 1`, is strictly smaller than the function's parameter, {lean}`n`.

Both termination proofs can be easily discharged using the {tactic}`omega` tactic.

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
::::
```lean (show := false)
end
```

:::example "Refined Parameters"

If a parameter of the function is the {tech key:="match discriminant"}[discriminant] of a pattern match, then the proof obligations mention the refined parameter.

```lean (error := true) (keep := false) (name := fibGoals2)
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) => fib (n + 1) + fib n
termination_by n => n
decreasing_by
  skip
```
```leanOutput fibGoals2 (whitespace := lax) (show := false)
unsolved goals
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
```

```proofState
∀ (n : Nat), n + 1 < n.succ.succ ∧ n < n.succ.succ := by
  intro n
  apply And.intro ?_ ?_
/--
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
-/

```

:::

Additionally, in the branches of {ref "if-then-else"}[if-then-else] expressions, a hypothesis asserting the current branch's condition is brought into scope, much as if the dependent if-then-else syntax had been used.


:::example "Local Assumptions and Conditionals"

Here, the {keywordOf termIfThenElse}`if` does not bring a local assumption about the condition into scope. Nevertheless, it is available in the context of the termination proof.

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

```leanOutput fibGoals3 (whitespace := lax) (show := false)
unsolved goals
   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 2 < n
```

```proofState
∀ (n : Nat), («h✝» : ¬ n ≤ 1) → n - 1 < n ∧ n - 2 < n := by
  intro n «h✝»
  apply And.intro ?_ ?_
/--
n : Nat
h✝ : ¬n ≤ 1
⊢ n - 1 < n

n : Nat
h✝ : ¬n ≤ 1
⊢ n - 2 < n
-/

```



:::

```lean (show := false)
section
```

:::example "Nested Recursion in Higher-order Functions"

When recursive calls are nested in higher-order functions, sometimes the function definition has to be adjusted so that the termination proof obligations can be discharged.
This often happens when defining functions recursively over {ref "nested-inductive-types"}[nested inductive types], such as the following tree structure:

```lean
structure Tree where
  children : List Tree
```

A naïve attempt to define a recursive function over this data structure will fail:
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

```lean (show := false)
variable (t : Tree) (c : Tree)
```


The termination proof obligation is not provable, because there is no connection between the local variable {lean}`c` and the parameter {lean}`t`.
However, {name}`List.map` applies its function argument only to elements of the given list; thus, {lean}`c` is always an element of {lean}`t.children`.

Because the termination proof goal provides access to the local context of the recursive call, it helps to bring facts into scope in the function definition that indicate that {lean}`c` is indeed an element of the list {lean}`t.children`.
This can be achieved by “attaching” a proof of membership in {lean}`t.children` to each of its elements using the function {name}`List.attach` and then bringing this proof into scope in the function passed to {name}`List.map`:

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

Note that the proof goal after {keywordOf Lean.Parser.Command.declaration}`decreasing_by` now includes the assumption {lean}`c ∈ t.children`, which suffices for {tactic}`decreasing_tactic` to succeed.

:::

```lean (show := false)
end
```


::::TODO

:::example "Nested recursive calls and subtypes"

I (Joachim) wanted to include a good example where recursive calls are nested inside each other, and one likely needs to introduce a subtype in the result to make it go through. But can't think of something nice and natural right now.

:::

::::

# Default Termination Proof Tactic

If no {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause is given, then the {tactic}`decreasing_tactic` is used implicitly, and applied to each proof obligation separately.


:::tactic "decreasing_tactic" (replace := true)

The tactic {tactic}`decreasing_tactic` mainly deals with lexicographic ordering of tuples, applying {name}`Prod.Lex.right` if the left components of the product are {tech (key := "definitional equality")}[definitionally equal], and {name}`Prod.Lex.left` otherwise.
After preprocessing tuples this way, it calls the {tactic}`decreasing_trivial` tactic.

:::


:::tactic "decreasing_trivial"

The tactic {tactic}`decreasing_trivial` is an extensible tactic that applies a few common heuristics to solve a termination goal.
In particular, it tries the following tactics and theorems:

* {tactic}`simp_arith`
* {tactic}`assumption`
* theorems {name}`Nat.sub_succ_lt_self`, {name}`Nat.pred_lt'`, {name}`Nat.pred_lt`, which handle common arithmetic goals
* {tactic}`omega`
* {tactic}`array_get_dec` and {tactic}`array_mem_dec`, which prove that the size of array elements is less than the size of the array
* {tactic}`sizeOf_list_dec` that the size of list elements is less than the size of the list
* {name}`String.Iterator.sizeOf_next_lt_of_hasNext` and {name}`String.Iterator.sizeOf_next_lt_of_atEnd`, to handle iteration through a string using  {keywordOf Lean.Parser.Term.doFor}`for`

This tactic is intended to be extended with further heuristics using {keywordOf Lean.Parser.Command.macro_rules}`macro_rules`.

:::


:::example "No Backtracking of Lexicographic Order"

A classic example of a recursive function that needs a more complex {tech}[measure] is the Ackermann function:

```lean (keep := false)
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
```

The measure is a tuple, so every recursive call has to be on arguments that are lexicographically smaller than the parameters.
The default {tactic}`decreasing_tactic` can handle this.

In particular, note that the third recursive call has a second argument that is smaller than the second parameter and a first argument that is definitionally equal to the first parameter.
This allowed  {tactic}`decreasing_tactic` to apply {name}`Prod.Lex.right`.

```signature
Prod.Lex.right {α β} {ra : α → α → Prop} {rb : β → β → Prop}
  (a : α) {b₁ b₂ : β}
  (h : rb b₁ b₂) :
  Prod.Lex ra rb (a, b₁) (a, b₂)
```

It fails, however, with the following modified function definition, where the third recursive call's first argument is provably smaller or equal to the first parameter, but not syntactically equal:

```lean (keep := false) (error := true) (name := synack)
def synack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => synack m 1
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

Because {name}`Prod.Lex.right` is not applicable, the tactic used {name}`Prod.Lex.left`, which resulted in the unprovable goal above.

This function definition may require a manual proof that uses the more general theorem {name}`Prod.Lex.right'`, which allows the first component of the tuple (which must be of type {name}`Nat`) to be less or equal instead of strictly equal:
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

The {tactic}`decreasing_tactic` tactic does not use the stronger {name}`Prod.Lex.right'` because it would require backtracking on failure.

:::

# Inferring Well-Founded Recursion
%%%
tag := "inferring-well-founded-recursion"
%%%

If a recursive function definition does not indicate a termination {tech}[measure], Lean will attempt to discover one automatically.
If neither {keywordOf Lean.Parser.Command.declaration}`termination_by` nor {keywordOf Lean.Parser.Command.declaration}`decreasing_by` is provided, Lean will try to {ref "inferring-structural-recursion"}[infer structural recursion] before attempting well-founded recursion.
If a {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause is present, only well-founded recursion is attempted.

To infer a suitable termination {tech}[measure], Lean considers multiple {deftech}_basic termination measures_, which are termination measures of type {name}`Nat`, and then tries all tuples of these measures.

The basic termination measures considered are:

* all parameters whose type have a non-trivial {name}`SizeOf` instance
* the expression `e₂ - e₁` whenever the local context of a recursive call has an assumption of type `e₁ < e₂` or `e₁ ≤ e₂`, where `e₁` and `e₂` are of type {name}`Nat` and depend only on the function's parameters. {margin}[This approach is based on work by {citehere manolios2006}[].]
* in a mutual group, an additional basic measure is used to distinguish between recursive calls to other functions in the group and recursive calls to the function being defined (for details, see {ref "mutual-well-founded-recursion"}[the section on mutual well-founded recursion])

{deftech}_Candidate measures_ are basic measures or tuples of basic measures.
If any of the candidate measures allow all proof obligations to be discharged by the termination proof tactic (that is, the tactic specified by {keywordOf Lean.Parser.Command.declaration}`decreasing_by`, or {tactic}`decreasing_trivial` if there is no {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause), then an arbitrary such candidate measure is selected as the automatic termination measure.

A {keyword}`termination_by?` clause causes the inferred termination annotation to be shown.
It can be automatically added to the source file using the offered suggestion or code action.

To avoid the combinatorial explosion of trying all tuples of measures, Lean first tabulates all {tech}[basic termination measures], determining whether the basic measure is decreasing, strictly decreasing, or non-decreasing.
A decreasing measure is smaller for at least one recursive call and never increases at any recursive call, while a strictly decreasing measure is smaller at all recursive calls.
A non-decreasing measure is one that the termination tactic could not show to be decreasing or strictly decreasing.
A suitable tuple is chosen based on the table.{margin}[This approach is based on {citehere bulwahn2007}[].]
This table shows up in the error message when no automatic measure could be found.

{spliceContents Manual.RecursiveDefs.WF.GuessLexExample}

```lean (show := false)
section
variable {e₁ e₂ i j : Nat}
```
:::example "Array Indexing"

The purpose of considering expressions of the form {lean}`e₂ - e₁` as measures is to support the common idiom of counting up to some upper bound, in particular when traversing arrays in possibly interesting ways.
In the following function, which performs binary search on a sorted array, this heuristic helps Lean to find the {lean}`j - i` measure.

```lean (name := binarySearch)
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

The fact that the inferred termination argument uses some arbitrary measure, rather than an optimal or minimal one, is visible in the inferred measure, which contains a redundant `j`:
```leanOutput binarySearch
Try this: termination_by (j, j - i)
```

:::

```lean (show := false)
end
```

:::example "Termination Proof Tactics During Inference"

The tactic indicated by {keywordOf Lean.Parser.Command.declaration}`decreasing_by` is used slightly differently when inferring the termination {tech}[measure] than it is in the actual termination proof.

* During inference, it is applied to a _single_ goal, attempting to prove {name LT.lt}`<` or {name LE.le}`≤` on {name}`Nat`.
* During the termination proof, it is applied to many simultaneous goals (one per recursive call), and the goals may involve the lexicographic ordering of pairs.

A consequence is that a {keywordOf Lean.Parser.Command.declaration}`decreasing_by` block that addresses goals individually and which works successfully with an explicit termination argument can cause inference of the termination measure to fail:

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

Because {tactic}`decreasing_tactic` avoids the need to backtrack by being incomplete with regard to lexicographic ordering, Lean may infer a termination {tech}[measure] that leads to goals that the tactic cannot prove.
In this case, the error message is the one that results from the failing tactic rather than the one that results from being unable to find a measure.
This is what happens in {lean}`notAck`:

```lean (error := true) (name := badInfer)
def notAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => notAck m 1
  | m + 1, n + 1 => notAck m (notAck (m / 2 + 1) n)
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

In this case, explicitly stating the termination {tech}[measure] helps.

:::

# Mutual Well-Founded Recursion
%%%
tag := "mutual-well-founded-recursion"
%%%

Lean supports the definition of {tech}[mutually recursive] functions using {tech}[well-founded recursion].
Mutual recursion may be introduced using a {tech}[mutual block], but it also results from {keywordOf Lean.Parser.Term.letrec}`let rec` expressions and {keywordOf Lean.Parser.Command.declaration}`where` blocks.
The rules for mutual well-founded recursion are applied to a group of actually mutually recursive, lifted definitions, that results from the {ref "mutual-syntax"}[elaboration steps] for mutual groups.

If any function in the mutual group has a {keywordOf Lean.Parser.Command.declaration}`termination_by` or {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause, well-founded recursion is attempted.
If a termination {tech}[measure] is specified using {keywordOf Lean.Parser.Command.declaration}`termination_by` for _any_ function in the mutual group, then _all_ functions in the group must specify a termination measure, and they have to have the same type.

If no termination argument is specified, the termination argument is {ref "inferring-well-founded-recursion"}[inferred, as described above]. In the case of mutual recursion, a third class of basic measures is considered during inference, namely for each function in the mutual group the measure that is `1` for that function and `0` for the others. This allows Lean to order the functions so that some calls from one function to another are allowed even if the parameters do not decrease.

:::example "Mutual recursion without parameter decrease"

In the following mutual function definitions, the parameter does not decrease in the call from {lean}`g` to {lean}`f`.
Nonetheless, the definition is accepted due to the ordering imposed on the functions themselves by the additional basic measure.

```lean (name := fg)
mutual
  def f : (n : Nat) → Nat
    | 0 => 0
    | n+1 => g n
  termination_by?

  def g (n : Nat) : Nat := (f n) + 1
  termination_by?
end
```

The inferred termination argument for {lean}`f` is:
```leanOutput fg
Try this: termination_by n => (n, 0)
```

The inferred termination argument for {lean}`g` is:
```leanOutput fg
Try this: termination_by (n, 1)
```

:::

# Theory and Construction

```lean (show := false)
section
variable {α : Type u}
```

This section gives a very brief glimpse into the mathematical constructions that underlie termination proofs via {tech}[well-founded recursion], which may surface occasionally.
The elaboration of functions defined by well-founded recursion is based on the {name}`WellFounded.fix` operator.

{docstring WellFounded.fix}

The type {lean}`α` is instantiated with the function's (varying) parameters, packed into one type using {name}`PSigma`.
The {name}`WellFounded` relation is constructed from the termination {tech}[measure] via {name}`invImage`.

{docstring invImage}

The function's body is passed to {name}`WellFounded.fix`, with parameters suitably packed and unpacked, and recursive calls are replaced with a call to the value provided by {name}`WellFounded.fix`.
The termination proofs generated by the {keywordOf Lean.Parser.Command.declaration}`decreasing_by` tactics are inserted in the right place.

Finally, the equational and unfolding theorems for the recursive function are proved from {name}`WellFounded.fix_eq`.
These theorems hide the details of packing and unpacking arguments and describe the function's behavior in terms of the original definition.

In the case of mutual recursion, an equivalent non-mutual function is constructed by combining the function's arguments using {name}`PSum`, and pattern-matching on that sum type in the result type and the body.

The definition of {name}`WellFounded` builds on the notion of _accessible elements_ of the relation:

{docstring WellFounded}

{docstring Acc}

::: example "Division by Iterated Subtraction: Termination Proof"

The definition of division by iterated subtraction can be written explicitly using well-founded recursion.
```lean
noncomputable def div (n k : Nat) : Nat :=
  (inferInstanceAs (WellFoundedRelation Nat)).wf.fix
    (fun n r =>
      if h : k = 0 then 0
      else if h : k > n then 0
      else 1 + (r (n - k) <| by
        show (n - k) < n
        omega))
    n
```
The definition must be marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` because well-founded recursion is not supported by the compiler.
Like {tech}[recursors], it is part of Lean's logic.

The definition of division should satisfy the following equations:
 * {lean}`∀{n k : Nat}, (k = 0) → div n k = 0`
 * {lean}`∀{n k : Nat}, (k > n) → div n k = 0`
 * {lean}`∀{n k : Nat}, (k ≠ 0) → (¬ k > n) → div n k = div (n - k) k`

This reduction behavior does not hold {tech key:="definitional equality"}[definitionally]:
```lean (error := true) (name := nonDef) (keep := false)
theorem div.eq0 : div n 0 = 0 := by rfl
```
```leanOutput nonDef
tactic 'rfl' failed, the left-hand side
  div n 0
is not definitionally equal to the right-hand side
  0
n : Nat
⊢ div n 0 = 0
```
However, using `WellFounded.fix_eq` to unfold the well-founded recursion, the three equations can be proved to hold:
```lean
theorem div.eq0 : div n 0 = 0 := by
  unfold div
  apply WellFounded.fix_eq

theorem div.eq1 : k > n → div n k = 0 := by
  intro h
  unfold div
  rw [WellFounded.fix_eq]
  simp only [gt_iff_lt, dite_eq_ite, ite_eq_left_iff, Nat.not_lt]
  intros; omega

theorem div.eq2 :
    ¬ k = 0 → ¬ (k > n) →
    div n k = 1 + div (n - k) k := by
  intros
  unfold div
  rw [WellFounded.fix_eq]
  simp_all only [
    gt_iff_lt, Nat.not_lt,
    dite_false, dite_eq_ite,
    ite_false, ite_eq_right_iff
  ]
  omega
```
:::
