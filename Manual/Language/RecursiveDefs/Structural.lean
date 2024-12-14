/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Verso.Genre Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option maxRecDepth 1500

#doc (Manual) "Structural Recursion" =>
%%%
tag := "structural-recursion"
%%%

Structurally recursive functions are those in which each recursive call is on a structurally smaller term than the argument.
Structural recursion is stronger than the primitive recursion that recursors provide, because the recursive call can use an _arbitrary_ sub-term of the argument, rather than only an immediate sub-term.
The constructions used to implement structural recursion are, however, implemented using the recursor; these helper constructions are described in the {ref "recursor-elaboration-helpers"}[section on inductive types].

```lean (show := false)
section
variable (n k : Nat) (mot : Nat → Sort u)
```
:::example "Recursion vs Recursors"
Addition of natural numbers can be defined via recursion on the second argument.
This function is straightforwardly structurally recursive.
```lean
def add (n : Nat) : Nat → Nat
  | .zero => n
  | .succ k => .succ (add n k)
```

Defined using {name}`Nat.rec`, it is much further from the notations that most people are used to.
```lean
def add' (n : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    n
    (fun k soFar => .succ soFar)
```

Structural recursive calls made on data that isn't the immediate child of the function parameter requires either creativity or a complex yet systematic encoding.
```lean
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
One way to think about this function is as a structural recursion that flips a bit at each call, only incrementing the result when the bit is set.
```lean
def helper : Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Bool → Nat)
    (fun _ => 0)
    (fun _ soFar =>
      fun b =>
        (if b then Nat.succ else id) (soFar !b))

def half' (n : Nat) : Nat := helper n false
```
```lean (name := halfTest)
#eval [0, 1, 2, 3, 4, 5, 6, 7, 8].map half'
```
```leanOutput halfTest
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

Instead of creativity, a general technique called {deftech}[course-of-values recursion] can be used.
Course-of-values recursion uses helpers that can be systematically derived for every inductive type, defined in terms of the recursor; Lean derives them automatically.
For every {lean}`Nat` {lean}`n`, the type {lean}`n.below (motive := mot)` provides a value of type {lean}`mot k` for all {lean}`k < n`, represented as an iterated {TODO}[xref sigma] dependent pair type.
The course-of-values recursor {name}`Nat.brecOn` allows a function to use the result for any smaller {lean}`Nat`.
Using it to define the function is inconvenient:
```lean
noncomputable def half'' (n : Nat) : Nat :=
  Nat.brecOn n (motive := fun _ => Nat)
    fun k soFar =>
      match k, soFar with
      | 0, _ | 1, _ => 0
      | _ + 2, ⟨_, ⟨h, _⟩⟩ => h + 1
```
The function is marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` because the compiler doesn't support generating code for course-of-values recursion, which is intended for reasoning rather that efficient code.
The kernel can still be used to test the function, however:
```lean (name := halfTest2)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest2
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

The dependent pattern matching in the body of {lean}`half''` can also be encoded using recursors (specifically, {name}`Nat.casesOn`), if necessary:
```lean
noncomputable def half''' (n : Nat) : Nat :=
  n.brecOn (motive := fun _ => Nat)
    fun k =>
      k.casesOn
        (motive :=
          fun k' =>
            (k'.below (motive := fun _ => Nat)) →
            Nat)
        (fun _ => 0)
        (fun k' =>
          k'.casesOn
            (motive :=
              fun k'' =>
                (k''.succ.below (motive := fun _ => Nat)) →
                Nat)
            (fun _ => 0)
            (fun _ soFar => soFar.2.1.succ))
```

This definition still works.
```lean (name := halfTest3)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest3
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

However, it is now far from the original definition and it has become difficult for most people to understand.
Recursors are an excellent logical foundation, but not an easy way to write programs or proofs.
:::
```lean (show := false)
end
```

Recognizing structural recursion involves the following steps:
 1. The function's parameters are divided into a _fixed prefix_ of parameters that do not vary in any recursive calls, and ordinary parameters that do.
 2. The ordinary parameters are split into groups of parameters that, together, may constitute a structurally decreasing parameter. In this step, indices are grouped with the arguments whose types depend on them.

The structural recursion analysis attempts to translate the recursive pre-definition into a use of the appropriate structural recursion constructions.
At this step, pattern matching has already been translated into the use of matcher functions; these are treated specially by the termination checker.
Next, for each group of parameters, a translation using `brecOn` is attempted.


:::example "Course-of-Values Tables"
This definition is equivalent to {name}`List.below`:
```lean
def List.below' {α : Type u} {motive : List α → Sort u} : List α → Sort (max 1 u)
  | [] => PUnit
  | _ :: xs => motive xs ×' xs.below' (motive := motive)
```

```lean (show := false)
theorem List.below_eq_below' : @List.below = @List.below' := by
  funext α motive xs
  induction xs <;> simp [List.below, below']
  congr
```

In other words, for a given {tech}[motive], {lean}`List.below'` is a type that contains a realization of the motive for all suffixes of the list.

More recursive arguments require further nested iterations of the product type.
For instance, binary trees have two recursive occurrences.
```lean
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)
```

It's corresponding course-of-values table contains the realizations of the motive for all subtrees:
```lean
def Tree.below' {α : Type u} {motive : Tree α → Sort u} : Tree α → Sort (max 1 u)
  | .leaf => PUnit
  | .branch left _val right =>
    motive left ×' motive right ×'
    left.below' (motive := motive) ×'
    right.below' (motive := motive)
```

```lean (show := false)
theorem Tree.below_eq_below' : @Tree.below = @Tree.below' := by
  funext α motive t
  induction t <;> simp [Tree.below, below']
  congr
```

For both lists and trees, the `brecOn` operator expects just a single case, rather than one per constructor.
This case accepts a list or tree along with a table of results for all smaller values; from this, it should satisfy the motive for the provided value.
Dependent case analysis of the provided value automatically refines the type of the memo table, providing everything needed.

The following definitions are equivalent to {name}`List.brecOn` and {name}`Tree.brecOn`, respectively.
The primitive recursive helpers {name}`List.brecOnTable`  and {name}`Tree.brecOnTable` compute the course-of-values tables along with the final results, and the actual definitions of the `brecOn` operators simply project out the result.
```lean
def List.brecOnTable {α : Type u}
    {motive : List α → Sort u}
    (xs : List α)
    (step :
      (ys : List α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive xs ×' xs.below' (motive := motive) :=
  match xs with
  | [] => ⟨step [] PUnit.unit, PUnit.unit⟩
  | x :: xs =>
    let res := xs.brecOnTable (motive := motive) step
    let val := step (x :: xs) res
    ⟨val, res⟩

def Tree.brecOnTable {α : Type u}
    {motive : Tree α → Sort u}
    (t : Tree α)
    (step :
      (ys : Tree α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive t ×' t.below' (motive := motive) :=
  match t with
  | .leaf => ⟨step .leaf PUnit.unit, PUnit.unit⟩
  | .branch left val right =>
    let resLeft := left.brecOnTable (motive := motive) step
    let resRight := right.brecOnTable (motive := motive) step
    let branchRes := ⟨resLeft.1, resRight.1, resLeft.2, resRight.2⟩
    let val := step (.branch left val right) branchRes
    ⟨val, branchRes⟩

def List.brecOn' {α : Type u}
    {motive : List α → Sort u}
    (xs : List α)
    (step :
      (ys : List α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive xs :=
  (xs.brecOnTable (motive := motive) step).1

def Tree.brecOn' {α : Type u}
    {motive : Tree α → Sort u}
    (t : Tree α)
    (step :
      (ys : Tree α) →
      ys.below' (motive := motive) →
      motive ys) :
    motive t :=
  (t.brecOnTable (motive := motive) step).1
```

```lean (show := false)
-- Proving the above-claimed equivalence is too time consuming, but evaluating a few examples will at least catch silly mistakes!

/--
info: fun motive x y z step =>
  step [x, y, z]
    ⟨step [y, z] ⟨step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩,
      step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩
-/
#guard_msgs in
#reduce fun motive x y z step => List.brecOn' (motive := motive) [x, y, z] step

/--
info: fun motive x y z step =>
  step [x, y, z]
    ⟨step [y, z] ⟨step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩,
      step [z] ⟨step [] PUnit.unit, PUnit.unit⟩, step [] PUnit.unit, PUnit.unit⟩
-/
#guard_msgs in
#reduce fun motive x y z step => List.brecOn (motive := motive) [x, y, z] step

/--
info: fun motive x z step =>
  step ((Tree.leaf.branch x Tree.leaf).branch z Tree.leaf)
    ⟨step (Tree.leaf.branch x Tree.leaf) ⟨step Tree.leaf PUnit.unit, step Tree.leaf PUnit.unit, PUnit.unit, PUnit.unit⟩,
      step Tree.leaf PUnit.unit, ⟨step Tree.leaf PUnit.unit, step Tree.leaf PUnit.unit, PUnit.unit, PUnit.unit⟩,
      PUnit.unit⟩
-/
#guard_msgs in
#reduce fun motive x z step => Tree.brecOn' (motive := motive) (.branch (.branch .leaf x .leaf) z .leaf) step

/--
info: fun motive x z step =>
  step ((Tree.leaf.branch x Tree.leaf).branch z Tree.leaf)
    ⟨⟨step (Tree.leaf.branch x Tree.leaf)
          ⟨⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
        ⟨step Tree.leaf PUnit.unit, PUnit.unit⟩, step Tree.leaf PUnit.unit, PUnit.unit⟩,
      step Tree.leaf PUnit.unit, PUnit.unit⟩
-/
#guard_msgs in
#reduce fun motive x z step => Tree.brecOn (motive := motive) (.branch (.branch .leaf x .leaf) z .leaf) step
```

:::

The `below` construction is a mapping from each value of a type to the results of some function call on _all_ smaller values; it can be understood as a memoization table that already contains the results for all smaller values.
Recursors expect an argument for each of the inductive type's constructors; these arguments are called with the constructor's arguments (and the result of recursion on recursive parameters) during {tech}[ι-reduction].
The course-of-values recursion operator `brecOn`, on the other hand, expects just a single case that covers all constructors at once.
This case is provided with a value and a `below` table that contains the results of recursion on all values smaller than the given value; it should use the contents of the table to satisfy the motive for the provided value.
If the function is structurally recursive over a given parameter (or parameter group), then the results of all recursive calls will be present in this table already.

When the body of the recursive function is transformed into an invocation of `brecOn` on one of the function's parameters, the parameter and its course-of-values table are in scope.
The analysis traverses the body of the function, looking for recursive calls.
If the parameter is matched against, then its occurrences in the local context are {ref "match-generalization"}[generalized] and then instantiated with the pattern; this is also true for the type of the course-of-values table.
Typically, this pattern matching results in the type of the course-of-values table becoming more specific, which gives access to the recursive results for smaller values.
When an recursive occurrence of the function is detected, the course-of-values table is consulted to see whether it contains a result for the argument being checked.
If so, the recursive call can be replaced with a projection from the table.
If not, then the parameter in question doesn't support structural recursion.

```lean (show := false)
section
```

:::example "Elaboration Walkthrough"
The first step in walking through the elaboration of {name}`half` is to manually desugar it to a simpler form.
This doesn't match the way Lean works, but its output is much easier to read when there are fewer {name}`OfNat` instances present.
This readable definition:
```lean (keep := false)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
can be rewritten to this somewhat lower-level version:
```lean (keep := false)
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```

The elaborator begins by elaborating a pre-definition in which recursion is still present but the definition is otherwise in Lean's core type theory.
Turning on the compiler's tracing of pre-definitions, as well as making the pretty printer more explicit, makes the resulting pre-definition visible:
```lean (keep := false) (show := false)
-- Test of next block - visually check correspondence when updating!
set_option trace.Elab.definition.body true in
set_option pp.all true in

/--
info: [Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x (fun (_ : Unit) => Nat.zero) (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
-/
#guard_msgs in
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
```lean (name := tracedHalf)
set_option trace.Elab.definition.body true in
set_option pp.all true in

def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
The returned trace message is:{TODO}[Trace not showing up in serialized info - figure out why so this test can work better, or better yet, add proper trace rendering to Verso]
```
[Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x
        (fun (_ : Unit) => Nat.zero)
        (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
```
The auxiliary match function's definition is:
```lean (name := halfmatch)
#print half.match_1
```
```leanOutput halfmatch (whitespace := lax)
def half.match_1.{u_1} :
    (motive : Nat → Sort u_1) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
Formatted more readably, this definition is:
```lean
def half.match_1'.{u} :
    (motive : Nat → Sort u) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
In other words, the specific configuration of patterns used in {name}`half` are captured in {name}`half.match_1`.

This definition is a more readable version of {name}`half`'s pre-definition:
```lean
def half' : Nat → Nat :=
  fun (x : Nat) =>
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
```

To elaborate it as a structurally recursive function, the first step is to establish the `bRec` invocation.
The definition must be marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` because Lean does not support code generation for recursors such as {name}`Nat.brecOn`.
```lean (error := true) (keep := false)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      _
/- To translate:
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```

The next step is to replace occurrences of `x` in the original function body with the `n` provided by {name Nat.brecOn}`brecOn`.
Because `table`'s type depends on `x`, it must also be generalized when splitting cases with {name}`half.match_1`, leading to a motive with an extra parameter.

```lean (error := true) (keep := false) (name := threeCases)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        _
        _
        _)
      table
/- To translate:
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```
The three cases' placeholders expect the following types:
```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_1'
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) Nat.zero
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_2'
context:
x n : Nat
table : Nat.below n
⊢ Unit → (fun k => Nat.below k → Nat) 1
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument 'h_3'
context:
x n : Nat
table : Nat.below n
⊢ (n : Nat) → (fun k => Nat.below k → Nat) n.succ.succ
```

The first two cases in the pre-definition are constant functions, with no recursion to check:

```lean (error := true) (keep := false) (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        _)
      table
/- To translate:
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```

The final case contains a recursive call.
It should be translated into a lookup into the course-of-values table.
A more readable representation of the last hole's type is:
```leanTerm
(n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat
```
which is equivalent to
```leanTerm
(n : Nat) →
Nat ×' Nat ×' Nat.below (motive := fun _ => Nat) n →
Nat
```

```lean (show := false)
example : ((n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat) = ((n : Nat) →
Nat ×' Nat ×' Nat.below (motive := fun _ => Nat) n →
Nat) := rfl
```

```lean (show := false)

variable {n : Nat}
```

The first {lean}`Nat` in the course-of-values table is the result of recursion on {lean}`n + 1`, and the second is the result of recursion on {lean}`n`.
The recursive call can thus be replaced by a lookup, and the elaboration is successful:

```lean (error := true) (keep := false) (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        (fun _ table => Nat.succ table.2.1)
      table
```

The actual elaborator keeps track of the relationship between the parameter being checked for structural recursion and the positions in the course-of-values tables by inserting sentinel types with fresh names into the motive.
:::

```lean (show := false)
end
```

For structural recursion to be detected, a parameter to the function must syntactically be a discriminant of a {keywordOf Lean.Parser.Term.match}`match`.
This maintains the connection between the discriminant and the function parameter, allowing the course-of-values table to line up with the subterms of the original argument.
This connection is checked syntactically: even simple transformations such as wrapping a discriminant and every pattern that matches it with {lean}`(·, ())` can cause elaboration to fail.
The generalization step that constructs a suitable motive for the auxiliary matchers searches for *exact occurrences of the discriminant* in the context.


```lean (show := false)
section
variable (n : Nat)
```

:::example "Failing Elaboration"
This definition of {lean}`half` terminates, but this can't be checked by either structural or well-founded recursion.
This is because the gratuitous tuple in the {tech}[match discriminant] breaks the connection between {lean}`n` and the patterns that match it.
```lean (error := true) (name := badhalfmatch) (keep := false)
def half (n : Nat) : Nat :=
  match (n, ()) with
  | (0, ()) | (1, ()) => 0
  | (n' + 2, ()) => half n' + 1
```
```leanOutput badhalfmatch
fail to show termination for
  half
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    half n'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n n' : Nat
⊢ n' < n
```

The generalization step that constructs the motive for the auxiliary match functions doesn't connect {lean}`n` to its patterns, so the course-of-values table doesn't contain a suitable result of recursion.
Similarly, well-founded recursion lacks the connection between the function's parameter and the pattern, though this can be fixed by adding a proposition to the context that states their equality.
This extra information allows the proof automation for well-founded recursion to succeed.

```lean
def half (n : Nat) : Nat :=
  match h : (n, ()) with
  | (0, ()) | (1, ()) => 0
  | (n' + 2, ()) =>
    -- Here, h : (n, ()) = (n' + 2, ())
    have : n = n' + 2 := by simp_all
    half n' + 1
```
:::


```lean (show := false)
end
```

# Matching Pairs vs Simultaneous Matching

An important consequence of the strategies that are used to prove termination is that *simultaneous matching of two discriminants is not equivalent to matching a pair*.
Simultaneous matching maintains the connection between the discriminants and the patterns, allowing the pattern matching to refine the types of the assumptions in the local context as well as the expected type of the {keywordOf Lean.Parser.Term.match}`match`.
Essentially, the elaboration rules for {keywordOf Lean.Parser.Term.match}`match` treat the discriminants specially, and changing discriminants in a way that preserves the run-time meaning of a program does not necessarily preserve the compile-time meaning.

:::example "Simultaneous Matching vs Matching Pairs for Structural Recursion"
This function that finds the minimum of two natural numbers is defined by structural recursion on its first parameter:
```lean
def min (n k : Nat) : Nat :=
  match n, k with
  | 0, _ => 0
  | _, 0 => 0
  | n' + 1, k' + 1 => min n' k' + 1
termination_by structural n
```

Replacing the simultaneous pattern match on both parameters with a match on a pair causes termination analysis to fail:
```lean (error := true) (name := noMin)
def min' (n k : Nat) : Nat :=
  match (n, k) with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' n' k' + 1
termination_by structural n
```
```leanOutput noMin
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    min' n' k'
```

This is because the analysis only considers direct pattern matching on parameters when matching recursive calls to strictly-smaller argument values.
Wrapping the discriminants in a pair breaks the connection.
:::

:::example "No Structural Recursion Over Pair Components"
This function that finds the minimum of the two components of a pair can't be elaborated via structural recursion.
```lean
def min (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min (n', k') + 1
termination_by structural nk
```
This is because the parameter's type's course-of-values recursor is used to justify the recursive definition, but the product type {name}`Prod` is not recursive and thus does not have a course-of-values recursor.
This definition is accepted using {tech}[well-founded recursion], however:
```lean
def min (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min (n', k') + 1
termination_by mk
```
:::




# Mutual Structural Recursion

::: planned 56
This section will describe the specification of the translation to recursors.
:::
