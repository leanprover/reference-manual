/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Language.RecursiveDefs.Structural.RecursorExample
import Manual.Language.RecursiveDefs.Structural.CourseOfValuesExample

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Structural Recursion" =>
%%%
tag := "structural-recursion"
%%%

Structurally recursive functions are those in which each recursive call is on a structurally smaller term than the argument.
Structural recursion is stronger than the primitive recursion that recursors provide, because the recursive call can use more deeply nested sub-terms of the argument, rather than only an immediate sub-term.
The constructions used to implement structural recursion are, however, implemented using the recursor; these helper constructions are described in the {ref "recursor-elaboration-helpers"}[section on inductive types].

# Explicit structural recursion

To explicitly use structural recursion, a function definition can be annotated with a `termination_by structural` clause specifying the *decreasing parameter*:

```lean (keep := false)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n => n
```
:::syntax Lean.Parser.Termination.terminationBy

The grammar of the `termination_by structural` clause is

```grammar
termination_by structural $[$_:ident* =>]? $term
```
where the identifiers before the optional `=>` can bring function parameters into scope that are not
already bound in the declaration header, and the `$term` must elaborate to one of the functions parameters.
:::

The type of the selected decreasing parameter must be an {tech}[inductive type]. If it is an indexed family, then all indices must be parameters of the function.

:::example "Ineligible decreasing parameters"

The decreasing parameter must have inductive type:

```lean (error := true) (name := badnoindct) (keep := false)
def bad (x : Nat → Nat) : Nat := bad (fun n => x (n+1))
termination_by structural x
```
```leanOutput badnoindct
cannot use specified parameter for structural recursion:
  its type is not an inductive
```

If the decreasing parameter is an indexed family, all the indices must be variables:
```lean (error := true) (name := badidx) (keep := false)
inductive Fin' : Nat → Type where
  | zero : Fin' (n+1)
  | succ : Fin' n → Fin' (n+1)

def bad (x : Fin' 100) : Nat := bad .zero
termination_by structural x
```
```leanOutput badidx
cannot use specified parameter for structural recursion:
  its type Fin' is an inductive family and indices are not variables
    Fin' 100
```
:::

Furthermore, every recursive call of the functions must be on a *strict* sub-term of the decreasing
parameter. The rules are as follows:

* The decreasing parameter itself is a (non-strict) sub-term.
* If a sub-term is the target of a `match` statement, then the pattern matched against that target is a sub-term.
* If a sub-term is a constructor applied to arguments, then its recursive arguments are strict sub-terms.

In the following example, the decreasing parameter `n` is matched against the nested pattern `.succ (.succ n)`. Therefore `.succ (.succ n)` is a (non-strict) sub-term of `n`, and consequently  both `n` and `.succ n` are strict sub-terms, and the definition is accepted.

```lean (keep := false)
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) =>  fib n + fib (.succ n)
termination_by structural n => n
```

Note that for clarity, this example uses `.succ n` and `.succ (.succ n)` instead of the equivalent `Nat`-specific `n+1` and `n+2`.

:::TODO
Link to where this special syntax is documented.
:::

:::example "Matching on Complex Expressions Can Prevent Elaboration"

In the following example, the decreasing parameter `n` is not directly the target of the `match` statement. Therefore, `n'` is not considered a subterm and the elaboration fails.

```lean (error := true) (name := badtarget) (keep := false)
def half (n : Nat) : Nat :=
  match Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by structural n
```
```leanOutput badtarget
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    half n'
```

Using {tech}[well-founded recursion], and explicitly connecting the target to the pattern of the match, this definition can be accepted.

```lean (keep := false)
def half (n : Nat) : Nat :=
  match h : Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by n
decreasing_by simp_all; omega
```

Similarly, the following example fails: Although `tail xs` would reduce to a strict sub-term of `xs`, this is not visible to lean according to the rules above.

```lean (error := true) (keep := false)
def listLen : List α → Nat
  | [] => 0
  | xs => listLen xs.tail + 1
termination_by structural xs => xs
```

:::


:::example "Simultaneous Matching vs Matching Pairs for Structural Recursion"

An important consequence of the strategies that are used to prove termination is that *simultaneous matching of two discriminants is not equivalent to matching a pair*.
Simultaneous matching maintains the connection between the discriminants and the patterns, allowing the pattern matching to refine the types of the assumptions in the local context as well as the expected type of the {keywordOf Lean.Parser.Term.match}`match`.
Essentially, the elaboration rules for {keywordOf Lean.Parser.Term.match}`match` treat the discriminants specially, and changing discriminants in a way that preserves the run-time meaning of a program does not necessarily preserve the compile-time meaning.

This function that finds the minimum of two natural numbers is defined by structural recursion on its first parameter:
```lean (keep := false)
def min' (n k : Nat) : Nat :=
  match n, k with
  | 0, _ => 0
  | _, 0 => 0
  | n' + 1, k' + 1 => min' n' k' + 1
termination_by structural n
```

Replacing the simultaneous pattern match on both parameters with a match on a pair causes termination analysis to fail:
```lean (error := true) (name := noMin) (keep := false)
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

This function that finds the minimum of the two components of a pair can't be elaborated via structural recursion.
```lean (keep := false) (error := true) (name := minpair)
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by structural nk
```
```leanOutput minpair
failed to infer structural recursion:
Cannot use parameter nk:
  the type Nat × Nat does not have a `.brecOn` recursor
```

This is because the parameter's type, {name}`Prod`, is not recursive and thus its constructor has no recursive parameters that can be exposed by pattern-matching.

This definition is accepted using {tech}[well-founded recursion], however:
```lean (keep := false)
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by nk
```
:::

# Mutual structural recursion

TODO

# Inferring structural recursion

TODO

# Elaboration using course-of-value recursion

In this section, the construction used to elaborate structurally recursive functions is explained in more detail.

{spliceContents Manual.Language.RecursiveDefs.Structural.RecursorExample}

The structural recursion analysis attempts to translate the recursive pre-definition into a use of the appropriate structural recursion constructions.
At this step, pattern matching has already been translated into the use of matcher functions; these are treated specially by the termination checker.
Next, for each group of parameters, a translation using `brecOn` is attempted.

{spliceContents Manual.Language.RecursiveDefs.Structural.CourseOfValuesExample}

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

::: planned 56
The construction for mutually recursive functions ought to be explained here.
:::
