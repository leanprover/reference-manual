/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Joachim Breitner
-/

import VersoManual
import Manual.RecursiveDefs.Structural.RecursorExample
import Manual.RecursiveDefs.Structural.CourseOfValuesExample

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
The same parameter must decrease in all recursive calls; this parameter is called the {deftech}_decreasing parameter_.
Structural recursion is stronger than the primitive recursion that recursors provide, because the recursive call can use more deeply nested sub-terms of the argument, rather than only an immediate sub-term.
The constructions used to implement structural recursion are, however, implemented using the recursor; these helper constructions are described in the {ref "recursor-elaboration-helpers"}[section on inductive types].

The rules that govern structural recursion are fundamentally _syntactic_ in nature.
There are many recursive definitions that exhibit structurally recursive computational behavior, but which are not accepted by these rules; this is a fundamental consequence of the analysis being fully automatic.
{tech}[Well-founded recursion] provides a semantic approach to demonstrating termination that can be used in situations where a recursive function is not structurally recursive, but it can also be used when a function that computes according to structural recursion doesn't satisfy the syntactic requirements.

```lean (show := false)
section
variable (n n' : Nat)
```
:::example "Structural Recursion vs Subtraction"
The function {lean}`countdown` is structurally recursive.
The parameter {lean}`n` was matched against the pattern {lean}`n' + 1`, which means that {lean}`n'` is a direct subterm of {lean}`n` in the second branch of the pattern match:
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown n'
```

Replacing pattern matching with an equivalent Boolean test and subtraction results in an error:
```lean (error := true) (name := countdown') (keep := false)
def countdown' (n : Nat) : List Nat :=
  if n == 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```
```leanOutput countdown'
fail to show termination for
  countdown'
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' n'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 0) = true
n' : Nat := n - 1
⊢ n - 1 < n
```
This is because there was no pattern matching on the parameter {lean}`n`.
While this function indeed terminates, the argument that it does so is based on properties of if, the equality test, and subtraction, rather than being a generic feature of {lean}`Nat` being an {tech}[inductive type].
These arguments are expressed using {tech}[well-founded recursion], and a slight change to the function definition allows Lean's automatic support for well-founded recursion to construct an alternative termination proof.
This version branches on the decidability of propositional equality for {lean}`Nat` rather than the result of a Boolean equality test:

```lean
def countdown' (n : Nat) : List Nat :=
  if n = 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```

Here, Lean's automation automatically constructs a termination proof from facts about propositional equality and subtraction.
It uses well-founded recursion rather than structure recursion behind the scenes.
:::
```lean (show := false)
end
```

Structural recursion may be used explicitly or automatically.
With explicit structural recursion, the function definition declares which parameter is the {tech}[decreasing parameter].
If no termination strategy is explicitly declared, Lean performs a search for a decreasing parameter as well as a decreasing measure for use with {tech}[well-founded recursion].
Explicitly annotating structural recursion has the following benefits:
 * It can speed up elaboration, because no search occurs.
 * It documents the termination argument for readers.
 * In situations where structural recursion is explicitly desired, it prevents the accidental use of well-founded recursion.

# Explicit Structural Recursion

To explicitly use structural recursion, a function or theorem definition can be annotated with a {keywordOf Lean.Parser.Command.declaration}`termination_by structural` clause that specifies the {tech}[decreasing parameter].
The decreasing parameter may be a reference to a parameter named in the signature.
When the signature specifies a function type, the decreasing parameter may additionally be a parameter not named in the signature; in this case, names for the remaining parameters may be introduced by writing them before an arrow ({keywordOf Lean.Parser.Command.declaration}`=>`).

:::example "Specifying Decreasing Parameters"

When the decreasing parameter is a named parameter to the function, it can be specified by referring to its name.

```lean (keep := false)
def half (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n
```

When the decreasing parameter is not named in the signature, a name can be introduced locally in the {keywordOf Lean.Parser.Command.declaration}`termination_by` clause.

```lean (keep := false)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n => n
```
:::

:::syntax Lean.Parser.Termination.terminationBy (title := "Explicit Structural Recursion")

The `termination_by structural` clause introduces a decreasing parameter.

```grammar
termination_by structural $[$_:ident* =>]? $term
```

The identifiers before the optional `=>` can bring function parameters into scope that are not
already bound in the declaration header, and the mandatory term must indicate one of the function's parameters, whether introduced in the header or locally in the clause.
:::

The decreasing parameter must satisfy the following conditions:

* Its type must be an {tech}[inductive type].

* If its type is an {tech}[indexed family], then all indices must be parameters of the function.

* If the inductive or indexed family of the decreasing parameter has data type parameters, then these data type parameters may themselves only depend on function parameters that are part of the {tech}[fixed prefix].

A {deftech}_fixed parameter_ is a function parameter that is passed unmodified in all recursive calls and is not an index of the recursive parameter's type.
The {deftech}_fixed prefix_ is the longest prefix of the function's parameters in which all are fixed.

:::example "Ineligible decreasing parameters"

The decreasing parameter's type must be an inductive type.
In {lean}`notInductive`, a function is specified as the decreasing parameter:

```lean (error := true) (name := badnoindct)
def notInductive (x : Nat → Nat) : Nat := notInductive (fun n => x (n+1))
termination_by structural x
```
```leanOutput badnoindct
cannot use specified parameter for structural recursion:
  its type is not an inductive
```

If the decreasing parameter is an indexed family, all the indices must be variables.
In {lean}`constantIndex`, the indexed family {lean}`Fin'` is instead applied to a constant value:

```lean (error := true) (name := badidx)
inductive Fin' : Nat → Type where
  | zero : Fin' (n+1)
  | succ : Fin' n → Fin' (n+1)

def constantIndex (x : Fin' 100) : Nat := constantIndex .zero
termination_by structural x
```
```leanOutput badidx
cannot use specified parameter for structural recursion:
  its type Fin' is an inductive family and indices are not variables
    Fin' 100
```

The parameters of the decreasing parameter's type must not depend on function parameters that come after varying parameters or indices.
In {lean}`afterVarying`, the {tech}[fixed prefix] is empty, because the first parameter `n` varies, so `p` is not part of the fixed prefix:

```lean (error := true) (name := badparam)
inductive WithParam' (p : Nat) : Nat → Type where
  | zero : WithParam' p (n+1)
  | succ : WithParam' p n → WithParam' p (n+1)

def afterVarying (n : Nat) (p : Nat) (x : WithParam' p n) : Nat :=
  afterVarying (n+1) p .zero
termination_by structural x
```
```leanOutput badparam
cannot use specified parameter for structural recursion:
  its type is an inductive datatype
    WithParam' p n
  and the datatype parameter
    p
  depends on the function parameter
    p
  which does not come before the varying parameters and before the indices of the recursion parameter.
```
:::

Furthermore, every recursive call of the functions must be on a {deftech}_strict sub-term_ of the decreasing
parameter.

 * The decreasing parameter itself is a sub-term, but not a strict sub-term.
 * If a sub-term is the {tech key:="match discriminant"}[discriminant] of a {keywordOf Lean.Parser.Term.match}`match` expression or other pattern-matching syntax, the pattern that matches the discriminant is a sub-term in the {tech}[right-hand side] of each {tech}[match alternative].
   In particular, the rules of {ref "match-generalization"}[match generalization] are used to connect the discriminant to the occurrences of the pattern term in the right-hand side; thus, it respects {tech}[definitional equality].
   The pattern is a _strict_ sub-term if and only if the discriminant is a strict sub-term.
 * If a sub-term is a constructor applied to arguments, then its recursive arguments are strict sub-terms.

```lean (show := false)
section
variable (n : Nat)
```
::::example "Nested Patterns and Sub-Terms"

In the following example, the decreasing parameter {lean}`n` is matched against the nested pattern {lean type:="Nat"}`.succ (.succ n)`. Therefore {lean type:="Nat"}`.succ (.succ n)` is a (non-strict) sub-term of {lean type:="Nat"}`n`, and consequently  both {lean type:="Nat"}`n` and {lean type:="Nat"}`.succ n` are strict sub-terms, and the definition is accepted.

```lean
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) =>  fib n + fib (.succ n)
termination_by structural n => n
```

For clarity, this example uses {lean type:="Nat"}`.succ n` and {lean type:="Nat"}`.succ (.succ n)` instead of the equivalent {lean}`Nat`-specific {lean}`n+1` and {lean}`n+2`.

:::TODO
Link to where this special syntax is documented.
:::

::::
```lean (show := false)
end
```

```lean (show := false)
section
variable {α : Type u} (n n' : Nat) (xs : List α)
```
:::example "Matching on Complex Expressions Can Prevent Elaboration"

In the following example, the decreasing parameter {lean}`n` is not directly the {tech key:="match discriminant"}[discriminant] of the {keywordOf Lean.Parser.Term.match}`match` expression.
Therefore, {lean}`n'` is not considered a sub-term of {lean}`n`.

```lean (error := true) (keep := false) (name := badtarget)
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

Using {tech}[well-founded recursion], and explicitly connecting the discriminant to the pattern of the match, this definition can be accepted.

```lean
def half (n : Nat) : Nat :=
  match h : Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by n
decreasing_by simp_all; omega
```

Similarly, the following example fails: although {lean}`xs.tail` would reduce to a strict sub-term of {lean}`xs`, this is not visible to Lean according to the rules above.
In particular, {lean}`xs.tail` is not {tech key:="definitional equality"}[definitionally equal] to a strict sub-term of {lean}`xs`.

```lean (error := true) (keep := false)
def listLen : List α → Nat
  | [] => 0
  | xs => listLen xs.tail + 1
termination_by structural xs => xs
```

:::
```lean (show := false)
end
```


:::example "Simultaneous Matching vs Matching Pairs for Structural Recursion"

An important consequence of the strategies that are used to prove termination is that *simultaneous matching of two {tech key:="match discriminant"}[discriminants] is not equivalent to matching a pair*.
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

:::example "Structural Recursion Under Pairs"

This function that finds the minimum of the two components of a pair can't be elaborated via structural recursion.
```lean (error := true) (name := minpair)
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

This is because the parameter's type, {name}`Prod`, is not recursive.
Thus, its constructor has no recursive parameters that can be exposed by pattern matching.

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

```lean (show := false)
section
variable (n n' : Nat)
```
:::example "Structural Recursion and Definitional Equality"

Even though the recursive occurrence of {lean}`countdown` is applied to a term that is not a strict sub-term of the decreasing parameter, the following definition is accepted:
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown (n' + 0)
termination_by structural n
```

This is because {lean}`n' + 0` is {tech key:="definitional equality"}[definitionally equal] to {lean}`n'`, which is a strict sub-term of {lean}`n`.
{tech key:="strict sub-term"}[Sub-terms] that result from pattern matching are connected to the {tech key:="match discriminant"}[discriminant] using the rules for {ref "match-generalization"}[match generalization], which respect definitional equality.

In {lean}`countdown'`, the recursive occurrence is applied to {lean}`0 + n'`, which is not definitionally equal to `n'` because addition on natural numbers is structurally recursive in its second parameter:
```lean (error := true) (name := countdownNonDefEq)
def countdown' (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown' (0 + n')
termination_by structural n
```
```leanOutput countdownNonDefEq
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' (0 + n')
```

:::
```lean (show := false)
end
```

# Mutual Structural Recursion
%%%
tag := "mutual-structural-recursion"
%%%

Lean supports the definition of {tech}[mutually recursive] functions using structural recursion.
Mutual recursion may be introduced using a {tech}[mutual block], but it also results from {keywordOf Lean.Parser.Term.letrec}`let rec` expressions and {keywordOf Lean.Parser.Command.declaration}`where` blocks.
The rules for mutual structural recursion are applied to a group of actually mutually recursive, lifted definitions, that results from the {ref "mutual-syntax"}[elaboration steps] for mutual groups.
If every function in the mutual group has a {keyword}`termination_by structural` annotation indicating that function’s decreasing argument, then structural recursion is used to translate the definitions.

The requirements on the decreasing argument above are extended:

 * All the types of all the decreasing arguments must be from the same inductive type, or more generally from the same {ref "mutual-inductive-types"}[mutual group of inductive types].

 * The parameters of the decreasing parameter's types must be the same for all functions, and may depend only on the _common_ fixed prefix of function arguments.

The functions do not have to be in a one-to-one correspondence to the mutual inductive types.
Multiple functions can have a decreasing argument of the same type, and not all types that are mutually recursive with the decreasing argument need have a corresponding function.

:::example "Mutual Structural Recursion Over Non-Mutual Types"

The following example demonstrates mutual recursion over a non-mutual inductive data type:

```lean
mutual
  def even : Nat → Prop
    | 0 => True
    | n+1 => odd n
  termination_by structural n => n

  def odd : Nat → Prop
    | 0 => False
    | n+1 => even n
  termination_by structural n => n
end
```
:::

:::example "Mutual Structural Recursion Over Mutual Types"

The following example demonstrates recursion over mutually inductive types.
The functions {lean}`Exp.size` and {lean}`App.size` are mutually recursive.

```lean
mutual
  inductive Exp where
    | var : String → Exp
    | app : App → Exp

  inductive App where
    | fn : String → App
    | app : App → Exp → App
end

mutual
  def Exp.size : Exp → Nat
    | .var _ => 1
    | .app a => a.size
  termination_by structural e => e

  def App.size : App → Nat
    | .fn _ => 1
    | .app a e => a.size + e.size + 1
  termination_by structural a => a
end
```

The definition of {lean}`App.numArgs` is structurally recursive over type {lean}`App`.
It demonstrates that not all inductive types in the mutual group need to be handled.

```lean
def App.numArgs : App → Nat
  | .fn _ => 0
  | .app a _ => a.numArgs + 1
termination_by structural a => a
```

:::

:::planned 235

Describe mutual structural recursion over {ref "nested-inductive-types"}[nested inductive types].

:::


# Inferring Structural Recursion
%%%
tag := "inferring-structural-recursion"
%%%


If no {keyword}`termination_by` clauses are present in a recursive or mutually recursive function definition, then Lean attempts to infer a suitable structurally decreasing argument, effectively by trying all suitable parameters in sequence.
If this search fails, Lean then attempts to infer {tech}[well-founded recursion].

For mutually recursive functions, all combinations of parameters are tried, up to a limit to avoid combinatorial explosion.
If only some of the mutually recursive functions have {keyword}`termination_by structural` clauses, then only those parameters are considered, while for the other functions all parameters are considered for structural recursion.

A {keyword}`termination_by?` clause causes the inferred termination annotation to be shown.
It can be automatically added to the source file using the offered suggestion or code action.

:::example "Inferred Termination Annotations"
Lean automatically infers that the function {lean}`half` is structurally recursive.
The {keyword}`termination_by?` clause causes the inferred termination annotation to be displayed, and it can be automatically added to the source file with a single click.

```lean (name := inferStruct)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by?
```
```leanOutput inferStruct
Try this: termination_by structural x => x
```
:::

# Elaboration Using Course-of-Values Recursion

In this section, the construction used to elaborate structurally recursive functions is explained in more detail.
This elaboration uses the {ref "recursor-elaboration-helpers"}[`below` and `brecOn` constructions] that are automatically generated from inductive types' recursors.

{spliceContents Manual.RecursiveDefs.Structural.RecursorExample}

The structural recursion analysis attempts to translate the recursive pre-definition into a use of the appropriate structural recursion constructions.
At this step, pattern matching has already been translated into the use of matcher functions; these are treated specially by the termination checker.
Next, for each group of parameters, a translation using `brecOn` is attempted.

{spliceContents Manual.RecursiveDefs.Structural.CourseOfValuesExample}

The `below` construction is a mapping from each value of a type to the results of some function call on _all_ smaller values; it can be understood as a memoization table that already contains the results for all smaller values.
The notion of “smaller value” that is expressed in the `below` construction corresponds directly to the definition of {tech}[strict sub-terms].

Recursors expect an argument for each of the inductive type's constructors; these arguments are called with the constructor's arguments (and the result of recursion on recursive parameters) during {tech}[ι-reduction].
The course-of-values recursion operator `brecOn`, on the other hand, expects just a single case that covers all constructors at once.
This case is provided with a value and a `below` table that contains the results of recursion on all values smaller than the given value; it should use the contents of the table to satisfy the motive for the provided value.
If the function is structurally recursive over a given parameter (or parameter group), then the results of all recursive calls will be present in this table already.

When the body of the recursive function is transformed into an invocation of `brecOn` on one of the function's parameters, the parameter and its course-of-values table are in scope.
The analysis traverses the body of the function, looking for recursive calls.
If the parameter is matched against, then its occurrences in the local context are {ref "match-generalization"}[generalized] and then instantiated with the pattern; this is also true for the type of the course-of-values table.
Typically, this pattern matching results in the type of the course-of-values table becoming more specific, which gives access to the recursive results for smaller values.
This generalization process implements the rule that patterns are {tech key:="strict sub-term"}[sub-terms] of match discriminants.
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

To elaborate it as a structurally recursive function, the first step is to establish the `bRecOn` invocation.
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
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat
```

```lean (show := false)
example : ((n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat) = ((n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
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
A description of the elaboration of mutually recursive functions
:::
