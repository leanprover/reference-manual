/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.RecursiveDefs.Structural
import Manual.RecursiveDefs.WF
import Manual.RecursiveDefs.PartialFixpoint

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode



#doc (Manual) "Recursive Definitions" =>
%%%
tag := "recursive-definitions"
%%%

Allowing arbitrary recursive function definitions would make Lean's logic inconsistent.
General recursion makes it possible to write circular proofs: "{tech}[proposition] $`P` is true because proposition $`P` is true".
Outside of proofs, an infinite loop could be assigned the type {name}`Empty`, which can be used with {keywordOf Lean.Parser.Term.nomatch}`nomatch` or {name Empty.rec}`Empty.rec` to prove any theorem.

Banning recursive function definitions outright would render Lean far less useful: {tech}[inductive types] are key to defining both predicates and data, and they have a recursive structure.
Furthermore, most useful recursive functions do not threaten soundness, and infinite loops usually indicate mistakes in definitions rather than intentional behavior.
Instead of banning recursive functions, Lean requires that each recursive function is defined safely.
While elaborating recursive definitions, the Lean elaborator also produces a justification that the function being defined is safe.{margin}[The section on {ref "elaboration-results"}[the elaborator's output] in the overview of elaboration contextualizes the elaboration of recursive definitions in the overall context of the elaborator.]

There are five main kinds of recursive functions that can be defined:

: Structurally recursive functions

  Structurally recursive functions take an argument such that the function makes recursive calls only on strict sub-components of said argument.{margin}[Strictly speaking, arguments whose types are {tech}[indexed families] are grouped together with their indices, with the whole collection considered as a unit.]
  The elaborator translates the recursion into uses of the argument's {tech}[recursor].
  Because every type-correct use of a recursor is guaranteed to avoid infinite regress, this translation is evidence that the function terminates.
  Applications of functions defined via recursors are definitionally equal to the result of the recursion, and are typically relatively efficient inside the kernel.

: Recursion over well-founded relations

  Many functions are also difficult to convert to structural recursion; for instance, a function may terminate because the difference between an array index and the size of the array decreases as the index increases, but {name}`Nat.rec` isn't applicable because the index that increases is the function's argument.
  Here, there is a {tech}[measure] of termination that decreases at each recursive call, but the measure is not itself an argument to the function.
  In these cases, {tech}[well-founded recursion] can be used to define the function.
  Well-founded recursion is a technique for systematically transforming recursive functions with a decreasing measure into recursive functions over proofs that every sequence of reductions to the measure eventually terminates at a minimum.
  Applications of functions defined via well-founded recursion are not necessarily definitionally equal to their return values, but this equality can be proved as a proposition.
  Even when definitional equalities exist, these functions are frequently slow to compute with because they require reducing proof terms that are often very large.

: Recursive functions as partial fixpoints

  The definition of a function can be understood as an equation that specifies its behavior.
  In certain cases, the existence of a function that satisfies this specification can be proven even when the recursive function does not necessarily terminate for all inputs.
  This strategy is even applicable in some cases where the function definition does not necessarily terminate for all inputs.
  These partial functions emerge as fixed points of these equations are called {tech}_partial fixpoints_.

  In particular, any function whose return type is in certain monads (e.g. {name}`Option`) can be defined using this strategy.
  Lean generates additional partial correctness theorems for these monadic functions.
  As with well-founded recursion, applications of functions defined as partial fixpoints are not definitionally equal to their return values, but Lean generates theorems that propositionally equate the function to its unfolding and to the reduction behavior specified in its definition.

: Partial functions with nonempty codomains

  For many applications, it's not important to reason about the implementation of certain functions.
  A recursive function might be used only as part of the implementation of proof automation steps, or it might be an ordinary program that will never be formally proved correct.
  In these cases, the Lean kernel does not need either definitional or propositional equalities to hold for the definition; it suffices that soundness is maintained.
  Functions marked {keywordOf Lean.Parser.Command.declaration}`partial` are treated as opaque constants by the kernel and are neither unfolded nor reduced.
  All that is required for soundness is that their return type is inhabited.
  Partial functions may still be used in compiled code as usual, and they may appear in propositions and proofs; their equational theory in Lean's logic is simply very weak.

: Unsafe recursive definitions

  Unsafe definitions have none of the restrictions of partial definitions.
  They may freely make use of general recursion, and they may use features of Lean that break assumptions about its equational theory, such as primitives for casting ({name}`unsafeCast`), checking pointer equality ({name}`ptrAddrUnsafe`), and observing {tech}[reference counts] ({name}`isExclusiveUnsafe`).
  However, any declaration that refers to an unsafe definition must itself be marked {keywordOf Lean.Parser.Command.declaration}`unsafe`, making it clear when logical soundness is not guaranteed.
  Unsafe operations can be used to replace the implementations of other functions with more efficient variants in compiled code, while the kernel still uses the original definition.
  The replaced function may be opaque, which results in the function name having a trivial equational theory in the logic, or it may be an ordinary function, in which case the function is used in the logic.
  Use this feature with care: logical soundness is not at risk, but the behavior of programs written in Lean may diverge from their verified logical models if the unsafe implementation is incorrect.

:::TODO

Table providing an overview of all strategies and their properties

:::

As described in the {ref "elaboration-results"}[overview of the elaborator's output], elaboration of recursive functions proceeds in two phases:
 1. The definition is elaborated as if Lean's core type theory had recursive definitions.
    Aside from using recursion, this provisional definition is fully elaborated.
    The compiler generates code from these provisional definitions.

 2. A termination analysis attempts to use the four techniques to justify the function to Lean's kernel.
    If the definition is marked {keywordOf Lean.Parser.Command.declaration}`unsafe` or {keywordOf Lean.Parser.Command.declaration}`partial`, then that technique is used.
    If an explicit {keywordOf Lean.Parser.Command.declaration}`termination_by` clause is present, then the indicated technique is the only one attempted.
    If there is no such clause, then the elaborator performs a search, testing each parameter to the function as a candidate for structural recursion, and attempting to find a measure with a well-founded relation that decreases at each recursive call.

This section describes the rules that govern recursive functions.
After a description of mutual recursion, each of the five kinds of recursive definitions is specified, along with the tradeoffs between reasoning power and flexibility that go along with each.

# Mutual Recursion
%%%
tag := "mutual-syntax"
%%%

Just as a recursive definition is one that mentions the name being defined in the body of the definition, {deftech}_mutually recursive_ definitions are definitions that may be recursive or mention one another.
To use mutual recursion between multiple declarations, they must be placed in a {deftech}[mutual block].

:::syntax command (title := "Mutual Declaration Blocks")
The general syntax for mutual recursion is:

```grammar
mutual
  $[$declaration:declaration]*
end
```
where the declarations must be definitions or theorems.
:::

The declarations in a mutual block are not in scope in each others' signatures, but they are in scope in each others' bodies.
Even though the names are not in scope in signatures, they will not be inserted as auto-bound implicit parameters.

:::example "Mutual Block Scope"
Names defined in a mutual block are not in scope in each others' signatures.

```lean (error := true) (name := mutScope) (keep := false)
mutual
  abbrev NaturalNum : Type := Nat
  def n : NaturalNum := 5
end
```
```leanOutput mutScope
Unknown identifier `NaturalNum`
```

Without the mutual block, the definition succeeds:
```lean
abbrev NaturalNum : Type := Nat
def n : NaturalNum := 5
```
:::

:::example "Mutual Block Scope and Automatic Implicit Parameters"
Names defined in a mutual block are not in scope in each others' signatures.
Nonetheless, they cannot be used as automatic implicit parameters:

```lean (error := true) (name := mutScopeTwo) (keep := false)
mutual
  abbrev α : Type := Nat
  def identity (x : α) : α := x
end
```
```leanOutput mutScopeTwo
Unknown identifier `α`
```

With a different name, the implicit parameter is automatically added:
```lean
mutual
  abbrev α : Type := Nat
  def identity (x : β) : β := x
end
```
:::

Elaborating recursive definitions always occurs at the granularity of mutual blocks, as if there were a singleton mutual block around every declaration that is not itself part of such a block.
Local definitions introduced via {keywordOf Lean.Parser.Term.letrec}`let rec` and
 {keywordOf Lean.Parser.Command.declaration}`where` are lifted out of their context, introducing parameters for captured free variables as necessary, and treated as if they were separate definitions within the {keywordOf Lean.Parser.Command.mutual}`mutual` block as well. {TODO}[Explain this mechanism in more detail, here or in the term section.]
Thus, helpers defined in a {keywordOf Lean.Parser.Command.declaration}`where` block may use mutual recursion both with one another and with the definition in which they occur, but they may not mention each other in their type signatures.

After the first step of elaboration, in which definitions are still recursive, and before translating recursion using the techniques above, Lean identifies the actually (mutually) recursive cliques{TODO}[define this term, it's useful]  among the definitions in the mutual block and processes them separately and in dependency order.

{include 0 Manual.RecursiveDefs.Structural}

{include 0 Manual.RecursiveDefs.WF}

{include 0 Manual.RecursiveDefs.PartialFixpoint}

# Partial and Unsafe Definitions
%%%
tag := "partial-unsafe"
%%%


While most Lean functions can be reasoned about in Lean's type theory as well as compiled and run, definitions marked {keyword}`partial` or {keyword}`unsafe` cannot be meaningfully reasoned about.
From the perspective of the logic, {keyword}`partial` functions are opaque constants, and theorems that refer to {keyword}`unsafe` definitions are summarily rejected.
In exchange for the inability to use these functions for reasoning, there are far fewer requirements placed on them; this can make it possible to write programs that would be impractical or cost-prohibitive to prove anything about, while not giving up formal reasoning for the rest.
In essence, the {keyword}`partial` subset of Lean is a traditional functional programming language that is nonetheless deeply integrated with the theorem proving features, and the {keyword}`unsafe` subset features the ability to break Lean's runtime invariants in certain rare situations, at the cost of less integration with Lean's theorem-proving features.
Analogously, {keyword}`noncomputable` definitions may use features that don't make sense in programs, but are meaningful in the logic.

## Partial Functions
%%%
tag := "partial-functions"
%%%

The {keyword}`partial` modifier may only be applied to function definitions.
Partial functions are not required to demonstrate termination, and Lean does not attempt to do so.
These functions are “partial” in the sense that they do not necessarily specify a mapping from each element of the domain to an element of the codomain, because they might fail to terminate for some or all elements of the domain.
They are elaborated into {tech}[pre-definitions] that contain explicit recursion, and type checked using the kernel; however, they are subsequently treated as opaque constants by the logic.

The function's return type must be inhabited; this ensures soundness.
Otherwise, a partial function could have a type such as {lean}`Unit → Empty`.
Together with {name}`Empty.elim`, the existence of such a function could be used to prove {lean}`False` even if it does not reduce.

With partial definitions, the kernel is responsible for the following:
* It ensures that the pre-definition's type is indeed a well-formed type.
* It checks that the pre-definition's type is a function type.
* It ensures that the function's codomain is inhabited by demanding a {lean}`Nonempty` or {lean}`Inhabited` instance.
* It checks that the resulting term would be type-correct if Lean had recursive definitions.

Even though recursive definitions are not part of the kernel's type theory, the kernel can still be used to check that the body of the definition has the right type.
This works the same way as in other functional languages: uses of recursion are type checked by checking the body in an environment in which the definition is already associated with its type.
Having ensured that it type checks, the body is discarded and only the opaque constant is retained by the kernel.
As with all Lean functions, the compiler generates code from the elaborated {tech}[pre-definition].

Even though partial functions are not unfolded by the kernel, it is still possible to reason about other functions that call them so long as this reasoning doesn't depend on the implementation of the partial function itself.

:::example "Partial Functions in Proofs"
The recursive function {name}`nextPrime` inefficiently computes the next prime number after a given number by repeatedly testing candidates with trial division.
Because there are infinitely many prime numbers, it always terminates; however, formulating this proof would be nontrivial.
It is thus marked {keyword}`partial`.

```lean
def isPrime (n : Nat) : Bool := Id.run do
  for i in [2:n] do
    if i * i > n then return true
    if n % i = 0 then return false
  return true

partial def nextPrime (n : Nat) : Nat :=
  let n := n + 1
  if isPrime n then n else nextPrime n
```

It is nonetheless possible to prove that the following two functions are equal:
```lean
def answerUser (n : Nat) : String :=
  s!"The next prime is {nextPrime n}"

def answerOtherUser (n : Nat) : String :=
  " ".intercalate [
    "The",
    "next",
    "prime",
    "is",
    toString (nextPrime n)
  ]
```
The proof contains two {tactic}`simp` steps to demonstrate that the two functions are not syntactically identical.
In particular, the desugaring of string interpolation resulted in an extra {lean}`toString ""` at the end of {lean}`answerUser`'s result.
```lean
theorem answer_eq_other : answerUser = answerOtherUser := by
  funext n
  simp only [answerUser, answerOtherUser]
  simp only [toString, String.append_empty]
  rfl
```
:::

## Unsafe Definitions
%%%
tag := "unsafe"
%%%

Unsafe definitions have even fewer safeguards than partial functions.
Their codomains do not need to be inhabited, they are not restricted to function definitions, and they have access to features of Lean that might violate internal invariants or break abstractions.
As a result, they cannot be used at all as part of mathematical reasoning.

While partial functions are treated as opaque constants by the type theory, unsafe definitions may only be referenced from other unsafe definitions.
As a consequence, any function that calls an unsafe function must be unsafe itself.
Theorems are not allowed to be declared unsafe.

In addition to unrestricted use of recursion, unsafe functions can cast from one type to another, check whether two values are the very same object in memory, retrieve pointer values, and run {lean}`IO` actions from otherwise-pure code.
Using these operators requires a thorough understanding of the Lean implementation.

{docstring unsafeCast}

{docstring ptrEq (allowMissing := true)}

{docstring ptrEqList (allowMissing := true)}

{docstring ptrAddrUnsafe (allowMissing := true)}

{docstring isExclusiveUnsafe}

{docstring unsafeIO}

{docstring unsafeEIO}

{docstring unsafeBaseIO}


Frequently, unsafe operators are used to write fast code that takes advantage of low-level details.
Just as Lean code may be replaced at runtime with C code via the FFI,{TODO}[xref] safe Lean code may be replaced with unsafe Lean code for runtime programs.
This is accomplished by adding the {attr}`implemented_by` attribute to the function that is to be replaced, which is often an {keyword}`opaque` definition.
While this does not threaten Lean's soundness as a logic because the constant to be replaced has already been checked by the kernel and the unsafe replacement is only used in run-time code, it is still risky.
Both C code and unsafe code may execute arbitrary side effects.

:::syntax attr (title := "Replacing Run-Time Implementations")
The {attr}`implemented_by` attribute instructs the compiler to replace one constant with another in compiled code.
The replacement constant may be unsafe.
```grammar
implemented_by $_:ident
```
:::

:::example "Checking Equality with Pointers"

Ordinarily, a {lean}`BEq` instance's equality predicate must fully traverse both of its arguments to determine whether they are equal.
If they are, in fact, the very same object in memory, this is wasteful indeed.
A pointer equality test can be used prior to the traversal to catch this case.

The type being compared is {name}`Tree`, a type of binary trees.
```lean
inductive Tree α where
  | empty
  | branch (left : Tree α) (val : α) (right : Tree α)
```

An unsafe function may use pointer equality to terminate the structural equality test more quickly, falling back to structural checks when pointer equality fails.
```lean
unsafe def Tree.fastBEq [BEq α] (t1 t2 : Tree α) : Bool :=
  if ptrEq t1 t2 then
    true
  else
    match t1, t2 with
    | .empty, .empty => true
    | .branch l1 x r1, .branch l2 y r2 =>
      if ptrEq x y || x == y then
        l1.fastBEq l2 && r1.fastBEq r2
      else false
    | _, _ => false
```

An {attr}`implemented_by` attribute on an opaque definition bridges the worlds of safe and unsafe code.
```lean
@[implemented_by Tree.fastBEq]
opaque Tree.beq [BEq α] (t1 t2 : Tree α) : Bool

instance [BEq α] : BEq (Tree α) where
  beq := Tree.beq
```
:::

::::example "Taking Advantage of Run-Time Representations"

Because a {name}`Fin` is represented identically to its underlying {name}`Nat`, {lean}`List.map Fin.val` can be replaced by {name}`unsafeCast` to avoid a linear-time traversal that, in practice, does nothing:
```lean
unsafe def unFinImpl (xs : List (Fin n)) : List Nat :=
  unsafeCast xs

@[implemented_by unFinImpl]
def unFin (xs : List (Fin n)) : List Nat :=
  xs.map Fin.val
```

:::paragraph
From the perspective of the Lean kernel, {lean}`unFin` is defined using {name}`List.map`:
```lean
theorem unFin_length_eq_length {xs : List (Fin n)} :
    (unFin xs).length = xs.length := by
  simp [unFin]
```
In compiled code, there is no traversal of the list.
:::

This kind of replacement is risky: the correspondence between the proof and the compiled code depends fully on the equivalence of the two implementations, which cannot be proved in Lean.
The correspondence relies on details of Lean's implementation.
These “escape hatches” should be used very carefully.
::::

# Controlling Reduction
%%%
tag := "reducibility"
htmlSplit := .never
%%%

While checking proofs and programs, Lean takes {deftech}_reducibility_, also known as _transparency_, into account.
A definition's reducibility controls the contexts in which it is unfolded during elaboration and proof execution.

There are three levels of reducibility:

: {deftech}[Reducible]

  Reducible definitions are unfolded essentially everywhere, on demand.
  Type class instance synthesis, definitional equality checks, and the rest of the language treat the definition as being essentially an abbreviation.
  This is the setting applied by the {keywordOf Lean.Parser.Command.declaration}`abbrev` command.

: {deftech}[Semireducible]

  Semireducible definitions are not unfolded by potentially expensive automation such as type class instance synthesis or {tactic}`simp`, but they are unfolded while checking definitional equality and while resolving {tech}[generalized field notation].
  The {keywordOf Lean.Parser.Command.declaration}`def` command generally creates semireducible definitions unless a different reducibility level is specified with an attribute; however, definitions that use {tech}[well-founded recursion] are irreducible by default.

: {deftech}[Irreducible]

  Irreducible definitions are not unfolded at all during elaboration.
  Definitions can be made irreducible by applying the {attr}`irreducible` attribute.

:::example "Reducibility and Instance Synthesis"
These three aliases for {lean}`String` are respectively reducible, semireducible, and irreducible.
```lean
abbrev Phrase := String

def Clause := String

@[irreducible]
def Utterance := String
```

The reducible and semireducible aliases are unfolded during the elaborator's definitional equality check, causing them to be considered equivalent to {lean}`String`:
```lean
def hello : Phrase := "Hello"

def goodMorning : Clause := "Good morning"
```
The irreducible alias, on the other hand, is rejected as the type for a string, because the elaborator's definitional equality test does not unfold it:
```lean (error := true) (name := irred)
def goodEvening : Utterance := "Good evening"
```
```leanOutput irred
type mismatch
  "Good evening"
has type
  String
but is expected to have type
  Utterance
```

Because {lean}`Phrase` is reducible, the {inst}`ToString String` instance can be used as a {inst}`ToString Phrase` instance:
```lean
#synth ToString Phrase
```

However, {lean}`Clause` is semireducible, so the {inst}`ToString String` instance cannot be used:
```lean (error := true) (name := toStringClause)
#synth ToString Clause
```
```leanOutput toStringClause
failed to synthesize
  ToString Clause

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

The instance can be explicitly enabled by creating a {lean}`ToString Clause` instance that reduces to the {lean}`ToString String` instance.
This example works because semireducible definitions are unfolded while checking definitional equality:
```lean
instance : ToString Clause := inferInstanceAs (ToString String)
```
:::


:::example "Reducibility and Generalized Field Notation"
{tech}[Generalized field notation] unfolds reducible and semireducible declarations while searching for matching names.
Given the semireducible alias {name}`Sequence` for {name}`List`:
```lean
def Sequence := List

def Sequence.ofList (xs : List α) : Sequence α := xs
```
generalized field notation allows {name}`List.reverse` to be accessed from a term of type {lean}`Sequence Nat`.
```lean
#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```

However, declaring {name}`Sequence` to be irreducible prevents the unfolding:
```lean (error := true) (name := irredSeq)
attribute [irreducible] Sequence

#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```
```leanOutput irredSeq
Invalid field `reverse`: The environment does not contain `Sequence.reverse`
  xs
has type
  Sequence Nat
```
:::

:::syntax attr (title := "Reducibility Annotations")
A definition's reducibility can be set using one of the three reducibility attributes:

```grammar
reducible
```
```grammar
semireducible
```
```grammar
irreducible
```
These attributes can only be applied globally in the same file as the definition being modified, but they may be {keywordOf attrInst parser:=Lean.Parser.Term.attrKind}`local`ly applied anywhere.
:::

## Reducibility and Tactics

The tactics {tactic}`with_reducible`, {tactic}`with_reducible_and_instances`, and {tactic}`with_unfolding_all` control which definitions are unfolded by most tactics.



:::example "Reducibility and Tactics"
The functions {lean}`plus`, {lean}`sum`, and {lean}`tally` are all synonyms for {lean}`Nat.add` that are respectively reducible, semireducible, and irreducible:
```lean
abbrev plus := Nat.add

def sum := Nat.add

@[irreducible]
def tally := Nat.add
```

The reducible synonym is unfolded by {tactic}`simp`:
```lean
theorem plus_eq_add : plus x y = x + y := by simp
```

The semireducible synonym is not, however, unfolded by {tactic}`simp`:
```lean (keep := false) (error := true) (name := simpSemi)
theorem sum_eq_add : sum x y = x + y := by simp
```
Nonetheless, the definitional equality check induced by {tactic}`rfl` unfolds the {lean}`sum`:
```lean
theorem sum_eq_add : sum x y = x + y := by rfl
```
The irreducible {lean}`tally`, however, is not reduced by definitional equality.
```lean  (keep := false) (error := true) (name := reflIr)
theorem tally_eq_add : tally x y = x + y := by rfl
```
The {tactic}`simp` tactic can unfold any definition, even irreducible ones, when they are explicitly provided:
```lean  (keep := false) (name := simpName)
theorem tally_eq_add : tally x y = x + y := by simp [tally]
```
Similarly, part of a proof can be instructed to ignore irreducibility by placing it in a {tactic}`with_unfolding_all` block:
```lean
theorem tally_eq_add : tally x y = x + y := by with_unfolding_all rfl
```
:::

## Modifying Reducibility

The reducibility of a definition can be globally modified in the module in which it is defined by applying the appropriate attribute with the {keywordOf Lean.Parser.Command.attribute}`attribute` command.
In other modules, the reducibility of imported definitions can be modified by applying the attribute with the {keyword}`local` modifier.
The {keywordOf Lean.Parser.commandSeal__}`seal` and  {keywordOf Lean.Parser.commandUnseal__}`unseal` commands are a shorthand for this process.

:::syntax command (title := "Local Irreducibility")

{includeDocstring Lean.Parser.commandSeal__}

```grammar
seal $_:ident $_*
```
:::

:::syntax command (title := "Local Reducibility")
{includeDocstring Lean.Parser.commandUnseal__}

```grammar
unseal $_:ident $_*
```

:::

## Options

For performance, the elaborator and many tactics construct indices and caches.
Many of these take reducibility into account, and there's no way to invalidate and regenerate them if reducibility changes globally.
Unsafe changes to reducibility settings that could have unpredictable results are disallowed by default, but they can be enabled by using the {option}`allowUnsafeReducibility` option.

{optionDocs allowUnsafeReducibility}
