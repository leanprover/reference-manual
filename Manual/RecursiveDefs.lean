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
import Manual.RecursiveDefs.CoinductivePredicates

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode



#doc (Manual) "Recursive Definitions" =>
%%%
tag := "recursive-definitions"
%%%

Allowing arbitrary recursive function definitions would make Lean's logic inconsistent.
General recursion makes it possible to write circular proofs: “{tech}[proposition] $`P` is true because proposition $`P` is true”.
Outside of proofs, an infinite loop could be assigned the type {name}`Empty`, which can be used with {keywordOf Lean.Parser.Term.nomatch}`nomatch` or {name Empty.rec}`Empty.rec` to prove any theorem.

Banning recursive function definitions outright would render Lean far less useful: {tech}[inductive types] are key to defining both predicates and data, and they have a recursive structure.
Furthermore, most useful recursive functions do not threaten soundness, and infinite loops usually indicate mistakes in definitions rather than intentional behavior.
Instead of banning recursive functions, Lean requires that each recursive function is defined safely.
While elaborating recursive definitions, the Lean elaborator also produces a justification that the function being defined is safe.{margin}[The section on {ref "elaboration-results"}[the elaborator's output] in the overview of elaboration contextualizes the elaboration of recursive definitions in the overall context of the elaborator.]

There are six main kinds of recursive functions that can be defined:

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

: Coinductive and inductive predicates as fixpoints

  Recursive {lean}`Prop`-valued functions can be defined as greatest or least fixpoints of monotone operators on complete lattices.
  Coinductive predicates, defined using {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` or the {keywordOf Lean.Parser.Command.declaration}`coinductive` command, describe potentially infinite behavior such as infinite sequences or bisimulation.
  Inductive predicates, defined using {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint`, provide an alternative to standard inductive types that is compatible with mixed inductive-coinductive mutual blocks.

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

 2. A termination analysis attempts to use the five techniques to justify the function to Lean's kernel.
    If the definition is marked {keywordOf Lean.Parser.Command.declaration}`unsafe` or {keywordOf Lean.Parser.Command.declaration}`partial`, then that technique is used.
    If an explicit {keywordOf Lean.Parser.Command.declaration}`termination_by`, {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`, {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint`, or {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` clause is present, then the indicated technique is the only one attempted.
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

```lean +error (name := mutScope) -keep
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

```lean +error (name := mutScopeTwo) -keep
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

{include 0 Manual.RecursiveDefs.CoinductivePredicates}

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
In fact, the proof is by {tactic}`rfl`:
```lean
theorem answer_eq_other : answerUser = answerOtherUser := by
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

{docstring ptrEq +allowMissing}

{docstring ptrEqList +allowMissing}

{docstring ptrAddrUnsafe +allowMissing}

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

There are five levels of reducibility:

: {deftech}[Irreducible]

  Irreducible definitions are not unfolded at all during elaboration.
  Definitions can be made irreducible by applying the {attr}`irreducible` attribute.

: {deftech}[Semireducible]

  Semireducible definitions are not unfolded by potentially expensive automation such as type class instance synthesis or {tactic}`simp`, but they are unfolded while checking definitional equality and while resolving {tech}[generalized field notation].
  The {keywordOf Lean.Parser.Command.declaration}`def` command generally creates semireducible definitions unless a different reducibility level is specified with an attribute; however, definitions that use {tech}[well-founded recursion] are irreducible by default.

: {deftech}[Implicit-reducible]

  Implicit-reducible definitions are unfolded while checking {tech}[definitional equality] of terms that are not visible to the user.
  There are two situations where this is relevant.

  First, implicit-reducible definitions are unfolded while checking {tech}[definitional equality] of implicit arguments to functions.
  This includes ordinary {tech}[implicit] arguments, {tech}[instance-implicit] arguments, and {tech}[strict implicit] arguments.
  Definitions that appear in implicit arguments and are intended to reduce should be implicit-reducible.

  Second, when a metavariable is assigned, Lean checks that the actual and expected type of the assigned term are definitionally equal.
  Implicit-reducible arguments are also unfolded during this check. Definitions that appear in types should usually be implicit-reducible
  so that said metavariable assignments succeed.

: {deftech}[Instance-reducible]

  Instance-reducible definitions are unfolded during type class {tech (key := "synthesis")}[instance synthesis].
  All type class instances should be instance-reducible or reducible.
  Instances that are created by the {keywordOf Lean.Parser.Command.instance}`instance` command are automatically marked instance-reducible.

: {deftech}[Reducible]

  Reducible definitions are unfolded essentially everywhere, on demand.
  Type class instance synthesis, definitional equality checks, and the rest of the language treat the definition as being essentially an abbreviation.
  This is the setting applied by the {keywordOf Lean.Parser.Command.declaration}`abbrev` command.

Type aliases, such as `def Str := String` should not be semireducible. In most cases, they should be made implicit-reducible.

(TODO: unify terminology! Reducibility/Transparency? Level/Mode?/s)

Definitional equality checks can unfold definitions up to a certain transparency level.
* A check at *reducible transparency* can only unfold reducible definitions.
* A check at *instance transparency* can unfold reducible and instance-reducible definitions.
* A check at *implicit transparency* can additionally unfold implicit-reducible definitions.
* A check at *semireducible transparency*, also called *default transparency*, can additionally anfold semireducible definitions.

There are also transparency modes “none” and “all”, allow or deny unfolding all declarations, irrespective of their reducibility.

:::example "Reducibility and Direct Assignments"
These four aliases for {lean}`String` are respectively reducible, implicit-reducible, and irreducible.
```lean
abbrev Phrase := String

@[implicit_reducible]
def Clause := String

-- just for demonstration; semireducible type aliases are discouraged
def Text := String

@[irreducible]
def Utterance := String
```

The reducible, implicit-reducible and semireducible aliases are unfolded during the elaborator's definitional equality check, causing them to be considered equivalent to {lean}`String`:
```lean
def hello : Phrase := "Hello"

def goodMorning : Clause := "Good morning"

def gDay : Text := "G'day"
```
The irreducible alias, on the other hand, is rejected as the type for a string, because the elaborator's definitional equality test does not unfold it:
```lean +error (name := irred)
def goodEvening : Utterance := "Good evening"
```
```leanOutput irred
Type mismatch
  "Good evening"
has type
  String
but is expected to have type
  Utterance
```

Proofs by `rfl` behave similarly.

```lean +error (name := rflProofs)
example : Text = String := rfl
example : Utterance = String := rfl
```
```leanOutput rflProofs
Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  Utterance = String
```
:::

:::example "Reducibility and Instance Synthesis"

(TODO: instance-reducible example?)

Recall from the previous example the four aliases for {lean}`String`:
```lean
abbrev Phrase := String

@[implicit_reducible]
def Clause := String

-- just for demonstration; semireducible type aliases are discouraged
def Text := String

@[irreducible]
def Utterance := String
```

Because {lean}`Phrase` is reducible, the {inst}`ToString String` instance can be used as a {inst}`ToString Phrase` instance:
```lean
#synth ToString Phrase
```

However, {lean}`Clause` and `Text` are implicit- and semireducible, so the {inst}`ToString String` instance cannot be used:
```lean +error (name := toStringClause)
#synth ToString Clause
#synth ToString Text
```
```leanOutput toStringClause
failed to synthesize
  ToString Clause

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
```leanOutput toStringClause
failed to synthesize
  ToString Text

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

The instance can be explicitly enabled by creating a {lean}`ToString Clause` instance that reduces to the {lean}`ToString String` instance.
This example works because `inferInstanceAs` unfolds semireducible definitions while comparing the types:
```lean
instance : ToString Clause := inferInstanceAs (ToString String)
instance : ToString Text := inferInstanceAs (ToString String)
```
:::


:::example "Reducibility and Generalized Field Notation"
{tech}[Generalized field notation] unfolds all declarations that are at least semireducible while searching for matching names.
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
```lean +error (name := irredSeq)
attribute [irreducible] Sequence

#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```
```leanOutput irredSeq
Invalid field `reverse`: The environment does not contain `Sequence.reverse`, so it is not possible to project the field `reverse` from an expression
  xs
of type `Sequence Nat`
```
:::

:::syntax attr (title := "Reducibility Annotations")
A definition's reducibility can be set using one of the five reducibility attributes:

```grammar
reducible
```
```grammar
instance_reducible
```
```grammar
implicit_reducible
```
```grammar
semireducible
```
```grammar
irreducible
```
These attributes can only be applied globally in the same file as the definition being modified, but they may be {keywordOf attrInst (parser := Lean.Parser.Term.attrKind)}`local`ly applied anywhere.
:::

## Reducibility and Tactics

(TODO: Make the following line less prominent!)
The tactics {tactic}`with_reducible`, {tactic}`with_reducible_and_instances`, {tactic}`with_implicit` and {tactic}`with_unfolding_all` control which definitions are unfolded by most tactics.

:::example "Reducibility and Tactics"
The functions are all synonyms for {lean}`Nat.add` that vary by their reducibility:
```lean
abbrev reducibleAdd := Nat.add

@[instance_reducible]
def instanceReducibleAdd := Nat.add

@[implicit_reducible]
def implicitReducibleAdd := Nat.add

def semireducibleAdd := Nat.add

@[irreducible]
def irreducibleAdd := Nat.add
```

The reducible synonym is unfolded by {tactic}`simp`:
```lean
example : reducibleAdd x y = x + y := by simp
```

The other synonyms are not, however, unfolded by {tactic}`simp`:
```lean -keep +error (name := simpSemi)
example : instanceReducibleAdd x y = x + y := by simp
example : implicitReducibleAdd x y = x + y := by simp
example : semireducibleAdd x y = x + y := by simp
example : irreducibleAdd x y = x + y := by simp
```
Nonetheless, the definitional equality check induced by {tactic}`rfl` unfolds all declarations that are at least semireducible:
```lean
example : semireducibleAdd x y = x + y := by rfl
```
The irreducible {lean}`irreducibleAdd`, however, is not reduced by definitional equality.
```lean  -keep +error (name := reflIr)
example : tally x y = x + y := by rfl
```
The {tactic}`simp` tactic can unfold any definition, even irreducible ones, when they are explicitly provided:
```lean  -keep (name := simpName)
example : irreducibleAdd x y = x + y := by simp [irreducibleAdd]
```
Similarly, part of a proof can be instructed to ignore irreducibility by placing it in a {tactic}`with_unfolding_all` block:
```lean
example : irreducibleAdd x y = x + y := by with_unfolding_all rfl
```
One can find out whether two terms are definitionally equal at implicit transparency using `with_implicit`:
```lean
example : implicitReducibleAdd x y = x + y := by with_implicit rfl
```
:::

:::example "Reducibility and Instance Synthesis"
The functions are all synonyms for {lean}`Nat.add` that vary by their reducibility:
```lean
abbrev reducibleAdd := Nat.add

@[instance_reducible]
def instanceReducibleAdd := Nat.add

@[implicit_reducible]
def implicitReducibleAdd := Nat.add

def semireducibleAdd := Nat.add

@[irreducible]
def irreducibleAdd := Nat.add
```

An instance of {name}`Nonzero` contains a proof that the given number is not equal to zero:
```lean
class Nonzero (n : Nat) where
  non_zero : n ≠ 0

instance Nonzero.instSucc : Nonzero (n + 1) where
  non_zero := by grind
```

The instance is found for the reducible definition {name}`reducibleAdd`:
```lean
#synth  Nonzero (reducibleAdd 2 2)
```
It is also found for the instance-reducible definition {name}`instanceReducibleAdd`.
```lean
#synth Nonzero (instanceReducibleAdd 2 2)
```
This works as follows.
First, the discrimination pattern of the instance is matched syntactically against `Nonzero (reducibleAdd 2 2)`:
```lean (name := discrTreeKey)
#discr_tree_key Nonzero.instSucc
```
```leanOutput discrTreeKey
Nonzero _
```
Then the instance's type `Nonzero (?n + 1)` is unified with `Nonzero (instanceReducibleAdd 2 2)` at instance transparency.
Here, `?n` is a {tech}[metavariable] representing the `n` parameter of `Nonzero.instSucc`.
Because `instanceReducibleAdd` is instance-reducible, `Nonzero (instanceReducibleAdd 2 2)` can be unfolded to
`Nonzero 4` and the unification succeeds with the assignment `?n := 3`.
(TODO: Also refer to the `Nat` special handling in `isDefEqOffset`?)

Instance synthesis fails for {name}`implicitReducibleAdd` because it is not reducible at instance transparency:
```lean +error (name := notZeroTally)
#synth Nonzero (implicitReducibleAdd 2 2)
```
```leanOutput notZeroTally
failed to synthesize
  Nonzero (implicitReducibleAdd 2 2)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::

:::example "Semireducible Type Aliases Are Problematic"
Consider this {tactic}`simp`-based proof.
```lean
example (nums : Array Nat) : (nums.push 0).size = nums.size + 1 := by
  set_option trace.Meta.Tactic.simp true in
  set_option trace.Meta.isDefEq true in
  set_option trace.Meta.isDefEq.printTransparency true in
  simp [Array.size_push]
```
We now introduce a type alias for `Array Nat`, semireducible by default.
```lean
def Numbers := Array Nat
```
The above proof fails if the statement is about `Numbers` instead of `Array Nat`.
```lean -keep +error (name := bla)
example (nums : Numbers) : (nums.push 0).size = nums.size + 1 := by
  simp [Array.size_push]
```
```leanOutput bla
`simp` made no progress

Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure. This is usually caused by unfolding of semireducible definitions in prior tactic steps. Use `set_option linter.tacticCheckInstances true` to investigate the source of the issue.
Full error:
  Application type mismatch: The argument
    nums
  has type
    Numbers
  but is expected to have type
    Array Nat
  in the application
    Array.push nums
```
The note already gives a hint what might have gone wrong: {name}`Numbers` is not definitionally equal to {lean}`Array Nat` at implicit transparency.

Enabling traces helps to see what happens:
```lean -keep +error
example (nums : Numbers) : (nums.push 0).size = nums.size + 1 := by
  set_option trace.Meta.Tactic.simp true in
  set_option trace.Meta.isDefEq true in
  set_option trace.Meta.isDefEq.printTransparency true in
  simp [Array.size_push]
```
```
[Meta.isDefEq] ❌️ [reducible] (Array.push ?xs ?v).size =?= (Array.push nums 0).size ▼
  [] ✅️ [reducible] ?α =?= Nat ▶
  [] ❌️ [reducible] Array.push ?xs ?v =?= Array.push nums 0 ▼
    [] ❌️ [reducible] ?xs =?= nums ▼
      [] ?xs [assignable] =?= nums [nonassignable]
      [transparency] raising transparency reducible → implicit
      [] ❌️ [implicit] Array Nat =?= Numbers ▼
        [onFailure] ❌️ Array Nat =?= Numbers
  [...]
[Meta.Tactic.simp.unify] Array.size_push:1000, failed to unify
      (Array.push ?xs ?v).size
    with
      (Array.push nums 0).size
```
`simp` tries to unify the left-hand side {lean}`((?xs : Array Nat).push ?v).size` of {name}`Array.size_push`,
with metavariables in place of the lemma's parameters, with the subterm `(nums.push 0).size` of the goal at *reducible transparency*.
It must assign `?xs := nums` to succeed. This assignment is only allowed if their types {lean}`Array Nat` and {name}`Numbers`,
so `simp` now tries to unify these types. The transparency level is bumped to at least `implicit` for all type comparisons for
metavariable assignments, so for this check, transparency increases from `reducible` to `implicit`.
Because {name}`Numbers` is semireducible, the assignment fails, and `simp` cannot apply the lemma.

The proof succeeds if {name}`Numbers` is implicit-reducible:
```lean -keep
attribute [implicit_reducible] Numbers

example (nums : Numbers) : (nums.push 0).size = nums.size + 1 := by
  simp [Array.size_push]
```

This is why most type aliases should be implicit-reducible or reducible instead of semireducible.
There are only few situations in which type aliases get a different reducibility, and even fewer
where they are left semireducible.

:::


## Modifying Reducibility

The reducibility of a definition can be globally modified in the module in which it is defined by applying the appropriate attribute with the {keywordOf Lean.Parser.Command.attribute}`attribute` command.
In other modules, the reducibility of imported definitions can be modified by applying the attribute with the {keyword}`local` modifier.
The {keywordOf Lean.Parser.commandSeal__}`seal` and  {keywordOf Lean.Parser.commandUnseal__}`unseal` commands are a shorthand for making
definitions locally irreducible and reverting to semireducibility, respectively.

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
