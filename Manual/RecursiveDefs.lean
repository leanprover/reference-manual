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
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option maxRecDepth 1500

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
unknown identifier 'NaturalNum'
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
unknown identifier 'α'
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

# Partial and Unsafe Recursive Definitions
%%%
tag := "partial-unsafe"
%%%

:::planned 59
This section will describe `partial` and `unsafe` definitions:


 * Interaction with the kernel and elaborator
 * What guarantees are there, and what aren't there?
 * How to bridge from unsafe to safe code?

:::

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
These three aliasees for {lean}`String` are respectively reducible, semireducible, and irreducible.
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
  String : Type
but is expected to have type
  Utterance : Type
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

Additional diagnostic information may be available using the `set_option diagnostics true` command.
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
invalid field 'reverse', the environment does not contain 'Sequence.reverse'
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
