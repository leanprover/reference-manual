/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.Language.RecursiveDefs.Structural

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

There are four main kinds of recursive functions that can be defined:

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

: Partial functions with nonempty ranges

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


As described in the {ref "elaboration-results"}[overview of the elaborator's output], elaboration of recursive functions proceeds in two phases:
 1. The definition is elaborated as if Lean's core type theory had recursive definitions.
    Aside from using recursion, this provisional definition is fully elaborated.
    The compiler generates code from these provisional definitions.

 2. A termination analysis attempts to use the four techniques to justify the function to Lean's kernel.
    If the definition is marked {keywordOf Lean.Parser.Command.declaration}`unsafe` or {keywordOf Lean.Parser.Command.declaration}`partial`, then that technique is used.
    If an explicit {keywordOf Lean.Parser.Command.declaration}`termination_by` clause is present, then the indicated technique is the only one attempted.
    If there is no such clause, then the elaborator performs a search, testing each parameter to the function as a candidate for structural recursion, and attempting to find a measure with a well-founded relation that decreases at each recursive call.

This section describes the four techniques in detail.

{include 0 Manual.Language.RecursiveDefs.Structural}

# Well-Founded Recursion
%%%
tag := "well-founded-recursion"
%%%

::: planned 57
This section will describe the translation of {deftech}[well-founded recursion].
:::

# Controlling Reduction

:::planned 58
This section will describe {deftech}_reducibility_: {deftech}[reducible], {deftech}[semi-reducible], and {deftech}[irreducible] definitions.
:::

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
