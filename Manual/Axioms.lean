/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Axioms" =>
%%%
tag := "axioms"
htmlSplit := .never
%%%
:::leanSection

```lean -show
universe u
```

{deftech}_Axioms_ are postulated constants.
While the axiom's type must itself be a type (that is, it must have type {lean}`Sort u`), there are no further requirements.
Axioms do not {tech (key := "reduction")}[reduce] to other terms.
:::

Axioms can be used to experiment with the consequences of an idea before investing the time required to construct a model or prove a theorem.
They can also be used to adopt reasoning principles that can't otherwise be accessed in Lean's type theory; Lean itself provides {ref "standard-axioms"}[three such axioms] that are known to be consistent.
However, axioms should be used with caution: axioms that are inconsistent with one another, or just false, undermine the very foundations of proofs.
Lean automatically tracks the axioms that each proof depends on so that they can be audited.

# Axiom Declarations
%%%
tag := "axiom-declarations"
%%%

Axioms declarations include a name and a type:

:::syntax Lean.Parser.Command.axiom (title := "Axiom Declarations")
```grammar
axiom $_ $_
```
:::

Axioms declarations may be modified with all possible {ref "declaration-modifiers"}[declaration modifiers].
Documentation comments, attributes, {keyword}`private`, and {keyword}`protected` have the same meaning as for other declarations.
The modifiers {keyword}`partial`, {keyword}`nonrec`, {keyword}`noncomputable` and {keyword}`unsafe` have no effect.

# Consistency
%%%
tag := "axiom-consistency"
%%%

Using axioms is risky.
Because they introduce a new constant of any type, and an inhabitant of a type that is a proposition counts as a proof of the proposition, axioms can be used to prove even false propositions.
Any proof that relies on an axiom can be trusted only to the extent that the axiom is both true and consistent with the other axioms used.
By their very nature, Lean cannot check whether new axioms are consistent; please exercise care when adding axioms.

:::example "Inconsistencies From Axioms"
Axioms may introduce inconsistency, either alone or in combination with other axioms.

Assuming a false statement allows any statement at all to be proved:
```lean
axiom false_is_true : False

theorem two_eq_five : 2 = 5 := false_is_true.elim
```

Inconsistency may also arise from axioms that are incompatible with other properties of Lean.
For example, parametricity is a powerful reasoning technique when used in languages that support it, but it is not compatible with Lean's standard axioms.
If parametricity held, then the “free theorem” from the introduction to Wadler's [_Theorems for Free_](https://dl.acm.org/doi/pdf/10.1145/99370.99404) (1989), which describes a technique for using parametricity to derive theorems about polymorphic functions, would be true.
As an axiom, it reads:
```lean
axiom List.free_theorem {α β}
  (f : {α : _} → List α → List α) (g : α → β) :
  f ∘ (List.map g) = (List.map g) ∘ f
```
However, a consequence of excluded middle is that all propositions are decidable; this means that a function can _check_ whether they are true or false.
This function can't be compiled, but it still exists.
This can be used to define polymorphic functions that are not parametric:
```lean
open Classical in
noncomputable def nonParametric
    {α : _} (xs : List α) :
    List α :=
  if α = Nat then [] else xs
```
The existence of this function contradicts the “free theorem”:
```lean
theorem unit_not_nat : Unit ≠ Nat := by
  intro eq
  have ⟨allEq⟩ := eq ▸ inferInstanceAs (Subsingleton Unit)
  specialize allEq 0 1
  contradiction

example : False := by
  have := List.free_theorem nonParametric (fun () => 42)

  unfold nonParametric at this
  simp [unit_not_nat] at this

  have := congrFun this [()]
  contradiction
```
:::

# Reduction
%%%
tag := "axiom-reduction"
%%%

Even consistent axioms can cause difficulties.
{tech}[Definitional equality] identifies terms modulo reduction rules.
The {tech}[ι-reduction] rule specifies the interaction of recursors and constructors; because axioms are not constructors, it does not apply to them.
Ordinarily, terms without free variables reduce to applications of constructors, but axioms can cause them to get “stuck,” resulting in large terms.

:::example "Axioms and Stuck Reduction"
Adding an additional `0` to {lean}`Nat` with an axiom results in some definitional reductions getting stuck.
In this example, two {name}`Nat.succ` constructors are successfully moved to the outside of the term by reduction, but {name}`Nat.rec` is unable to make further progress after encountering {lean}`Nat.otherZero`.
```lean (name := otherZero)
axiom Nat.otherZero : Nat

#reduce 4 + (Nat.otherZero + 2)
```
```leanOutput otherZero
((Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) Nat.otherZero).1 4).succ.succ
```
:::

Furthermore, the Lean compiler is not able to generate code for axioms.
At runtime, Lean values must be represented by concrete data in memory, but axioms do not have a concrete representation.
Definitions that contain non-proof code that relies on axioms must be marked {keyword}`noncomputable` and can't be compiled.

:::example "Axioms and Compilation"
Adding an additional `0` to {lean}`Nat` with an axiom makes it so functions that use it can't be compiled.
In particular, {name}`List.length'` returns the axiom {name}`Nat.otherZero` instead of {name}`Nat.zero` as the length of the empty list.
```lean (name := otherZero2) +error
axiom Nat.otherZero : Nat

def List.length' : List α → Nat
  | [] => Nat.otherZero
  | _ :: _ => xs.length
```
```leanOutput otherZero2
`Nat.otherZero` not supported by code generator; consider marking definition as `noncomputable`
```

Axioms used in proofs rather than programs do not prevent a function from being compiled.
The compiler does not generate code for proofs, so axioms in proofs are no problem.
{lean}`nextOdd` computes the next odd number from a {lean}`Nat`, which may be the number itself or one greater:
```lean
def nextOdd (k : Nat) :
    { n : Nat // n % 2 = 1 ∧ (n = k ∨ n = k + 1) } where
  val := if k % 2 = 1 then k else k + 1
  property := by
    by_cases k % 2 = 1 <;>
    simp [*] <;> omega
```
The tactic proof generates a term that transitively relies on three axioms:
```lean (name:=printAxNextOdd)
#print axioms nextOdd
```
```leanOutput printAxNextOdd
'nextOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Because they occur only in a proof, the compiler has no problem generating code:
```lean (name := evalNextOdd)
#eval (nextOdd 4, nextOdd 5)
```
```leanOutput evalNextOdd
(5, 5)
```
:::

# Standard Axioms
%%%
tag := "standard-axioms"
%%%

There are seven standard axioms in Lean. The first three axioms are important parts of how mathematics is done in Lean:
 * ```signature
   Classical.choice.{u} {α : Sort u} : Nonempty α → α
   ```
 * ```signature
   propext {a b : Prop} : (a ↔ b) → a = b
   ```
 * ```signature
   Quot.sound.{u} {α : Sort u}
     {r : α → α → Prop} {a b : α} :
     r a b → Quot.mk r a = Quot.mk r b
   ```

All three of these axioms are discussed in the book [Theorem Proving in Lean](https://lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=axioms-and-computation).

The axiom {name}`sorryAx` is used as part of the implementation of the {tactic}`sorry` tactic and {lean}`sorry` term.
Uses of this axiom are not intended to occur in finished proofs, as it can be used to prove anything:
 * ```signature
   sorryAx {α : Sort u} (synthetic := true) : α
   ```

Three final axioms do not truly exist for their _mathematical_ content; from a mathematical perspective they prove trivial statements:

 * ```signature
    Lean.trustCompiler : True
   ```

 * ```signature
    Lean.ofReduceBool (a b : Bool) : Lean.reduceBool a = b → a = b
   ```
 * ```signature
    Lean.ofReduceNat (a b : Nat) : Lean.reduceNat a = b → a = b
   ```

These axioms instead track proofs that depend on the correctness of the entire compiler, and not just on the much smaller {tech}`kernel`.

:::example "Creating and Tracking Proofs That Trust the Compiler"
The functions {name}`Lean.reduceBool` and {name}`Lean.reduceNat` can be invoked to have the compiler perform a calculation; this can greatly improve performance of implementations of proof by reflection.

```lean
def largeNumber : Nat := Lean.reduceNat (230_000 + 4_500 + 1_000_067)
```

The resulting term depends on the axiom {name}`Lean.trustCompiler` in order to track the fact that this calculation depends on the correctness of the compiler.

```lean (name := printAxExC1)
#print axioms largeNumber
```
```leanOutput printAxExC1
'largeNumber' depends on axioms: [Lean.trustCompiler]
```

The most common way that proofs end up trusting the compiler is through the {tactic}`native_decide` tactic:

```lean (name := printAxExC2)
def bigSum : (List.range 1_001).sum = 500_500 := by native_decide
#print axioms bigSum
```
```leanOutput printAxExC2
'bigSum' depends on axioms: [Lean.ofReduceBool, Lean.trustCompiler]
```
:::

# Displaying Axiom Dependencies
%%%
tag := "print-axioms"
%%%

The command {keywordOf Lean.Parser.Command.printAxioms}`#print axioms`, followed by a defined identifier, displays all the axioms that a definition transitively relies on.
In other words, if a proof uses another proof, which itself uses an axiom, then the axiom is reported by {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` for both.

::::keepEnv

This can be used to audit the assumptions made by a proof, for instance detecting that a proof transitively depends on the {tactic}`sorry` tactic.

```lean
def lazy : 4 == 2 + 1 + 1 := by sorry
```
```lean (name := printAxEx4)
#print axioms lazy
```
```leanOutput printAxEx4
'lazy' depends on axioms: [sorryAx]
```

:::example "Printing Axioms of Simple Definitions" (keep := true)

Consider the following three constants:

```lean
def addThree (n : Nat) : Nat := 1 + n + 2
theorem excluded_middle (P : Prop) : P ∨ ¬ P := Classical.em P
theorem simple_equality (P : Prop) : (P ∨ False) = P := or_false P
```

Regular functions like {lean}`addThree` that we might want to actually evaluation typically do not depend on any axioms:

```lean (name := printAxEx2)
#print axioms addThree
```
```leanOutput printAxEx2
'addThree' does not depend on any axioms
```

The excluded middle theorem is only true if we use classical reasoning, so the foundation for classical reasoning shows up alongside other axioms:

```lean (name := printAxEx1)
#print axioms excluded_middle
```
```leanOutput printAxEx1
'excluded_middle' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Finally, the idea that two equivalent propositions are equal directly relies on {tech}[propositional extensionality].

```lean (name := printAxEx3)
#print axioms simple_equality
```
```leanOutput printAxEx3
'simple_equality' depends on axioms: [propext]
```
:::

:::example "Using {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` with {keywordOf Lean.guardMsgsCmd}`#guard_msgs`"

You can use {keywordOf Lean.Parser.Command.printAxioms}`#print axioms`
together with {keywordOf Lean.guardMsgsCmd}`#guard_msgs` to ensure
that updates to libraries from other projects cannot silently
introduce unwanted dependencies on axioms.

For example, if the proof of {name}`double_neg_elim` below changed in such a way that it used more
axioms than those listed, then the {keywordOf Lean.guardMsgsCmd}`#guard_msgs` command would report an error.

```lean
theorem double_neg_elim (P : Prop) : (¬ ¬ P) = P :=
  propext Classical.not_not

/--
info: 'double_neg_elim' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms double_neg_elim

```
:::


::::
