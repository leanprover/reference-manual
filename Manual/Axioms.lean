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

```lean (show := false)
universe u
```

{deftech}_Axioms_ are postulated constants.
While the axiom's type must itself be a type (that is, it must have type {lean}`Sort u`), there are no further requirements.
Axioms do not {tech key:="reduction"}[reduce] to other terms.
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
Adding an addtional `0` to {lean}`Nat` with an axiom results in some definitional reductions getting stuck.
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
Adding an addtional `0` to {lean}`Nat` with an axiom makes it so functions that use it can't be compiled.
In particular, {name}`List.length'` returns the axiom {name}`Nat.otherZero` instead of {name}`Nat.zero` as the length of the empty list.
```lean (name := otherZero2) (error := true)
axiom Nat.otherZero : Nat

def List.length' : List α → Nat
  | [] => Nat.otherZero
  | _ :: _ => xs.length
```
```leanOutput otherZero2
'Nat.otherZero' not supported by code generator; consider marking definition as 'noncomputable'
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

# Displaying Axiom Dependencies
%%%
tag := "print-axioms"
%%%

The command {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` displays all the axioms that a declaration transitively relies on.
In other words, if a proof uses another proof, which itself uses an axiom, then the axiom is reported by {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` for both.
This can be used to audit the assumptions made by a proof.
Together with {keywordOf Lean.guardMsgsCmd}`#guard_msgs`, it can also ensure that updates to libraries from other projects don't silently introduce unwanted dependencies on axioms.

# Standard Axioms
%%%
tag := "standard-axioms"
%%%

Lean includes the following mathematical axioms:
 * ```signature
   propext {a b : Prop} : (a ↔ b) → a = b
   ```
 * ```signature
   Classical.choice.{u} {α : Sort u} : Nonempty α → α
   ```
 * ```signature
   Quot.sound.{u} {α : Sort u}
     {r : α → α → Prop} {a b : α} :
     r a b → Quot.mk r a = Quot.mk r b
   ```

Three additional axioms allow the Lean kernel to invoke code generated by the compiler, rather than using its internal reduction engine.
This can greatly improve performance of implementations of proof by reflection.
Rather than using these axioms directly, they are usually invoked via the {tactic}`native_decide` tactic.
Both {name}`Lean.reduceBool` and {name}`Lean.reduceNat` contain references to {name}`Lean.trustCompiler`, which ensures that the fact that a proof trusts the correctness of the compiler is tracked.

These axioms do not truly exist for their _mathematical_ content; after all, {name}`Lean.reduceBool` and {name}`Lean.reduceNat` are essentially the identity function.
However, they allow the use of compiled code in proofs to be carefully controlled, and tracking them as axioms allows {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` to be used to audit theorems.

 * ```signature
    Lean.trustCompiler : True
   ```

 * ```signature
    Lean.ofReduceBool (a b : Bool) : Lean.reduceBool a = b → a = b
   ```
 * ```signature
    Lean.ofReduceNat (a b : Nat) : Lean.reduceNat a = b → a = b
   ```

:::keepEnv
```lean (show := false)
axiom Anything : Type
```
Finally, the axiom {name}`sorryAx` is used as part of the implementation of the {tactic}`sorry` tactic and {lean type:="Anything"}`sorry` term.
Uses of this axiom are not intended to occur in finished proofs, and this can be confirmed using {keywordOf Lean.Parser.Command.printAxioms}`#print axioms`.
:::
