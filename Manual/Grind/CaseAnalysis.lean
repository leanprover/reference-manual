/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Case Analysis" =>
%%%
tag := "grind-split"
%%%

In addition to congruence closure and constraint propagation, {tactic}`grind` performs case analysis.
During case analysis, {tactic}`grind` considers each possible way that a term could have been built, or each possible value of a particular term, in a manner similar to the {tactic}`cases` and {tactic}`split` tactics.
This case analysis is not exhaustive: {tactic}`grind` only recursively splits cases up to a configured depth limit, and configuration options and annotations control which terms are candidates for splitting.


# Selection Heuristics

{tactic}`grind` decides which sub‑term to split on by combining three sources of signal:

: Structural flags

  These configuration flags determine whether {tactic}`grind` performs certain case splits:

  : `splitIte` (default {lean}`true`)

    Every {keywordOf Lean.Parser.Term.ite}`if`-term should be split, as if by the {tactic}`split` tactic.

  : `splitMatch` (default {lean}`true`)

    Every {keywordOf Lean.Parser.Term.match}`match`-term should be split, as if by the {tactic}`split` tactic.

  :  `splitImp` (default {lean}`false`)

    :::leanSection
    ```lean -show
    variable {A : Prop} {B : Sort u}
    ```
    Hypotheses of the form {lean}`A → B` whose antecedent {lean}`A` is *propositional* are split by considering all possibilities for {lean}`A`.
    Arithmetic antecedents are special‑cased: if {lean}`A` is an arithmetic literal (that is, a proposition formed by operators such as `≤`, `=`, `¬`, {lean}`Dvd`, …) then {tactic}`grind` will split _even when `splitImp := false`_ so the integer solver can propagate facts.
    :::

: Global limits

  The {tactic}`grind` option `splits := n` caps the depth of the search tree.
  Once a branch performs `n` splits {tactic}`grind` stops splitting further in that branch; if the branch cannot be closed it reports that the split threshold has been reached.

: Manual annotations

  Inductive predicates or structures may be tagged with the {attr}`grind cases` attribute.
  {tactic}`grind` treats every instance of that predicate as a candidate for splitting.


:::syntax attr (title := "Case Analysis")
```grammar
grind cases
```
{includeDocstring Lean.Parser.Attr.grindCases}
:::

:::syntax attr (title := "Eager Case Analysis")
```grammar
grind cases eager
```
{includeDocstring Lean.Parser.Attr.grindCasesEager}
:::


:::example "Splitting Conditional Expressions"
In this example, {tactic}`grind` proves the theorem by considering both cases for the conditional:
```lean
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind
```

Disabling `splitIte` causes the proof to fail:
```lean +error (name := noSplitIte)
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind -splitIte
```
In particular, it cannot make progress after discovering that the conditional expression is equal to {lean}`0`:
```leanOutput noSplitIte (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] others
      [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
```

Forbidding all case splitting causes the proof to fail for the same reason:
```lean +error (name := noSplitsAtAll)
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind (splits := 0)
```
```leanOutput noSplitsAtAll (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] others
      [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
```

Allowing just one split is sufficient:
```lean
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind (splits := 1)
```
:::

:::example "Splitting Pattern Matching"
Disabling case splitting on pattern matches causes {tactic}`grind` to fail in this example:
```lean +error (name := noSplitMatch)
example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  grind -splitMatch
```
```leanOutput noSplitMatch (expandTrace := eqc)
`grind` failed
case grind
y x : Nat
h : y =
  match x with
  | 0 => 1
  | x => 2
h_1 : y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] (x = 0 → False) →
          (match x with
            | 0 => 1
            | x => 2) =
            2
  [eqc] Equivalence classes
    [eqc] {y, 0}
      [eqc] {match x with
          | 0 => 1
          | x => 2}
    [eqc] {x = 0 → False, (fun x_0 => x_0 = 0 → False) x, x = 0 → False}
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints

[grind] Diagnostics
```
Enabling the option causes the proof to succeed:
```lean
example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  grind
```
:::

:::example "Splitting Predicates"
{lean}`Not30` is a somewhat verbose way to state that a number is not {lean}`30`:
```lean
inductive Not30 : Nat → Prop where
  | gt : x > 30 → Not30 x
  | lt : x < 30 → Not30 x
```

By default, {tactic}`grind` cannot show that {lean}`Not30` implies that a number is, in fact, not {lean}`30`:
```lean +error (name := not30fail)
example : Not30 n → n ≠ 30 := by grind
```
This is because {tactic}`grind` does not consider both cases for {lean}`Not30`
```leanOutput not30fail (expandTrace := eqc)
`grind` failed
case grind
n : Nat
h : Not30 n
h_1 : n = 30
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] Not30 n
  [eqc] Equivalence classes
    [eqc] {n, 30}
  [cutsat] Assignment satisfying linear constraints
```

Adding the {attr}`grind cases` attribute to {lean}`Not30` allows the proof to succeed:
```lean
attribute [grind cases] Not30

example : Not30 n → n ≠ 30 := by grind
```

Similarly, the {attr}`grind cases` attribute on {lean}`Even` allows {tactic}`grind` to perform case splits:
```lean (name := blah)
@[grind cases]
inductive Even : Nat → Prop
  | zero : Even 0
  | step : Even n → Even (n + 2)

attribute [grind cases] Even

example (h : Even 5) : False := by
  grind

set_option trace.grind.split true in
example (h : Even (n + 2)) : Even n := by
  grind
```

:::

# Performance

Case analysis is powerful, but computationally expensive: each level of case splitting multiplies the search space.
It's important to be judicious and not perform unnecessary splits.
In particular:
* Increase `splits` *only* when the goal genuinely needs deeper branching; each extra level multiplies the search space.
* Disable `splitMatch` when large pattern‑matching definitions explode the tree; this can be observed by setting the {option}`trace.grind.split`.
* Flags can be combined, e.g. `by grind -splitMatch (splits := 10) +splitImp`.
* The {attr}`grind cases` attribute is {ref "scoped-attributes"}_scoped_.
  The modifiers {keywordOf Lean.Parser.Term.attrKind}`local` and {keywordOf Lean.Parser.Term.attrKind}`scoped` restrict extra splitting to a section or namespace.

{optionDocs trace.grind.split}
