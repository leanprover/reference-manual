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

#doc (Manual) "E‑matching" =>
%%%
tag := "e-matching"
%%%

{deftech}_E-matching_ is procedure for efficiently instantiating quantified theorem statements with ground terms that is widely employed in SMT solvers, used by {tactic}`grind` to instantiate theorems efficiently.
It is especially effective when combined with {tech}[congruence closure], enabling {tactic}`grind` to discover non-obvious consequences of equalities and annotated theorems automatically.

E-matching adds new facts to the metaphorical whiteboard, based on an index of theorems.
When the whiteboard contains terms that match the index, the E-matching engine instantiates the corresponding theorems, and the resulting terms can feed further rounds of {tech}[congruence closure], {tech}[constraint propagation], and theory-specific solvers.
Each fact added to the whiteboard by E-matching is referred to as an {deftech (key := "e-matching instance")}_instance_.
Annotating theorems for E-matching, thus adding them to the index, is essential for enabling {tactic}`grind` to make effective use of a library.

In addition to user-specified theorems, {tactic}`grind` uses automatically generated equations for {keywordOf Lean.Parser.Term.match}`match`-expressions as E-matching theorems.
Behind the scenes, the {tech}[elaborator] generates auxiliary functions that implement pattern matches, along with equational theorems that specify their behavior.
Using these equations with E-matching enables {tactic}`grind` to reduce these instances of pattern matching.


# Patterns
%%%
tag := "e-matching-patterns"
%%%

The E-matching index is a table of _patterns_.
When a term matches one of the patterns in the table, {tactic}`grind` attempts to instantiate and apply the corresponding theorem, giving rise to further facts and equalities.
Selecting appropriate patterns is an important part of using {tactic}`grind` effectively: if the patterns are too restrictive, then useful theorems may not be applied; if they are too general, performance may suffer.


::::example "E-matching Patterns"
Consider the following functions and theorems:
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```

```lean -show
variable {x a b : Nat}
```
The theorem {lean}`gf` asserts that {lean}`g (f x) = x` for all natural numbers {lean}`x`.
The attribute {attr}`grind =` instructs {tactic}`grind` to use the left-hand side of the equation, {lean}`g (f x)`, as a pattern for heuristic instantiation via E-matching.

This proof goal does not include an instance of {lean}`g (f x)`, but {tactic}`grind` is nonetheless able to solve it:
```lean
example {a b} (h : f b = a) : g a = b := by
  grind
```

Although {lean}`g a` is not an instance of the pattern {lean}`g (f x)`, it becomes one modulo the equation {lean}`f b = a`.
By substituting {lean}`a` with {lean}`f b` in {lean}`g a`, we obtain the term {lean}`g (f b)`, which matches the pattern {lean}`g (f x)` with the assignment `x := b`.
Thus, the theorem {lean}`gf` is instantiated with `x := b`, and the new equality {lean}`g (f b) = b` is asserted.
{tactic}`grind` then uses congruence closure to derive the implied equality {lean}`g a = g (f b)` and completes the proof.
::::


The {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` command can be used to manually select an E-matching pattern for a theorem.
Enabling the option {option}`trace.grind.ematch.instance` causes {tactic}`grind` print a trace message for each theorem instance it generates, which can be helpful when determining E-matching patterns.

:::syntax command (title := "E-matching Pattern Selection")
```grammar
grind_pattern $_ => $_,*
```
Associates a theorem with one or more patterns.
When multiple patterns are provided in a single {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` command, _all_ of them must match a term before {tactic}`grind` will attempt to instantiate the theorem.
:::

::::example "Selecting Patterns"
The {attr}`grind =` attribute uses the left side of the equality as the E-matching pattern for {lean}`gf`:
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```

For example, the pattern `g (f x)` is too restrictive in the following case:
the theorem `gf` will not be instantiated because the goal does not even
contain the function symbol `g`.

In this example, {tactic}`grind` fails because the pattern is too restrictive: the goal does not contain the function symbol {lean}`g`.
```lean +error (name := restrictivePattern)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```
```leanOutput restrictivePattern (expandTrace := eqc)
`grind` failed
case grind
b a c : Nat
h₁ : f b = a
h₂ : f c = a
h : ¬b = c
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] b = c
  [eqc] Equivalence classes
    [eqc] {a, f b, f c}
```

Using just `f x` as the pattern allows {tactic}`grind` to solve the goal automatically:
```lean
grind_pattern gf => f x

example {a b c} (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```

Enabling {option}`trace.grind.ematch.instance` makes it possible to see the equalities found by E-matching:
```lean (name := ematchInstanceTrace)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  set_option trace.grind.ematch.instance true in
  grind
```
```leanOutput ematchInstanceTrace
[grind.ematch.instance] gf: g (f c) = c
[grind.ematch.instance] gf: g (f b) = b
```

After E-matching, the proof succeeds because congruence closure equates `g (f c)` with `g (f b)`, because both `f b` and `f c` are equal to `a`.
Thus, `b` and `c` must be in the same equivalence class.

::::

When multiple patterns are specified together, all of them must match in the current context before {tactic}`grind` attempts to instantiate the theorem.
This is referred to as a {deftech}_multi-pattern_.
This is useful for lemmas such as transitivity rules, where multiple premises must be simultaneously present for the rule to apply.
A single theorem may be associated with multiple separate patterns by using multiple invocations of {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` or the {attrs}`@[grind _=_]` attribute.
If _any_ of these separate patterns match, the theorem will be instantiated.

::::example "Multi-Patterns"

{lean}`R` is a transitive binary relation over {lean}`Int`:
```lean
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z
```

To use the fact that {lean}`R` is transitive, {tactic}`grind` must already be able to satisfy both premises.
This is represented using a {tech}[multi-pattern]:
```lean
grind_pattern Rtrans => R x y, R y z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```

```lean -show
variable {x y z a b c d : Int}
```

The multi-pattern `R x y, R y z` instructs {tactic}`grind` to instantiate {lean}`Rtrans` only when both {lean}`R x y` and {lean}`R y z` are available in the context.
In the example, {tactic}`grind` applies {lean}`Rtrans` to derive {lean}`R a c` from {lean}`R a b` and {lean}`R b c`, and can then repeat the same reasoning to deduce {lean}`R a d` from {lean}`R a c` and {lean}`R c d`.
::::

The {attr}`grind` attribute automatically generates an E-matching pattern or multi-pattern using a heuristic, instead of using {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern` to explicitly specify a pattern.
It includes a number of variants that select different heuristics.
The {attr}`grind?` attribute displays an info message showing the pattern which was selected—this is very helpful for debugging!

Patterns are subexpressions of theorem statements.
A subexpression is {deftech}_indexable_ if it has an indexable constant as its head, and it is said to {deftech}_cover_ one of the theorem's arguments if it fixes the argument's value.
Indexable constants are all constants other than {name}`Eq`, {name}`HEq`, {name}`Iff`, {name}`And`, {name}`Or`, and {name}`Not`.
The set of arguments that are covered by a pattern or multi-pattern is referred to as its {deftech}_coverage_.
Some constants are lower priority than others; in particular, the arithmetic operators {name}`HAdd.hAdd`, {name}`HSub.hSub`, {name}`HMul.hMul`, {name}`Dvd.dvd`, {name}`HDiv.hDiv`, and {name}`HMod.hMod` have low priority.
An indexable subexpression is {deftech}_minimal_ if there is no smaller indexable subexpression whose head constant has at least as high priority.

:::syntax attr (title := "Grind Patterns")
When the {attr}`grind` attribute is added to a definition, it causes `grind` to unfold that definition to its body whenever it is encountered.
When using the module system, if the body of the definition is not visible (e.g. via {attrs}`@[expose]`), then the {attr}`grind` attribute is ignored.

```grammar
grind $[$_:grindMod]?
```
The {attr}`grind` attribute automatically generates an E-matching pattern for a theorem, using a strategy determined by the provided modifier.
If no modifier is provided, then {attr}`grind` suggests suitable modifiers, displaying the resulting patterns.

```grammar
grind! $[$_:grindMod]?
```
The {attr}`grind!` attribute automatically generates an E-matching pattern for a theorem, using a strategy determined by the provided modifier.
It additionally enforces the condition that the selected pattern(s) should be minimal indexable subexpressions.

```grammar
grind? $[$_:grindMod]?
```

The {attr}`grind?` displays the pattern that was generated.

```grammar
grind!? $[$_:grindMod]?
```
The {attr}`grind!?` attribute is equivalent to {attr}`grind!`, except it displays the resulting pattern for inspection.


Without any modifier, {attrs}`@[grind]` traverses the conclusion and then the hypotheses from left to right, adding patterns as they increase the coverage, stopping when all arguments are covered.
This default strategy can be explicitly requested using the {keywordOf Lean.Parser.Attr.grindDef}`.` modifier.
In addition to using the default strategy, the attribute checks which other strategies could be applied, and displays all of the resulting patterns.
:::

```lean -keep -show
-- This test will start failing if new grind modfiers are added. It's to make sure they're all
-- documented (or at least that a decision has been mad to _not_ document one of them).
open Lean Parser Attr
open Lean Elab Command

deriving instance Repr for ParserDescr

def getName : ParserDescr → CommandElabM String
  | .nodeWithAntiquot name .. => pure name
  | other => throwError m!"Expected a {.ofConstName ``nodeWithAntiquot}, got {repr other}"

def getOrElse (descr : ParserDescr) : CommandElabM (Array ParserDescr) := do
  match descr with
  | .binary `orelse x y => return (← getOrElse x) ++ (← getOrElse y)
  | other => return #[other]

def getGrindAlts (descr : ParserDescr) : CommandElabM (Array String) := do
  if let .nodeWithAntiquot "grindMod" ``grindMod d' := descr then
    let cases ← getOrElse d'
    return (← cases.mapM getName).qsort
  else throwError "Expected a {.ofConstName ``nodeWithAntiquot}, got {repr descr}"

/--
info: `grindMod` can be these:
grindBwd
grindCases
grindCasesEager
grindDef
grindEq
grindEqBoth
grindEqBwd
grindEqRhs
grindExt
grindFunCC
grindFwd
grindGen
grindInj
grindIntro
grindLR
grindRL
grindSym
grindUsr
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let allMods ← getGrindAlts grindMod
  IO.println "`grindMod` can be these:"
  for gmod in allMods do
    IO.println gmod

```

:::syntax Lean.Parser.Attr.grindMod (title := "Default Pattern")
```grammar
.
```
```grammar
·
```
{includeDocstring Lean.Parser.Attr.grindDef}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Equality Rewrites")
```grammar
=
```
{includeDocstring Lean.Parser.Attr.grindEq}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Backward Equality Rewrites")
```grammar
=_
```
{includeDocstring Lean.Parser.Attr.grindEqRhs}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Bidirectional Equality Rewrites")
```grammar
_=_
```
{includeDocstring Lean.Parser.Attr.grindEqBoth}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Forward Reasoning")
```grammar
→
```
{includeDocstring Lean.Parser.Attr.grindFwd}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Backward Reasoning")
```grammar
←
```
{includeDocstring Lean.Parser.Attr.grindBwd}
:::

It is important to inspect the patterns generated by the {attrs}`@[grind]` attribute to ensure that they match the correct parts of the lemma.
If the pattern is too strict, the lemma will not be applied in situations where it would be relevant, leading to less automation.
If it is too general, then performance will suffer as the lemma is tried in many situations where it is not helpful.

There are also three less commonly used modifiers for lemmas:

:::syntax Lean.Parser.Attr.grindMod (title := "Left-to-Right Traversal")
```grammar
=>
```
```grammar
⇒
```
{includeDocstring Lean.Parser.Attr.grindLR}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Right-to-Left Traversal")
```grammar
<=
```
```grammar
⇐
```
{includeDocstring Lean.Parser.Attr.grindRL}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Backward Reasoning on Equality")
```grammar
←=
```
{includeDocstring Lean.Parser.Attr.grindEqBwd}
:::

:::example "The `@[grind ←=]` Attribute"
```lean -show
variable {α} {a b : α} [Inv α]
```
When attempting to prove that {lean}`a⁻¹ = b`, {tactic}`grind` uses {name}`inv_eq` due to the {attrs}`@[grind ←=]` annotation.
```lean
@[grind ←=]
theorem inv_eq [One α] [Mul α] [Inv α] {a b : α}
    (w : a * b = 1) : a⁻¹ = b :=
  sorry
```
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Function-Valued Congruence Closure")
```grammar
funCC
```
{includeDocstring Lean.Parser.Attr.grindFunCC}
:::


Some additional modifiers can be used to add other kinds of lemmas to the index.
This includes extensionality theorems, injectivity theorems for functions, and a shortcut to add all constructors of an inductively defined predicate to the index.

:::syntax Lean.Parser.Attr.grindMod (title := "Extensionality")
```grammar
ext
```
{includeDocstring Lean.Parser.Attr.grindExt}

In addition, adding {attrs}`@[grind ext]` to a structure registers a its extensionality theorem.
:::


::::example "The `@[grind ext]` Attribute"

{lean}`Point` is a structure with two fields:
```lean
structure Point where
  x : Int
  y : Int
```
By default, {tactic}`grind` can solve goals like this one, because definitional equality includes {tech (key := "η-equivalence")}[η-equivalence] for product types:
```lean
example (p : Point) : p = ⟨p.x, p.y⟩ := by grind
```
However, it can't solve goals like this one that require an appeal to propositional equalities:
```lean +error (name := noExt)
example (p : Point) (a : Int) : a = p.x → p = ⟨a, p.y⟩ := by grind
```
```leanOutput noExt
`grind` failed
case grind
p : Point
a : Int
h : a = p.x
h_1 : ¬p = { x := a, y := p.y }
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
```


This kind of goal may come up when proving theorems like the fact that swapping the fields of a point twice is the identity:
```lean
def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩
```
```lean +error (name := noExt')
theorem swap_swap_eq_id : Point.swap ∘ Point.swap = id := by
  unfold Point.swap
  grind
```
```leanOutput noExt'
`grind` failed
case grind
h : ¬((fun p => { x := p.y, y := p.x }) ∘ fun p => { x := p.y, y := p.x }) = id
w : Point
h_1 : ¬{ x := w.x, y := w.y } = id w
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns

[grind] Diagnostics
```
Adding the {attrs}`@[grind ext]` attribute to {name}`Point` enables {tactic}`grind` to solve both the original example and prove this theorem:
```lean
attribute [grind ext] Point

example (p : Point) (a : Int) : a = p.x → p = ⟨a, p.y⟩ := by
  grind

theorem swap_swap_eq_id' : Point.swap ∘ Point.swap = id := by
  unfold Point.swap
  grind
```
::::

:::syntax Lean.Parser.Attr.grindMod (title := "Injectivity")
```grammar
inj
```
{includeDocstring Lean.Parser.Attr.grindInj}
:::

:::example "Injectivity Patterns"
This function {name}`double` doubles its argument:
```lean
def double (x : Nat) : Nat := x + x
```
By default, {tactic}`grind` cannot prove the following theorem:
```lean +error
theorem A {n k : Nat} :
    double (n + 5) = double (k - 3) →
    n + 8 = k := by
  grind
```
However, {name}`double` is injective, and this fact can be registered for {tactic}`grind` using the {attr}`grind inj` attribute:
```lean
@[grind inj]
theorem double_inj : Function.Injective double := by
  simp only [double, Function.Injective]
  grind
```
This injectivity lemma suffices to prove the theorem:
```lean
theorem B {n k : Nat} :
    double (n + 5) = double (k - 3) →
    n + 8 = k := by
  grind
```
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Constructor Patterns")
```grammar
intro
```
{includeDocstring Lean.Parser.Attr.grindIntro}
:::

:::example "Patterns for Constructors"
The predicate {name}`Decreasing` states that each of the values in a list of integers is less than the one before, and the function {name}`decreasing` checks this property, returning a {name}`Bool`.
```lean
inductive Decreasing : List Int → Prop
  | nil : Decreasing []
  | singleton : Decreasing [x]
  | cons : Decreasing (x :: xs) → y > x → Decreasing (y :: x :: xs)

def decreasing : List Int → Bool
  | [] | [_] => true
  | y :: x :: xs => y > x && decreasing (x :: xs)
```

The function is correct if it returns {name}`true` exactly when {name}`Decreasing` holds for its argument.
Attempting to prove this fact using a combination of {tactic}`fun_induction` and {tactic}`grind` fails immediately, with none of the three cases proven:
```lean +error (name := decreasingCorrect1)
def decreasingCorrect : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> grind
```
```leanOutput decreasingCorrect1
`grind` failed
case grind
h : True = ¬Decreasing []
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
```
```leanOutput decreasingCorrect1
`grind` failed
case grind
head : Int
h : True = ¬Decreasing [head]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
```
```leanOutput decreasingCorrect1
`grind` failed
case grind.1
y x : Int
xs : List Int
ih1 : (decreasing (x :: xs) = true) = Decreasing (x :: xs)
h : (-1 * y + x + 1 ≤ 0 ∧ decreasing (x :: xs) = true) = ¬Decreasing (y :: x :: xs)
left : -1 * y + x + 1 ≤ 0
left_1 : decreasing (x :: xs) = true
right_1 : ¬Decreasing (y :: x :: xs)
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [cutsat] Assignment satisfying linear constraints
```
Adding the {attr}`grind intro` attribute to {name}`Decreasing` results in E-matching patterns being added for each of the three constructors, after which {tactic}`grind` can prove the first two goals, and requires only a case analysis of a hypothesis to prove the final goal:
```lean
attribute [grind intro] Decreasing

def decreasingCorrect' : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> try grind
  case case3 y x xs ih =>
    apply propext
    constructor
    . grind
    . intro
      | .cons hDec hLt =>
        grind
```
Adding {attr}`grind cases` to {name}`Decreasing` enables this case analysis automatically, resulting in a fully automatic proof:
```lean
attribute [grind cases] Decreasing

def decreasingCorrect'' : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> grind
```
:::

{TODO}[Document `gen` modifier for `grind` patterns]

# Inspecting Patterns

The {attr}`grind?` attribute is a version of the {attr}`grind` attribute that additionally displays the generated pattern or {tech}[multi-pattern].
Patterns and multi-patterns are displayed as lists of subexpressions, each of which is a pattern; ordinary patters are displayed as singleton lists.
In these displayed patterns, the names of defined constants are printed as-is.
When the theorem's parameters occur in the pattern, they are displayed using numbers rather than names.
In particular, they are numbered from right to left, starting at 0; this representation is referred as {deftech}_de Bruijn indices_.

:::example "Inspecting Patterns" (open := true)
In order to use this proof that divisibility is transitive with {tactic}`grind`, it requires E-matching patterns:
```lean
theorem div_trans {n k j : Nat} : n ∣ k → k ∣ j → n ∣ j := by
  intro ⟨d₁, p₁⟩ ⟨d₂, p₂⟩
  exact ⟨d₁ * d₂, by rw [p₂, p₁, Nat.mul_assoc]⟩
```
The right attribute to use is {attrs}`@[grind →]`, because there should be a pattern for each premise.
Using {attrs}`@[grind? →]`, it is possible to see which patterns are generated:
```lean (name := grindHuh)
attribute [grind? →] div_trans
```
There are two:
```leanOutput grindHuh
div_trans: [@Dvd.dvd `[Nat] `[Nat.instDvd] #4 #3, @Dvd.dvd `[Nat] `[Nat.instDvd] #3 #2]
```
Arguments are numbered from right to left, so `#0` is the assumption that `k ∣ j`, while `#4` is `n`.
Thus, these two patterns correspond to the terms `n ∣ k` and `k ∣ j`.
:::

The rules for selecting patterns from subexpressions of the hypotheses and conclusion are subtle.
:::TODO
more text
:::

:::example "Forward Pattern Generation" (open := true)
```lean
axiom p : Nat → Nat
axiom q : Nat → Nat
```

```lean (name := h1)
@[grind!? →] theorem h₁ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
```leanOutput h1
h₁: [q #1]
```
The pattern is `q x`.
Counting from the right, parameter `#0` is the premise `w` and parameter `#1` is the implicit parameter `x`.

Why did `@[grind →]`? select `q #1`?
The attribute `@[grind →]` finds patterns by traversing the hypotheses (that is, parameters whose types are propositions) from left to right.
In this case, there's only a single hypothesis: `7 = p (q x)`.
The heuristic described above says that {attr}`grind` will search for a minimal {tech}[indexable] subexpression which {tech}[covers] a previously uncovered parameter.
There's just one uncovered parameter, namely `x`.
The whole hypothesis `p (q x) = 7` can't be used because {tactic}`grind` will not index on equality.
The right-hand side `7` is not helpful, because it doesn't determine the value of `x`.
`p (q x)` is not suitable because it is not minimal: it has `q x` inside of it, which is indexable (its head is the constant `q`), and it determines the value of `x`.
The expression `q x` itself is minimal, because `x` is not indexable.
Thus, `q x` is selected as the pattern.
:::

:::example "Backward Pattern Generation" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```

In this example, the {keywordOf Lean.Parser.Attr.grindMod}`←` modifier indicates that the pattern should be found in the conclusion:
```lean (name := h2)
set_option trace.grind.debug.ematch.pattern true in
@[grind? ←] theorem h₂ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
The left side of the equality is used because {name}`Eq` is not indexable and {name}`HAdd.hAdd` has lower priority than {lean}`p`.
```leanOutput h2
h₂: [p (#1 + 1)]
```
:::

:::example "Bidirectional Equality Pattern Generation" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
In this example, two separate E-matching patterns are generated from the equality conclusion.
One matches the left-hand side, and the other matches the right-hand side.
```lean (name := h3)
@[grind? _=_] theorem h₃ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
```leanOutput h3
h₃: [q #1]
```

The entire left side of the equality is used instead of just `x + 1` because {name}`HAdd.hAdd` has lower priority than {lean}`p`.
```leanOutput h3
h₃: [p (#1 + 1)]
```
:::

:::example "Patterns from Conclusion and Hypotheses" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```

Without any modifiers, {attrs}`@[grind]` produces a multipattern by first checking the conclusion and then the premises:
```lean (name := h4)
@[grind? .] theorem h₄ (w : p x = q y) : p (x + 2) = 7 := sorry
```
Here, argument `x` is `#2`, `y` is `#1`, and `w` is `#0`.
The resulting multipattern contains the left-hand side of the equality, which is the only {tech}[minimal] {tech}[indexable] subexpression of the conclusion that covers an argument (namely `x`).
It also contains `q y`, which is the only minimal indexable subexpression of the hypothesis `w` that covers an additional argument (namely `y`).
```leanOutput h4
h₄: [p (#2 + 2), q #1]
```
:::

:::example "Failing Backward Pattern Generation" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
In this example, pattern generation fails because the theorem's conclusion doesn't mention the the argument `y`.
```lean (name := h5) +error
@[grind? ←] theorem h₅ (w : p x = q y) : p (x + 2) = 7 := sorry
```
```leanOutput h5
`@[grind ←] theorem h₅` failed to find patterns in the theorem's conclusion, consider using different options or the `grind_pattern` command
```
:::

:::example "Left-to-Right Generation" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
In this example, the pattern is generated by traversing the premises from left to right, followed by the conclusion:
```lean (name := h6)
@[grind? =>] theorem h₆
    (_ : q (y + 2) = q y)
    (_ : q (y + 1) = q y) :
    p (x + 2) = 7 :=
  sorry
```
In the patterns, `y` is argument `#3` and `x` is argument `#2`, because {tech}[automatic implicit parameters] are inserted from left to right and `y` occurs before `x` in the theorem statement.
The premises are arguments `#1` and `#0`.
In the resulting multipattern, `y` is covered by a subexpression of the first premise, and `z` is covered by a subexpression of the conclusion:
```leanOutput h6
h₆: [q (#3 + 2), p (#2 + 2)]
```
:::


# Resource Limits
%%%
tag := "grind-limits"
%%%

E-matching can generate an unbounded number of theorem {tech (key := "e-matching instance")}[instances].
For the sake of both efficiency and termination, {tactic}`grind` limits the number of times that E-matching can run using two mechanisms:

: Generations

  Each term is assigned a {deftech}_generation_, and terms produced by E-matching have a generation that is one greater than the maximal generation of all the terms used to instantiate the theorem.
  E-matching only considers terms whose generation is beneath a configurable threshold.
  The `gen` option to {tactic}`grind` controls the generation threshold.

: Round Limits

  Each invocation of the E-matching engine is referred to as a {deftech}_round_.
  Only a limited number of rounds of E-matching are performed.
  The `ematch` option to {tactic}`grind` controls the round limit.


:::example "Too Many Instances" (open := true)

E-matching can generate too many theorem {tech (key := "e-matching instance")}[instances].
Some patterns may even generate an unbounded number of instances.

In this example, {name}`s_eq` is added to the index with the pattern `s x`:
```lean (name := ematchUnboundedPat)
def s (x : Nat) := 0

@[grind? =] theorem s_eq (x : Nat) : s x = s (x + 1) :=
  rfl
```
```leanOutput ematchUnboundedPat
s_eq: [s #0]
```

Attempting to use this theorem results in many facts about {lean}`s` applied to concrete values being generated.
In particular, {lean}`s_eq` is instantiated with a new {lean}`Nat` in each of the five rounds.
First, {tactic}`grind` instantiates {lean}`s_eq` with `x := 0`, which generates the term {lean}`s 1`.
This matches the pattern `s x`, and is thus used to instantiate {lean}`s_eq` with `x := 1`, which generates the term {lean}`s 2`,
and so on until the round limit is reached.
```lean +error (name := ematchUnbounded)
example : s 0 > 0 := by
  grind
```

```leanOutput ematchUnbounded (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```

Increasing the round limit to 20 causes E-matching to terminate due to the default generation limit of 8:
```lean +error (name := ematchUnbounded2)
example : s 0 > 0 := by
  grind (ematch := 20)
```
```leanOutput ematchUnbounded2 (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
    [prop] s 5 = s 6
    [prop] s 6 = s 7
    [prop] s 7 = s 8
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 8)`

[grind] Diagnostics
```
:::

:::example "Increasing E-matching Limits"


{lean}`iota` returns the list of all numbers strictly less than its argument, and the theorem {lean}`iota_succ` describes its behavior on {lean}`Nat.succ`:
```lean
def iota : Nat → List Nat
  | 0 => []
  | n + 1 => n :: iota n

@[grind =] theorem iota_succ : iota (n + 1) = n :: iota n :=
  rfl
```

The fact that {lean}`(iota 20).length > 10` can be proven by repeatedly instantiating {lean}`iota_succ` and {lean}`List.length_cons`.
However, {tactic}`grind` does not succeed:
```lean +error (name := biggerGrindLimits)
example : (iota 20).length > 10 := by
  grind
```
```leanOutput biggerGrindLimits (expandTrace := limits) (expandTrace := facts)
`grind` failed
case grind
h : (iota 20).length ≤ 10
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] (iota 20).length ≤ 10
    [prop] iota 20 = 19 :: iota 19
    [prop] iota 19 = 18 :: iota 18
    [prop] (19 :: iota 19).length = (iota 19).length + 1
    [prop] iota 18 = 17 :: iota 17
    [prop] (18 :: iota 18).length = (iota 18).length + 1
    [prop] iota 17 = 16 :: iota 16
    [prop] (17 :: iota 17).length = (iota 17).length + 1
    [prop] iota 16 = 15 :: iota 15
    [prop] (16 :: iota 16).length = (iota 16).length + 1
  [eqc] True propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```

Due to the limited number of E-matching rounds, the chain of instantiations is not completed.
Increasing these limits allows {tactic}`grind` to succeed:

```lean
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```

When the option {option}`diagnostics` is set to {lean}`true`, {tactic}`grind` displays the number of instances that it generates for each theorem.
This is useful to detect theorems that contain patterns that are triggering too many instances.
In this case, the diagnostics show that {name}`iota_succ` is instantiated 12 times:
```lean (name := grindDiagnostics)
set_option diagnostics true in
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```
```leanOutput grindDiagnostics (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] iota_succ ↦ 12
    [thm] List.length_cons ↦ 11
  [app] Applications
  [grind] Simplifier
    [simp] tried theorems (max: 46, num: 1):
    use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
```
:::

By default, {tactic}`grind` uses automatically generated equations for {keywordOf Lean.Parser.Term.match}`match`-expressions as E-matching theorems.
This can be disabled by setting the `matchEqs` flag to {lean}`false`.

:::example "E-matching and Pattern Matching"

Enabling diagnostics shows that {tactic}`grind` uses one of the equations of the auxiliary matching function during E-matching:
```lean (name := gt1diag)
theorem gt1 (x y : Nat) :
    x = y + 1 →
    0 < match x with
        | 0 => 0
        | _ + 1 => 1 := by
  set_option diagnostics true in
  grind
```
```leanOutput gt1diag (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] gt1.match_1.congr_eq_2 ↦ 1
  [app] Applications
```
The theorem has this type:
```lean (name := gt1matchtype)
#check gt1.match_1.congr_eq_2
```
```leanOutput gt1matchtype
gt1.match_1.congr_eq_2.{u_1} (motive : Nat → Sort u_1) (x✝ : Nat) (h_1 : Unit → motive 0)
  (h_2 : (n : Nat) → motive n.succ) (n✝ : Nat) (heq_1 : x✝ = n✝.succ) :
  (match x✝ with
    | 0 => h_1 ()
    | n.succ => h_2 n) ≍
    h_2 n✝
```

Disabling the use of matcher function equations causes the proof to fail:

```lean +error (name := noMatchEqs)
example (x y : Nat)
    : x = y + 1 →
      0 < match x with
          | 0 => 0
          | _+1 => 1 := by
  grind -matchEqs
```
```leanOutput noMatchEqs
`grind` failed
case grind.2
x y : Nat
h : x = y + 1
h_1 : (match x with
  | 0 => 0
  | n.succ => 1) =
  0
n : Nat
h_2 : x = n + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] Equivalence classes
  [cases] Case analyses
  [cutsat] Assignment satisfying linear constraints
  [ring] Rings

[grind] Diagnostics
```
:::

{optionDocs trace.grind.ematch.instance}

:::comment
TBD
* anti‑patterns
* local vs global attributes
* `gen` modifier?
:::
