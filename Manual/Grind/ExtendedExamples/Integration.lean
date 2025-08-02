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


open Lean.Grind

#doc (Manual) "Integrating `grind`'s Features" =>

:::paragraph
This example demonstrates how the various submodules of {tactic}`grind` are seamlessly integrated.
In particular we can:
* instantiate theorems from the library, using custom patterns,
* perform case splitting,
* do linear integer arithmetic reasoning, including modularity conditions, and
* do Gröbner basis reasoning
all without providing explicit instructions to drive the interactions between these modes of reasoning.
:::

For this example we'll begin with a “mocked up” version of the real numbers, and the `sin` and `cos` functions.
Of course, this example works [without any changes](https://github.com/leanprover-community/mathlib4/blob/master/MathlibTest/grind/trig.lean) using Mathlib's versions of these!


:::TODO
A `sorry` for `instCommRingR` causes a run-time crash. It's unclear why.
:::

```lean
axiom R : Type


@[instance] axiom instCommRingR : Lean.Grind.CommRing R


axiom sin : R → R
axiom cos : R → R
axiom trig_identity : ∀ x, (cos x)^2 + (sin x)^2 = 1
```

:::paragraph
Our first step is to tell grind to “put the trig identity on the whiteboard” whenever it sees a goal involving {name}`sin` or {name}`cos`:

```lean
grind_pattern trig_identity => cos x
grind_pattern trig_identity => sin x
```

Note here we use *two* different patterns for the same theorem, so the theorem is instantiated even if {tactic}`grind` sees just one of these functions.
If we preferred to more conservatively instantiate the theorem only when both {name}`sin` and {name}`cos` are present, we could have used a multi-pattern:

```lean (keep := false)
grind_pattern trig_identity => cos x, sin x
```

For this example, either approach will work.
:::

::::leanSection
```lean (show := false)
variable {x : R}
```

:::paragraph
Because `grind` immediately notices the trig identity, we can prove goals like this:
```lean
example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind
```
Here {tactic}`grind` does the following:

1. It notices {lean}`cos x` and {lean}`sin x`, so instantiates the trig identity.

2. It notices that this is a polynomial in {inst}`CommRing R`, and sends it to the Gröbner basis module.
   No calculation happens at this point: it's the first polynomial relation in this ring, so the Gröbner basis is updated to {lean}`[(cos x)^2 + (sin x)^2 - 1]`.

3. It notices that the left and right hand sides of the goal are polynomials in {inst}`CommRing R`, and sends them to the Gröbner basis module for normalization.

Since their normal forms modulo {lean}`(cos x)^2 + (sin x)^2 = 1` are equal, their equivalence classes are merged, and the goal is solved.

:::


:::paragraph
We can also do this sort of argument when {tech}[congruence closure] is needed:
```lean
example (f : R → Nat) :
    f ((cos x + sin x)^2) = f (2 * cos x * sin x + 1) := by
  grind
```

```lean (show := false)
variable (f : R → Nat) (n : Nat)
```

As before, {tactic}`grind` instantiates the trig identity, notices that {lean}`(cos x + sin x)^2` and {lean}`2 * cos x * sin x + 1` are equal modulo {lean}`(cos x)^2 + (sin x)^2 = 1`,
puts those algebraic expressions in the same equivalence class, and then puts the function applications {lean}`f ((cos x + sin x)^2)` and {lean}`f (2 * cos x * sin x + 1)` in the same equivalence class,
and closes the goal.
:::

Notice that we've used an arbitrary function {typed}`f : R → Nat` here; let's check that `grind` can use some linear integer arithmetic reasoning after the Gröbner basis steps:
```lean
example (f : R → Nat) :
    4 * f ((cos x + sin x)^2) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind
```


Here {tactic}`grind` first works out that this goal reduces to {lean}`4 * n ≠ 2 + n` for some {typed}`n : Nat` (i.e. by identifying the two function applications as described above), and then uses modularity to derive a contradiction.



Finally, we can also mix in some case splitting:
```lean
example (f : R → Nat) :
    max 3 (4 * f ((cos x + sin x)^2)) ≠
      2 + f (2 * cos x * sin x + 1) := by
  grind
```
As before, {tactic}`grind` first does the instantiation and Gröbner basis calculations required to identify the two function applications.
However the `cutsat` algorithm by itself can't do anything with {lean}`max 3 (4 * n) ≠ 2 + n`.
Next, after instantiating {lean}`Nat.max_def` (automatically, because of an annotation in the standard library) which states {lean}`∀ {n m : Nat}, max n m = if n ≤ m then m else n`, {tactic}`grind` can then case split on the inequality.
In the branch {lean}`3 ≤ 4 * n`, `cutsat` again uses modularity to prove `4 * n ≠ 2 + n`.
In the branch {lean}`4 * n < 3`, `cutsat` quickly determines {lean}`n = 0`, and then notices that {lean}`4 * 0 ≠ 2 + 0`.

This has been, of course, a quite artificial example!
In practice, this sort of automatic integration of different reasoning modes is very powerful: the central “whiteboard” which tracks instantiated theorems and equivalence classes can hand off relevant terms and equalities to the appropriate modules (here, `cutsat` and Gröbner bases), which can then return new facts to the whiteboard.

::::
