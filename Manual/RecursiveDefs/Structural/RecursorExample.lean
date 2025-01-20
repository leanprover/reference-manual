/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Verso.Genre Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


#doc (Manual) "Recursion Example (for inclusion elsewhere)" =>


```lean (show := false)
section
variable (n k : Nat) (mot : Nat → Sort u)
```
:::example "Recursion vs Recursors"
Addition of natural numbers can be defined via recursion on the second argument.
This function is straightforwardly structurally recursive.
```lean
def add (n : Nat) : Nat → Nat
  | .zero => n
  | .succ k => .succ (add n k)
```

Defined using {name}`Nat.rec`, it is much further from the notations that most people are used to.
```lean
def add' (n : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    n
    (fun k soFar => .succ soFar)
```

Structural recursive calls made on data that isn't the immediate child of the function parameter requires either creativity or a complex yet systematic encoding.
```lean
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
One way to think about this function is as a structural recursion that flips a bit at each call, only incrementing the result when the bit is set.
```lean
def helper : Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Bool → Nat)
    (fun _ => 0)
    (fun _ soFar =>
      fun b =>
        (if b then Nat.succ else id) (soFar !b))

def half' (n : Nat) : Nat := helper n false
```
```lean (name := halfTest)
#eval [0, 1, 2, 3, 4, 5, 6, 7, 8].map half'
```
```leanOutput halfTest
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

Instead of creativity, a general technique called {deftech}[course-of-values recursion] can be used.
Course-of-values recursion uses helpers that can be systematically derived for every inductive type, defined in terms of the recursor; Lean derives them automatically.
For every {lean}`Nat` {lean}`n`, the type {lean}`n.below (motive := mot)` provides a value of type {lean}`mot k` for all {lean}`k < n`, represented as an iterated {TODO}[xref sigma] dependent pair type.
The course-of-values recursor {name}`Nat.brecOn` allows a function to use the result for any smaller {lean}`Nat`.
Using it to define the function is inconvenient:
```lean
noncomputable def half'' (n : Nat) : Nat :=
  Nat.brecOn n (motive := fun _ => Nat)
    fun k soFar =>
      match k, soFar with
      | 0, _ | 1, _ => 0
      | _ + 2, ⟨_, ⟨h, _⟩⟩ => h + 1
```
The function is marked {keywordOf Lean.Parser.Command.declaration}`noncomputable` because the compiler doesn't support generating code for course-of-values recursion, which is intended for reasoning rather that efficient code.
The kernel can still be used to test the function, however:
```lean (name := halfTest2)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest2
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

The dependent pattern matching in the body of {lean}`half''` can also be encoded using recursors (specifically, {name}`Nat.casesOn`), if necessary:
```lean
noncomputable def half''' (n : Nat) : Nat :=
  n.brecOn (motive := fun _ => Nat)
    fun k =>
      k.casesOn
        (motive :=
          fun k' =>
            (k'.below (motive := fun _ => Nat)) →
            Nat)
        (fun _ => 0)
        (fun k' =>
          k'.casesOn
            (motive :=
              fun k'' =>
                (k''.succ.below (motive := fun _ => Nat)) →
                Nat)
            (fun _ => 0)
            (fun _ soFar => soFar.2.1.succ))
```

This definition still works.
```lean (name := halfTest3)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest3
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

However, it is now far from the original definition and it has become difficult for most people to understand.
Recursors are an excellent logical foundation, but not an easy way to write programs or proofs.
:::
```lean (show := false)
end
```
