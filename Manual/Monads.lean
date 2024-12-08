/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Manual.Monads.Syntax
import Manual.Monads.Zoo
import Manual.Monads.Lift
import Manual.Monads.API
import Manual.Monads.Laws

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false
set_option maxRecDepth 1024

#doc (Manual) "Functors, Monads and `do`-Notation" =>

%%%
tag := "monads-and-do"
%%%

The type classes {name}`Functor`, {name}`Applicative`, and {name}`Monad` provide fundamental tools for functional programming.{margin}[An introduction to programming with these abstractions is available in [_Functional Programming in Lean_](https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad.html).]
While they are inspired by the concepts of functors and monads in category theory, the versions used for programming are more limited.
The type classes in Lean's standard library represent the concepts as used for programming, rather than the general mathematical definition.

Instances of {deftech}[{name}`Functor`] allow an operation to be applied consistently throughout some polymorphic context.
Examples include transforming each element of a list by applying a function and creating new {lean}`IO` actions by arranging for a pure function to be applied to the result of an existing {lean}`IO` action.
Instances of {deftech}[{name}`Monad`] allow side effects with data dependencies to be encoded; examples include using a tuple to simulate mutable state, a sum type to simulate exceptions, and representing actual side effects with {lean}`IO`.
{deftech}[{name}`Applicative` functors] occupy a middle ground: like monads, they allow functions computed with effects to be applied to arguments that are computed with effects, but they do not allow sequential data dependencies where the output of an effect forms an input into another effectful operation.

The additional type classes {name}`Pure`, {name}`Bind`, {name}`SeqLeft`, {name}`SeqRight`, and {name}`Seq` capture individual operations from {name}`Applicative` and {name}`Monad`, allowing them to be overloaded and used with types that are not necessarily {name}`Applicative` functors or {name}`Monad`s.
The {name}`Alternative` type class describes applicative functors that additionally have some notion of failure and recovery.


{docstring Functor}

{docstring Pure}

{docstring Seq}

{docstring SeqLeft}

{docstring SeqRight}

{docstring Applicative}


:::::keepEnv

```lean (show := false)
section
variable {α : Type u} {β : Type u}
variable {n : Nat}
```

::::example "Lists with Lengths as Applicative Functors"

The structure {name}`LenList` pairs a list with a proof that it has the desired length.
As a consequence, its `zipWith` operator doesn't require a fallback in case the lengths of its inputs differ.

```lean
structure LenList (length : Nat) (α : Type u) where
  list : List α
  lengthOk : list.length = length

def LenList.head (xs : LenList (n + 1) α) : α :=
  xs.list.head <| by
    intro h
    cases xs
    simp_all [List.length]
    subst_eqs

def LenList.tail (xs : LenList (n + 1) α) : LenList n α :=
  match xs with
  | ⟨_ :: xs', _⟩ => ⟨xs', by simp_all⟩

def LenList.map (f : α → β) (xs : LenList n α) : LenList n β where
  list := xs.list.map f
  lengthOk := by
    cases xs
    simp [List.length_map, *]

def LenList.zipWith (f : α → β → γ)
    (xs : LenList n α) (ys : LenList n β) :
    LenList n γ where
  list := xs.list.zipWith f ys.list
  lengthOk := by
    cases xs; cases ys
    simp [List.length_zipWith, *]
```

The well-behaved {name}`Applicative` instance applies functions to arguments element-wise.
Because {name}`Applicative` extends {name}`Functor`, a separate {name}`Functor` instance is not necessary, and {name Functor.map}`map` can be defined as part of the {name}`Applicative` instance.

```lean
instance : Applicative (LenList n) where
  map := LenList.map
  pure x := {
    list := List.replicate n x
    lengthOk := List.length_replicate _ _
  }
  seq fs xs := fs.zipWith (· ·) (xs ())
```

The well-behaved {name}`Monad` instance takes the diagonal of the results of applying the function:

```lean
@[simp]
theorem LenList.list_length_eq (xs : LenList n α) : xs.list.length = n := by
  cases xs
  simp [*]

def LenList.diagonal (square : LenList n (LenList n α)) : LenList n α :=
  match n with
  | 0 => ⟨[], rfl⟩
  | n' + 1 => {
    list := square.head.head :: (square.tail.map (·.tail)).diagonal.list,
    lengthOk := by simp
  }
```

```lean (show := false)
end
```
::::
:::::


{docstring Alternative}

{docstring Bind}

{docstring Monad}

{include 0 Manual.Monads.Laws}

{include 0 Manual.Monads.Lift}

{include 0 Manual.Monads.Syntax}

{include 0 Manual.Monads.API}

{include 0 Manual.Monads.Zoo}
