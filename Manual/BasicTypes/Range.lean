/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Interaction.FormatRepr

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option format.width 60

#doc (Manual) "Ranges" =>
%%%
tag := "ranges"
%%%

A {deftech}_range_ represents a series of consecutive elements of some type, from a lower bound to an upper bound.
The bounds may be open, in which case the bound value is not part of the range, or closed, in which case the bound value is part of the range.
Either bound may be omitted, in which case the range extends infinitely in the corresponding direction.

Ranges have dedicated syntax that consists of a starting point, {keyword}`...`, and an ending point.
The starting point may be either `*`, which denotes a range that continues infinitely downwards, or a term, which denotes a range with a specific starting value.
By default, ranges are left-closed: they contain their starting points.
A trailing `<` indicates that the range is left-open and does not contain its starting point.
The ending point may be `*`, in which case the range continues infinitely upwards, or a term, which denotes a range with a specific ending value.
By default, ranges are right-open: they do not contain their ending points.
The ending point may be prefixed with `<` to indicate that it is right-open; this is the default and does not change the meaning, but may be easier to read.
It may also be prefixed with `=` to indicate that the range is right-closed and contains its ending point.


:::example "Ranges of Natural Numbers"
The range that contains the numbers {lean}`3` through {lean}`6` can be written in a variety of ways:
```lean (name := rng1)
#eval (3...7).toList
```
```leanOutput rng1
[3, 4, 5, 6]
```
```lean (name := rng2)
#eval (3...=6).toList
```
```leanOutput rng2
[3, 4, 5, 6]
```
```lean (name := rng3)
#eval (2<...=6).toList
```
```leanOutput rng3
[3, 4, 5, 6]
```
:::

:::example "Finite and Infinite Ranges"
This range cannot be converted to a list, because it is infinite:
```lean (name := rng4) +error
#eval (3...*).toList
```
Finiteness of a left-closed, right-unbounded range is indicated by the presence of an instance of {name}`Std.Rxi.IsAlwaysFinite`, which does not exist for {name}`Nat`.
{name}`Std.Rco` is the type of these ranges, and the name {name}`Std.Rxi.IsAlwaysFinite` indicates that it determines finiteness for all right-unbounded ranges.
```leanOutput rng4
failed to synthesize instance of type class
  Std.Rxi.IsAlwaysFinite Nat

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

Attempting to enumerate the negative integers leads to a similar error, this time because there is no way to determine the least element:
```lean (name := intrange) +error
#eval (*...(0 : Int)).toList
```
```leanOutput intrange
failed to synthesize instance of type class
  Std.PRange.Least? Int

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

Unbounded ranges in finite types indicate that the range extends to the greatest element of the type.
Because {name}`UInt8` has 256 elements, this range contains 253 elements:
```lean (name := uintrange)
#eval ((3 : UInt8)...*).toArray.size
```
```leanOutput uintrange
253
```

:::



:::syntax term (title := "Range Syntax")

This range is left-closed, right-open, and indicates {name}`Std.Rco`:
```grammar
$a...$b
```

This range is left-closed, right-open, and indicates {name}`Std.Rco`:
```grammar
$a...<$b
```

This range is left-closed, right-closed, and indicates {name}`Std.Rcc`:
```grammar
$a...=$b
```

This range is left-closed, right-infinite, and indicates {name}`Std.Rci`:
```grammar
$a...*
```

This range is left-open, right-open, and indicates {name}`Std.Roo`:
```grammar
$a<...$b
```

This range is left-open, right-open, and indicates {name}`Std.Roo`:
```grammar
$a<...<$b
```

This range is left-open, right-closed, and indicates {name}`Std.Roc`:
```grammar
$a<...=$b
```
This range is left-open, right-infinite, and indicates {name}`Std.Roi`:
```grammar
$a<...*
```
This range is left-infinite, right-open, and indicates {name}`Std.Rio`:
```grammar
*...$b
```

This range is left-infinite, right-open, and indicates {name}`Std.Ric`:
```grammar
*...<$b
```

This range is left-infinite, right-closed, and indicates {name}`Std.Ric`:
```grammar
*...=$b
```

This range is infinite on both sides, and indicates {name}`Std.Rii`:
```grammar
*...*
```
:::

# Range Types

{docstring Std.Rco +allowMissing}

{docstring Std.Rco.iter}

{docstring Std.Rco.toArray}

{docstring Std.Rco.toList}

{docstring Std.Rco.size}

{docstring Std.Rco.isEmpty}

{docstring Std.Rcc +allowMissing}

{docstring Std.Rcc.iter}

{docstring Std.Rcc.toArray}

{docstring Std.Rcc.toList}

{docstring Std.Rcc.size}

{docstring Std.Rcc.isEmpty}

{docstring Std.Rci +allowMissing}

{docstring Std.Rci.iter}

{docstring Std.Rci.toArray}

{docstring Std.Rci.toList}

{docstring Std.Rci.size}

{docstring Std.Rci.isEmpty}

{docstring Std.Roo +allowMissing}

{docstring Std.Roo.iter}

{docstring Std.Roo.toArray}

{docstring Std.Roo.toList}

{docstring Std.Roo.size}

{docstring Std.Roo.isEmpty}

{docstring Std.Roc +allowMissing}

{docstring Std.Roc.iter}

{docstring Std.Roc.toArray}

{docstring Std.Roc.toList}

{docstring Std.Roc.size}

{docstring Std.Roc.isEmpty}

{docstring Std.Roi +allowMissing}

{docstring Std.Roi.iter}

{docstring Std.Roi.toArray}

{docstring Std.Roi.toList}

{docstring Std.Roi.size}

{docstring Std.Roi.isEmpty}

{docstring Std.Rio +allowMissing}

{docstring Std.Rio.iter}

{docstring Std.Rio.toArray}

{docstring Std.Rio.toList}

{docstring Std.Rio.size}

{docstring Std.Rio.isEmpty}

{docstring Std.Ric +allowMissing}

{docstring Std.Ric.iter}

{docstring Std.Ric.toArray}

{docstring Std.Ric.toList}

{docstring Std.Ric.size}

{docstring Std.Ric.isEmpty}

{docstring Std.Rii}

{docstring Std.Rii.iter}

{docstring Std.Rii.toArray}

{docstring Std.Rii.toList}

{docstring Std.Rii.size}

{docstring Std.Rii.isEmpty}

# Range-Related Type Classes

{docstring Std.PRange.UpwardEnumerable}

{docstring Std.PRange.UpwardEnumerable.LE}

{docstring Std.PRange.UpwardEnumerable.LT}

{docstring Std.PRange.LawfulUpwardEnumerable}

{docstring Std.PRange.Least?}

{docstring Std.PRange.InfinitelyUpwardEnumerable +allowMissing}

{docstring Std.PRange.LinearlyUpwardEnumerable +allowMissing}

{docstring Std.Rxi.IsAlwaysFinite +allowMissing}

{docstring Std.Rxi.HasSize}

{docstring Std.Rxc.IsAlwaysFinite +allowMissing}

{docstring Std.Rxc.HasSize}

# Implementing Ranges

The built-in range types may be used with any type, but their usefulness depends on the presence of certain type class instances.
Generally speaking, ranges are either checked for membership, enumerated or iterated over.
To check whether an value is contained in a range, {name}`DecidableLT` and {name}`DecidableLE` instances are used to compare the value to the range's respective open and closed endpoints.
To get an iterator for a range, instances of {name}`Std.PRange.UpwardEnumerable` and {name}`Std.PRange.LawfulUpwardEnumerable` are all that's needed.
To iterate directly over it in a {keywordOf Lean.Parser.Term.doFor}`for` loop, {name}`Std.PRange.LawfulUpwardEnumerableLE` and {name}`Std.PRange.LawfulUpwardEnumerableLT` are required as well.
To enumerate a range (e.g. by calling {name Std.Rco.toList}`toList`), it must be proven finite.
This is done by supplying instances of {name}`Std.Rxi.IsAlwaysFinite`, {name}`Std.Rxc.IsAlwaysFinite`, or {name}`Std.Rxo.IsAlwaysFinite`.

::::example "Implementing Ranges" (open := true)
The enumeration type {name}`Day` represents the days of the week:
```lean
inductive Day where
  | mo | tu | we | th | fr | sa | su
deriving Repr
```

:::paragraph
```imports -show
import Std.Data.Iterators
```

While it's already possible to use this type in ranges, they're not particularly useful.
There's no membership instance:
```lean +error (name := noMem)
#eval Day.we ∈ (Day.mo...=Day.fr)
```
```leanOutput noMem
failed to synthesize instance of type class
  Membership Day (Std.Rcc Day)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
Ranges can't be iterated over:
```lean +error (name := noIter)
#eval show IO Unit from
  for d in Day.mo...=Day.fr do
    IO.println s!"It's {repr d}"
```
```leanOutput noIter
failed to synthesize instance for 'for_in%' notation
  ForIn (EIO IO.Error) (Std.Rcc Day) ?m.11
```
Nor can they be enumerated, even though the type is finite:
```lean +error (name := noEnum)
#eval (Day.sa...*).toList
```
```leanOutput noEnum
failed to synthesize instance of type class
  Std.PRange.UpwardEnumerable Day

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
:::

:::paragraph
Membership tests require {name}`DecidableLT` and {name}`DecidableLE` instances.
An easy way to get these is to number each day, and compare the numbers:
```lean
def Day.toNat : Day → Nat
  | mo => 0
  | tu => 1
  | we => 2
  | th => 3
  | fr => 4
  | sa => 5
  | su => 6

instance : LT Day where
  lt d1 d2 := d1.toNat < d2.toNat

instance : LE Day where
  le d1 d2 := d1.toNat ≤ d2.toNat

instance : DecidableLT Day :=
  fun d1 d2 => inferInstanceAs (Decidable (d1.toNat < d2.toNat))

instance : DecidableLE Day :=
  fun d1 d2 => inferInstanceAs (Decidable (d1.toNat ≤ d2.toNat))
```
:::

:::paragraph
With these instances available, membership tests work as expected:
```lean
def Day.isWeekday (d : Day) : Bool := d ∈ Day.mo...Day.sa
```
```lean (name := thursday)
#eval Day.th.isWeekday
```
```leanOutput thursday
true
```
```lean (name := saturday)
#eval Day.sa.isWeekday
```
```leanOutput saturday
false
```
:::

:::paragraph
Iteration and enumeration are both variants on repeatedly applying a successor function until either the upper bound of the range or the largest element of the type is reached.
This successor function is {name}`Std.PRange.UpwardEnumerable.succ?`.
It's also convenient to have a definition of the function in {name}`Day`'s namespace for use with generalized field notation:
```lean
def Day.succ? : Day → Option Day
  | mo => some tu
  | tu => some we
  | we => some th
  | th => some fr
  | fr => some sa
  | sa => some su
  | su => none

instance : Std.PRange.UpwardEnumerable Day where
  succ? := Day.succ?
```
:::

Iteration also requires a proof that the implementation of {name Std.PRange.UpwardEnumerable.succ?}`succ?` is sensible.
Its properties are expressed in terms of {name}`Std.PRange.UpwardEnumerable.succMany?`, which iterates the application of {name Std.PRange.UpwardEnumerable.succ?}`succ?` a certain number of times and has a default implementation in terms of {name}`Nat.repeat` and {name Std.PRange.UpwardEnumerable.succ?}`succ?`.
In particular, an instance of {name Std.PRange.LawfulUpwardEnumerable}`LawfulUpwardEnumerable` requires proofs that {name}`Std.PRange.UpwardEnumerable.succMany?` corresponds to the default implementation along with a proof that repeatedly applying the successor never yields the same element again.

:::paragraph
The first step is to write two helper lemmas for the two proofs about {name Std.PRange.UpwardEnumerable.succMany?}`succMany?`.
While they could be written inline in the instance declaration, it's convenient for them to have the {attrs}`@[simp]` attribute.
```lean
@[simp]
theorem Day.succMany?_zero (d : Day) :
  Std.PRange.succMany? 0 d = some d := by
  simp [Std.PRange.succMany?, Nat.repeat]

@[simp]
theorem Day.succMany?_add_one (n : Nat) (d : Day) :
    Std.PRange.succMany? (n + 1) d =
    (Std.PRange.succMany? n d).bind Std.PRange.succ? := by
  simp [Std.PRange.succMany?, Nat.repeat, Std.PRange.succ?]
```

Proving that there are no cycles in successor uses a convenient helper lemma that calculates the number of successor steps between any two days.
It is marked {attrs}`@[grind →]` because when assumptions that match its premises are present, it adds a great deal of new information:
```lean
@[grind →]
theorem Day.succMany?_steps {d d' : Day} {steps} :
    Std.PRange.succMany? steps d = some d' →
    if d ≤ d' then steps = d'.toNat - d.toNat
    else False := by
  intro h
  match steps with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 =>
    cases d <;> cases d' <;>
    simp_all +decide [Std.PRange.succMany?, Nat.repeat, Day.succ?]
  | n + 7 =>
    simp at h
    cases h' : (Std.PRange.succMany? n d) with
    | none =>
      simp_all
    | some d'' =>
      rw [h'] at h
      cases d'' <;> contradiction
```
With that helper, the proof is quite short:
```lean
instance : Std.PRange.LawfulUpwardEnumerable Day where
  ne_of_lt d1 d2 h := by grind [Std.PRange.UpwardEnumerable.LT]
  succMany?_zero := Day.succMany?_zero
  succMany?_add_one := Day.succMany?_add_one
```
:::

:::paragraph
Proving the three kinds of enumerable ranges to be finite makes it possible to enumerate ranges of days:
```lean
instance : Std.Rxo.IsAlwaysFinite Day where
  finite init hi := ⟨7, by cases init <;> simp [Std.PRange.succ?, Day.succ?]⟩

instance : Std.Rxc.IsAlwaysFinite Day where
  finite init hi := ⟨7, by cases init <;> simp [Std.PRange.succ?, Day.succ?]⟩

instance : Std.Rxi.IsAlwaysFinite Day where
  finite init := ⟨7, by cases init <;> rfl⟩
```
```lean (name := allWeekdays)
def allWeekdays : List Day := (Day.mo...Day.sa).toList
#eval allWeekdays
```
```leanOutput allWeekdays
[Day.mo, Day.tu, Day.we, Day.th, Day.fr]
```
Adding a {name}`Std.PRange.Least?` instance allows enumeration of left-unbounded ranges:
```lean (name := allWeekdays')
instance : Std.PRange.Least? Day where
  least? := some .mo

def allWeekdays' : List Day := (*...Day.sa).toList
#eval allWeekdays'
```
```leanOutput allWeekdays'
[Day.mo, Day.tu, Day.we, Day.th, Day.fr]
```
It's also possible to create an iterator that can be enumerated, but it can't yet be used with {keywordOf Lean.Parser.Term.doFor}`for`:
```lean (name := iterEnum)
#eval (Day.we...Day.fr).iter.toList
```
```leanOutput iterEnum
[Day.we, Day.th]
```
```lean (name := iterForNo) +error
#eval show IO Unit from do
  for d in (Day.mo...Day.th).iter do
    IO.println s!"It's {repr d}."
```
```leanOutput iterForNo
failed to synthesize instance for 'for_in%' notation
  ForIn (EIO IO.Error) (Std.Iter Day) ?m.12
```

:::

:::paragraph
The last step to enable iteration, thus making ranges of days fully-featured, is to prove that the less-than and less-than-or-equal-to relations on {name}`Day` correspond to the notions of inequality that are derived from iterating the successor function.
This is captured in the classes {name}`Std.PRange.LawfulUpwardEnumerableLT` and {name}`Std.PRange.LawfulUpwardEnumerableLE`, which require that the two notions are logically equivalent:
```lean
instance : Std.PRange.LawfulUpwardEnumerableLT Day where
  lt_iff d1 d2 := by
    constructor
    . intro lt
      simp only [Std.PRange.UpwardEnumerable.LT, Day.succMany?_add_one]
      exists d2.toNat - d1.toNat.succ
      cases d1 <;> cases d2 <;>
      simp_all [Day.toNat, Std.PRange.succ?, Day.succ?] <;>
      contradiction
    . intro ⟨steps, eq⟩
      have := Day.succMany?_steps eq
      cases d1 <;> cases d2 <;>
      simp only [if_false_right] at this <;>
      cases this <;> first | decide | contradiction

instance : Std.PRange.LawfulUpwardEnumerableLE Day where
  le_iff d1 d2 := by
    constructor
    . intro le
      simp only [Std.PRange.UpwardEnumerable.LE]
      exists d2.toNat - d1.toNat
      cases d1 <;> cases d2 <;>
      simp_all [Day.toNat, Std.PRange.succ?, Day.succ?] <;>
      contradiction
    . intro ⟨steps, eq⟩
      have := Day.succMany?_steps eq
      cases d1 <;> cases d2 <;>
      simp only [if_false_right] at this <;>
      cases this <;> grind
```
:::

:::paragraph
It is now possible to iterate over ranges of days:
```lean (name := done)
#eval show IO Unit from do
  for x in (Day.mo...Day.th).iter do
    IO.println s!"It's {repr x}"
```
```leanOutput done
It's Day.mo
It's Day.tu
It's Day.we
```
:::

::::

# Ranges and Slices

Range syntax can be used with data structures that support slicing to select a slice of the structure.

:::example "Slicing Lists"
Lists may be sliced with any of the interval types:
```lean
def groceries :=
  ["apples", "bananas", "coffee", "dates", "endive", "fennel"]
```

```lean (name := rco)
#eval groceries[1...4] |>.toList
```
```leanOutput rco
["bananas", "coffee", "dates"]
```
```lean (name := rcc)
#eval groceries[1...=4] |>.toList
```
```leanOutput rcc
["bananas", "coffee", "dates", "endive"]
```
```lean (name := rci)
#eval groceries[1...*] |>.toList
```
```leanOutput rci
["bananas", "coffee", "dates", "endive", "fennel"]
```
```lean (name := roo)
#eval groceries[1<...4] |>.toList
```
```leanOutput roo
["coffee", "dates"]
```
```lean (name := roc)
#eval groceries[1<...=4] |>.toList
```
```leanOutput roc
["coffee", "dates", "endive"]
```
```lean (name := ric)
#eval groceries[*...=4] |>.toList
```
```leanOutput ric
["apples", "bananas", "coffee", "dates", "endive"]
```
```lean (name := rio)
#eval groceries[*...4] |>.toList
```
```leanOutput rio
["apples", "bananas", "coffee", "dates"]
```
```lean (name := rii)
#eval groceries[*...*] |>.toList
```
```leanOutput rii
["apples", "bananas", "coffee", "dates", "endive", "fennel"]
```


:::

:::example "Custom Slices"
A {name}`Triple` contains three values of the same type:
```lean
structure Triple (α : Type u) where
  fst : α
  snd : α
  thd : α
deriving Repr
```
Positions in a triple may be any of the fields, or just after {name Triple.thd}`thd`:
```lean
inductive TriplePos where
  | fst | snd | thd | done
deriving Repr
```
A slice of a triple consists of a triple, a starting position, and a stopping position.
The starting position is inclusive, and the stopping position exclusive:
```lean
structure TripleSlice (α : Type u) where
  triple : Triple α
  start : TriplePos
  stop : TriplePos
deriving Repr
```
Ranges of {name}`TriplePos` can be used to select a slice from a triple by implementing instances of each supported range type's {name Std.Rco.Sliceable}`Sliceable` class.
For example, {name}`Std.Rco.Sliceable` allows left-closed, right-open ranges to be used to slice {name}`Triple`s:
```lean
instance : Std.Rco.Sliceable (Triple α) TriplePos (TripleSlice α) where
  mkSlice triple range :=
    { triple, start := range.lower, stop := range.upper }
```
```lean (name := slice)
def abc : Triple Char := ⟨'a', 'b', 'c'⟩

open TriplePos in
#eval abc[snd...thd]
```
```leanOutput slice
{ triple := { fst := 'a', snd := 'b', thd := 'c' }, start := TriplePos.snd, stop := TriplePos.thd }
```
Infinite ranges have only a lower bound:
```lean (name := slice2)
instance : Std.Rci.Sliceable (Triple α) TriplePos (TripleSlice α) where
  mkSlice triple range :=
    { triple, start := range.lower, stop := .done }

open TriplePos in
#eval abc[snd...*]
```
```leanOutput slice2
{ triple := { fst := 'a', snd := 'b', thd := 'c' }, start := TriplePos.snd, stop := TriplePos.done }
```

:::

{docstring Std.Rco.Sliceable +allowMissing}

{docstring Std.Rcc.Sliceable +allowMissing}

{docstring Std.Rci.Sliceable +allowMissing}

{docstring Std.Roo.Sliceable +allowMissing}

{docstring Std.Roc.Sliceable +allowMissing}

{docstring Std.Roi.Sliceable +allowMissing}

{docstring Std.Rio.Sliceable +allowMissing}

{docstring Std.Ric.Sliceable +allowMissing}

{docstring Std.Rii.Sliceable +allowMissing}
