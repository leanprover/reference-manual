/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Maps.TreeSet
import Manual.BasicTypes.Maps.TreeMap

import Std.Data.HashMap
import Std.Data.HashMap.Raw
import Std.Data.HashMap.RawLemmas
import Std.Data.DHashMap
import Std.Data.DHashMap.Raw
import Std.Data.DHashMap.RawLemmas
import Std.Data.ExtHashMap
import Std.Data.TreeMap
import Std.Data.DTreeMap
import Std.Data.DTreeMap.Raw
import Std.Data.ExtHashSet
import Std.Data.TreeSet
import Std.Data.HashSet
import Std.Data.HashSet.Raw
import Std.Data.HashSet.RawLemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option maxHeartbeats 1000000

#doc (Manual) "Maps and Sets" =>
%%%
tag := "maps"
%%%

A {deftech}_map_ is a data structure that associates keys with values.
They are also referred to as {deftech}_dictionaries_, {deftech}_associative arrays_, or simply as hash tables.


::::paragraph
In Lean, maps may have the following properties:

: Representation

  The in-memory representation of a map may be either a tree or a hash table.
  Tree-based representations are better when the {ref "reference-counting"}[reference] to the data structure is shared, because hash tables are based on {ref "Array"}[arrays].
  Arrays are copied in full on modification when the reference is not unique, while only the path from the root of the tree to the modified nodes must be copied on modification of a tree.
  Hash tables, on the other hand, can be more efficient when references are not shared, because non-shared arrays can be modified in constant time.
  Furthermore, tree-based maps store data in order and thus support ordered traversals of the data.

: Extensionality

  Maps can be viewed as partial functions from keys to values.
  {deftech}_Extensional maps_{index (subterm := "extensional")}[map] are maps for which propositional equality matches this interpretation.
  This can be convenient for reasoning, but it also rules out some useful operations that would be able to distinguish between them.
  In general, extensional maps should be used only when needed for verification.

: Dependent or Not

  A {deftech}_dependent map_{index (subterm := "dependent")}[map] is one in which the type of each value is determined by its corresponding key, rather than being constant.
  Dependent maps have more expressive power, but are also more difficult to use.
  They impose more requirements on their users.
  For example, many operations on {name Std.DHashMap}`DHashMap` require {name}`LawfulBEq` instances rather than {name}`BEq`.

::::

::::: leanSection

```lean -show
open Std
```


:::table +header
*
  - Map
  - Representation
  - Extensional?
  - Dependent?

*
  - {name}`TreeMap`
  - Tree
  - No
  - No

*
  - {name}`DTreeMap`
  - Tree
  - No
  - Yes

*
  - {name}`HashMap`
  - Hash Table
  - No
  - No

*
  - {name}`DHashMap`
  - Hash Table
  - No
  - Yes

*
  - {name}`ExtHashMap`
  - Hash Table
  - Yes
  - No

*
  - {name}`ExtDHashMap`
  - Hash Table
  - Yes
  - Yes

:::

:::::

A map can always be used as a set by setting its type of values to {name}`Unit`.
The following set types are provided:
 * {name}`Std.HashSet` is a set based on hash tables. Its performance characteristics are like those of {name}`Std.HashMap`: it is based on arrays and can be efficiently updated, but only when not shared.
 * {name}`Std.TreeSet` is a set based on balanced trees. Its performance characteristics are like those of {name}`Std.TreeMap`.
 * {name}`Std.ExtHashSet` is an extensional hash set type that matches the mathematical notion of finite sets: two sets are equal if they contain the same elements.


# Library Design

All the basic operations on maps and sets are fully verified.
They are proven correct with respect to simpler models implemented with lists.
At the same time, maps and sets have predictable performance.

Some types include additional operations that are not yet fully verified.
These operations are useful, and not all programs need full verification.
Examples include {name Std.HashMap.partition}`HashMap.partition` and {name Std.TreeMap.filterMap}`TreeMap.filterMap`.

## Fused Operations

It is common to modify a table based on its pre-existing contents.
To avoid having to traverse a data structure twice, many query/modification pairs are provided in “fused” variants that perform a query while modifying a map or set.
In some cases, the result of the query affects the modification.

For example, {name}`Std.HashMap` provides {name Std.HashMap.containsThenInsert}`containsThenInsert`, which inserts a key-value pair into a map while signalling whether it was previously found, and {name Std.HashMap.containsThenInsertIfNew}`containsThenInsertIfNew`, which inserts the new mapping only if it was not previously present.
The {name Std.HashMap.alter}`alter` function modifies the value for a given key without having to search for the key multiple times; the alternation is performed by a function in which missing values are represented by {name}`none`.

## Raw Data and Invariants
%%%
tag := "raw-data"
%%%

Both hash-based and tree-based maps rely on certain internal well-formedness invariants, such as that trees are balanced and ordered.
In Lean's standard library, these data structures are represented as a pair of the underlying data with a proof that it is well formed.
This fact is mostly an internal implementation detail; however, it is relevant to users in one situation: this representation prevents them from being used in {tech}[nested inductive types].

To enable their use in nested inductive types, the standard library provides “{deftech}[raw]” variants of each container along with separate “unbundled” versions of their invariants.
These use the following naming convention:
 * `T.Raw` is the version of type `T` without its invariants. For example, {name}`Std.HashMap.Raw` is a version of {name}`Std.HashMap` without the embedded proofs.
 * `T.Raw.WF` is the corresponding well-formedness predicate. For example, {name}`Std.HashMap.Raw.WF` asserts that a {name}`Std.HashMap.Raw` is well-formed.
 * Each operation on `T`, called `T.f`, has a corresponding operation on `T.Raw` called `T.Raw.f`. For example, {name}`Std.HashMap.Raw.insert` is the version of {name}`Std.HashMap.insert` to be used with raw hash maps.
 * Each operation `T.Raw.f` has an associated well-formedness lemma `T.Raw.WF.f`. For example, {name}`Std.HashMap.Raw.WF.insert` asserts that inserting a new key-value pair into a well-formed raw hash map results in a well-formed raw hash map.

Because the vast majority of use cases do not require them, not all lemmas about raw types are imported by default with the data structures.
It is usually necessary to import `Std.Data.T.RawLemmas` (where `T` is the data structure in question).

A nested inductive type that occurs inside a map or set should be defined in three stages:

 1. First, define a raw version of the nested inductive type that uses the raw version of the map or set type. Define any necessary operations.
 2. Next, define an inductive predicate that asserts that all maps or sets in the raw nested type are well formed. Show that the operations on the raw type preserve well-formedness.
 3. Construct an appropriate interface to the nested inductive type by defining an API that proves well-formedness properties as needed, hiding them from users.

:::example "Nested Inductive Types with `Std.HashMap`"

```imports -show
import Std
```

This example requires that `Std.Data.HashMap.RawLemmas` is imported.
To keep the code shorter, the `Std` namespace is opened:
```lean
open Std
```

The map of an adventure game may consist of a series of rooms, connected by passages.
Each room has a description, and each passage faces in a particular direction.
This can be represented as a recursive structure.

```lean +error (name:=badNesting) -keep
structure Maze where
  description : String
  passages : HashMap String Maze
```

This definition is rejected:

```leanOutput badNesting
(kernel) application type mismatch
  DHashMap.Raw.WF inner
argument has type
  _nested.Std.DHashMap.Raw_3
but function has type
  (DHashMap.Raw String fun x => Maze) → Prop
```

Making this work requires separating the well-formedness predicates from the structure.
The first step is to redefine the type without embedded hash map invariants:

```lean
structure RawMaze where
  description : String
  passages : Std.HashMap.Raw String RawMaze
```

The most basic raw maze has no passages:
```lean
def RawMaze.base (description : String) : RawMaze where
  description := description
  passages := ∅
```

A passage to a further maze can be added to a raw maze using {name}`RawMaze.insert`:
```lean
def RawMaze.insert (maze : RawMaze)
    (direction : String) (next : RawMaze) : RawMaze :=
  { maze with
    passages := maze.passages.insert direction next
  }
```

The second step is to define a well-formedness predicate for {name}`RawMaze` that ensures that each included hash map is well-formed.
If the {name RawMaze.passages}`passages` field itself is well-formed, and all raw mazes included in it are well-formed, then a raw maze is well-formed.

```lean
inductive RawMaze.WF : RawMaze → Prop
  | mk {description passages} :
    (∀ (dir : String) v, passages[dir]? = some v → WF v) →
    passages.WF →
    WF { description, passages := passages }
```

Base mazes are well-formed, and inserting a passage to a well-formed maze into some other well-formed maze produces a well-formed maze:
```lean
theorem RawMaze.base_wf (description : String) :
    RawMaze.WF (.base description) := by
  constructor
  . intro v h h'
    simp [Std.HashMap.Raw.getElem?_empty] at *
  . exact HashMap.Raw.WF.empty

def RawMaze.insert_wf (maze : RawMaze) :
    WF maze → WF next → WF (maze.insert dir next) := by
  let ⟨desc, passages⟩ := maze
  intro ⟨wfMore, wfPassages⟩ wfNext
  constructor
  . intro dir' v
    rw [HashMap.Raw.getElem?_insert wfPassages]
    split <;> intros <;> simp_all [wfMore dir']
  . simp_all [HashMap.Raw.WF.insert]
```

Finally, a more friendly interface can be defined that frees users from worrying about well-formedness.
A {name}`Maze` bundles up a {name}`RawMaze` with a proof that it is well-formed:
```lean
structure Maze where
  raw : RawMaze
  wf : raw.WF
```

The {name Maze.base}`base` and {name Maze.insert}`insert` operators take care of the well-formedness proof obligations:
```lean
def Maze.base (description : String) : Maze where
  raw := .base description
  wf := by apply RawMaze.base_wf

def Maze.insert (maze : Maze)
    (dir : String) (next : Maze) : Maze where
  raw := maze.raw.insert dir next.raw
  wf := RawMaze.insert_wf maze.raw maze.wf next.wf
```

Users of the {name}`Maze` API may either check the description of the current maze or attempt to go in a direction to a new maze:
```lean
def Maze.description (maze : Maze) : String :=
  maze.raw.description

def Maze.go? (maze : Maze) (dir : String) : Option Maze :=
  match h : maze.raw.passages[dir]? with
  | none => none
  | some m' =>
    Maze.mk m' <| by
      let ⟨r, wf⟩ := maze
      let ⟨wfAll, _⟩ := wf
      apply wfAll dir
      apply h
```
:::

## Suitable Operators for Uniqueness

Care should be taken when working with data structures to ensure that as many references are unique as possible, which enables Lean to use destructive mutation behind the scenes while maintaining a pure functional interface.
The map and set library provides operators that can be used to maintain uniqueness of references.
In particular, when possible, operations such as {name Std.HashMap.alter}`alter` or {name Std.HashMap.modify}`modify` should be preferred over explicitly retrieving a value, modifying it, and reinserting it.
These operations avoid creating a second reference to the value during modification.

:::example "Modifying Values in Maps"

```imports -show
import Std
```

```lean
open Std
```

The function {name}`addAlias` is used to track aliases of a string in some data set.
One way to add an alias is to first look up the existing aliases, defaulting to the empty array, then insert the new alias, and finally save the resulting array in the map:

```lean
def addAlias (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  let prior := aliases.getD key #[]
  aliases.insert key (prior.push value)
```

This implementation has poor performance characteristics.
Because the map retains a reference to the prior values, the array must be copied rather than mutated.
A better implementation explicitly erases the prior value from the map before modifying it:

```lean
def addAlias' (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  let prior := aliases.getD key #[]
  let aliases := aliases.erase key
  aliases.insert key (prior.push value)
```

Using {name}`HashMap.alter` is even better.
It removes the need to explicitly delete and re-insert the value:

```lean
def addAlias'' (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  aliases.alter key fun prior? =>
    some ((prior?.getD #[]).push value)
```

:::



# Hash Maps
%%%
tag := "HashMap"
%%%

The declarations in this section should be imported using `import Std.HashMap`.

{docstring Std.HashMap +hideFields +hideStructureConstructor}


## Creation

{docstring Std.HashMap.emptyWithCapacity}

## Properties

{docstring Std.HashMap.size}

{docstring Std.HashMap.isEmpty}

{docstring Std.HashMap.Equiv}

:::syntax term (title := "Equivalence") (namespace := Std.HashMap)

The relation {name Std.HashMap.Equiv}`HashMap.Equiv` can also be written with an infix operator, which is scoped to its namespace:

```grammar
$_ ~m $_
```

:::

## Queries

{docstring Std.HashMap.contains}

{docstring Std.HashMap.get}

{docstring Std.HashMap.get!}

{docstring Std.HashMap.get?}

{docstring Std.HashMap.getD}

{docstring Std.HashMap.getKey}

{docstring Std.HashMap.getKey!}

{docstring Std.HashMap.getKey?}

{docstring Std.HashMap.getKeyD}

{docstring Std.HashMap.keys}

{docstring Std.HashMap.keysArray}

{docstring Std.HashMap.values}

{docstring Std.HashMap.valuesArray}

## Modification

{docstring Std.HashMap.alter}

{docstring Std.HashMap.modify}

{docstring Std.HashMap.containsThenInsert}

{docstring Std.HashMap.containsThenInsertIfNew}

{docstring Std.HashMap.erase}

{docstring Std.HashMap.filter}

{docstring Std.HashMap.filterMap}

{docstring Std.HashMap.insert}

{docstring Std.HashMap.insertIfNew}

{docstring Std.HashMap.getThenInsertIfNew?}

{docstring Std.HashMap.insertMany}

{docstring Std.HashMap.insertManyIfNewUnit}

{docstring Std.HashMap.partition}

{docstring Std.HashMap.union}

## Iteration

{docstring Std.HashMap.iter}

{docstring Std.HashMap.keysIter}

{docstring Std.HashMap.valuesIter}

{docstring Std.HashMap.map}

{docstring Std.HashMap.fold}

{docstring Std.HashMap.foldM}

{docstring Std.HashMap.forIn}

{docstring Std.HashMap.forM}

## Conversion

{docstring Std.HashMap.ofList}

{docstring Std.HashMap.toArray}

{docstring Std.HashMap.toList}

{docstring Std.HashMap.unitOfArray}

{docstring Std.HashMap.unitOfList}

## Unbundled Variants

Unbundled maps separate well-formedness proofs from data.
This is primarily useful when defining {ref "raw-data"}[nested inductive types].
To use these variants, import the modules `Std.HashMap.Raw` and `Std.HashMap.RawLemmas`.

{docstring Std.HashMap.Raw}

{docstring Std.HashMap.Raw.WF}

# Dependent Hash Maps
%%%
tag := "DHashMap"
%%%

The declarations in this section should be imported using `import Std.DHashMap`.

{docstring Std.DHashMap +hideFields +hideStructureConstructor}

## Creation

{docstring Std.DHashMap.emptyWithCapacity}

## Properties

{docstring Std.DHashMap.size}

{docstring Std.DHashMap.isEmpty}

{docstring Std.DHashMap.Equiv}

:::syntax term (title := "Equivalence") (namespace := Std.DHashMap)

The relation {name Std.DHashMap.Equiv}`DHashMap.Equiv` can also be written with an infix operator, which is scoped to its namespace:

```grammar
$_ ~m $_
```

:::

## Queries

{docstring Std.DHashMap.contains}

{docstring Std.DHashMap.get}

{docstring Std.DHashMap.get!}

{docstring Std.DHashMap.get?}

{docstring Std.DHashMap.getD}

{docstring Std.DHashMap.getKey}

{docstring Std.DHashMap.getKey!}

{docstring Std.DHashMap.getKey?}

{docstring Std.DHashMap.getKeyD}

{docstring Std.DHashMap.keys}

{docstring Std.DHashMap.keysArray}

{docstring Std.DHashMap.values}


{docstring Std.DHashMap.valuesArray}

## Modification

{docstring Std.DHashMap.alter}

{docstring Std.DHashMap.modify}

{docstring Std.DHashMap.containsThenInsert}

{docstring Std.DHashMap.containsThenInsertIfNew}

{docstring Std.DHashMap.erase}

{docstring Std.DHashMap.filter}

{docstring Std.DHashMap.filterMap}

{docstring Std.DHashMap.insert}

{docstring Std.DHashMap.insertIfNew}

{docstring Std.DHashMap.getThenInsertIfNew?}

{docstring Std.DHashMap.insertMany}

{docstring Std.DHashMap.partition}

{docstring Std.DHashMap.union}

## Iteration

{docstring Std.DHashMap.iter}

{docstring Std.DHashMap.keysIter}

{docstring Std.DHashMap.valuesIter}

{docstring Std.DHashMap.map}

{docstring Std.DHashMap.fold}

{docstring Std.DHashMap.foldM}

{docstring Std.DHashMap.forIn}

{docstring Std.DHashMap.forM}

## Conversion

{docstring Std.DHashMap.ofList}

{docstring Std.DHashMap.toArray}

{docstring Std.DHashMap.toList}

## Unbundled Variants

Unbundled maps separate well-formedness proofs from data.
This is primarily useful when defining {ref "raw-data"}[nested inductive types].
To use these variants, import the modules `Std.DHashMap.Raw` and `Std.DHashMap.RawLemmas`.

{docstring Std.DHashMap.Raw}

{docstring Std.DHashMap.Raw.WF}

# Extensional Hash Maps
%%%
tag := "ExtHashMap"
%%%

The declarations in this section should be imported using `import Std.ExtHashMap`.

{docstring Std.ExtHashMap +hideFields +hideStructureConstructor}

## Creation

{docstring Std.ExtHashMap.emptyWithCapacity}

## Properties

{docstring Std.ExtHashMap.size}

{docstring Std.ExtHashMap.isEmpty}

## Queries

{docstring Std.ExtHashMap.contains}

{docstring Std.ExtHashMap.get}

{docstring Std.ExtHashMap.get!}

{docstring Std.ExtHashMap.get?}

{docstring Std.ExtHashMap.getD}

{docstring Std.ExtHashMap.getKey}

{docstring Std.ExtHashMap.getKey!}

{docstring Std.ExtHashMap.getKey?}

{docstring Std.ExtHashMap.getKeyD}

## Modification

{docstring Std.ExtHashMap.alter}

{docstring Std.ExtHashMap.modify}

{docstring Std.ExtHashMap.containsThenInsert}

{docstring Std.ExtHashMap.containsThenInsertIfNew}

{docstring Std.ExtHashMap.erase}

{docstring Std.ExtHashMap.filter}

{docstring Std.ExtHashMap.filterMap}

{docstring Std.ExtHashMap.insert}

{docstring Std.ExtHashMap.insertIfNew}

{docstring Std.ExtHashMap.getThenInsertIfNew?}

{docstring Std.ExtHashMap.insertMany}

{docstring Std.ExtHashMap.insertManyIfNewUnit}

## Iteration

{docstring Std.ExtHashMap.map}

## Conversion

{docstring Std.ExtHashMap.ofList}

{docstring Std.ExtHashMap.unitOfArray}

{docstring Std.ExtHashMap.unitOfList}

# Extensional Dependent Hash Maps
%%%
tag := "ExtDHashMap"
%%%

The declarations in this section should be imported using `import Std.ExtDHashMap`.

{docstring Std.ExtDHashMap +hideFields +hideStructureConstructor}

## Creation

{docstring Std.ExtDHashMap.emptyWithCapacity}

## Properties

{docstring Std.ExtDHashMap.size}

{docstring Std.ExtDHashMap.isEmpty}


## Queries

{docstring Std.ExtDHashMap.contains}

{docstring Std.ExtDHashMap.get}

{docstring Std.ExtDHashMap.get!}

{docstring Std.ExtDHashMap.get?}

{docstring Std.ExtDHashMap.getD}

{docstring Std.ExtDHashMap.getKey}

{docstring Std.ExtDHashMap.getKey!}

{docstring Std.ExtDHashMap.getKey?}

{docstring Std.ExtDHashMap.getKeyD}

## Modification

{docstring Std.ExtDHashMap.alter}

{docstring Std.ExtDHashMap.modify}

{docstring Std.ExtDHashMap.containsThenInsert}

{docstring Std.ExtDHashMap.containsThenInsertIfNew}

{docstring Std.ExtDHashMap.erase}

{docstring Std.ExtDHashMap.filter}

{docstring Std.ExtDHashMap.filterMap}

{docstring Std.ExtDHashMap.insert}

{docstring Std.ExtDHashMap.insertIfNew}

{docstring Std.ExtDHashMap.getThenInsertIfNew?}

{docstring Std.ExtDHashMap.insertMany}


## Iteration

{docstring Std.ExtDHashMap.map}

## Conversion

{docstring Std.ExtDHashMap.ofList}


# Hash Sets
%%%
tag := "HashSet"
%%%

{docstring Std.HashSet}

## Creation

{docstring Std.HashSet.emptyWithCapacity}

## Properties

{docstring Std.HashSet.isEmpty}

{docstring Std.HashSet.size}

{docstring Std.HashSet.Equiv}

:::syntax term (title := "Equivalence") (namespace := Std.HashMap)

The relation {name Std.HashSet.Equiv}`HashSet.Equiv` can also be written with an infix operator, which is scoped to its namespace:

```grammar
$_ ~m $_
```

:::


## Queries


{docstring Std.HashSet.contains}

{docstring Std.HashSet.get}

{docstring Std.HashSet.get!}

{docstring Std.HashSet.get?}

{docstring Std.HashSet.getD}


## Modification

{docstring Std.HashSet.insert}

{docstring Std.HashSet.insertMany}

{docstring Std.HashSet.erase}

{docstring Std.HashSet.filter}

{docstring Std.HashSet.containsThenInsert}

{docstring Std.HashSet.partition}

{docstring Std.HashSet.union}

## Iteration

{docstring Std.HashSet.iter}

{docstring Std.HashSet.all}

{docstring Std.HashSet.any}

{docstring Std.HashSet.fold}

{docstring Std.HashSet.foldM}

{docstring Std.HashSet.forIn}

{docstring Std.HashSet.forM}

## Conversion

{docstring Std.HashSet.ofList}

{docstring Std.HashSet.toList}

{docstring Std.HashSet.ofArray}

{docstring Std.HashSet.toArray}

## Unbundled Variants

Unbundled maps separate well-formedness proofs from data.
This is primarily useful when defining {ref "raw-data"}[nested inductive types].
To use these variants, import the modules `Std.HashSet.Raw` and `Std.HashSet.RawLemmas`.

{docstring Std.HashSet.Raw}

{docstring Std.HashSet.Raw.WF}


# Extensional Hash Sets
%%%
tag := "ExtHashSet"
%%%

{docstring Std.ExtHashSet}

## Creation

{docstring Std.ExtHashSet.emptyWithCapacity}

## Properties

{docstring Std.ExtHashSet.isEmpty}

{docstring Std.ExtHashSet.size}


## Queries

{docstring Std.ExtHashSet.contains}

{docstring Std.ExtHashSet.get}

{docstring Std.ExtHashSet.get!}

{docstring Std.ExtHashSet.get?}

{docstring Std.ExtHashSet.getD}


## Modification

{docstring Std.ExtHashSet.insert}

{docstring Std.ExtHashSet.insertMany}

{docstring Std.ExtHashSet.erase}

{docstring Std.ExtHashSet.filter}

{docstring Std.ExtHashSet.containsThenInsert}

## Conversion

{docstring Std.ExtHashSet.ofList}

{docstring Std.ExtHashSet.ofArray}

{include 1 Manual.BasicTypes.Maps.TreeMap}


# Dependent Tree-Based Maps
%%%
tag := "DTreeMap"
%%%

The declarations in this section should be imported using `import Std.DTreeMap`.

{docstring Std.DTreeMap +hideFields +hideStructureConstructor}

## Creation

{docstring Std.DTreeMap.empty}

## Properties

{docstring Std.DTreeMap.size}

{docstring Std.DTreeMap.isEmpty}

## Queries

{docstring Std.DTreeMap.contains}

{docstring Std.DTreeMap.get}

{docstring Std.DTreeMap.get!}

{docstring Std.DTreeMap.get?}

{docstring Std.DTreeMap.getD}

{docstring Std.DTreeMap.getKey}

{docstring Std.DTreeMap.getKey!}

{docstring Std.DTreeMap.getKey?}

{docstring Std.DTreeMap.getKeyD}

{docstring Std.DTreeMap.keys}

{docstring Std.DTreeMap.keysArray}

{docstring Std.DTreeMap.values}

{docstring Std.DTreeMap.valuesArray}

## Modification

{docstring Std.DTreeMap.alter}

{docstring Std.DTreeMap.modify}

{docstring Std.DTreeMap.containsThenInsert}

{docstring Std.DTreeMap.containsThenInsertIfNew}

{docstring Std.DTreeMap.erase}

{docstring Std.DTreeMap.filter}

{docstring Std.DTreeMap.filterMap}

{docstring Std.DTreeMap.insert}

{docstring Std.DTreeMap.insertIfNew}

{docstring Std.DTreeMap.getThenInsertIfNew?}

{docstring Std.DTreeMap.insertMany}

{docstring Std.DTreeMap.partition}

## Iteration

{docstring Std.DTreeMap.iter}

{docstring Std.DTreeMap.keysIter}

{docstring Std.DTreeMap.valuesIter}

{docstring Std.DTreeMap.map}

{docstring Std.DTreeMap.foldl}

{docstring Std.DTreeMap.foldlM}

{docstring Std.DTreeMap.forIn}

{docstring Std.DTreeMap.forM}

## Conversion

{docstring Std.DTreeMap.ofList}

{docstring Std.DTreeMap.toArray}

{docstring Std.DTreeMap.toList}

## Unbundled Variants

Unbundled maps separate well-formedness proofs from data.
This is primarily useful when defining {ref "raw-data"}[nested inductive types].
To use these variants, import the module `Std.DTreeMap.Raw`.

{docstring Std.DTreeMap.Raw}

{docstring Std.DTreeMap.Raw.WF}

{include 1 Manual.BasicTypes.Maps.TreeSet}
