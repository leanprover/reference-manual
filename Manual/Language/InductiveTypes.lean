import VersoManual

import Manual.Meta

open Verso.Genre Manual

#doc (Manual) "Inductive Types" =>

{deftech}_Inductive types_ are the primary means of introducing new types to Lean.
While {tech}[universes] and {tech}[functions] are built-in primitives that could not be added by users, every other {tech}[canonical] type former in Lean is an inductive type.
Inductive types are specified by their {deftech}_type constructors_ {index}[type constructor] and their {deftech}_constructors_; {index}[constructor] their other properties are derived from these.
Each inductive type has a single type constructor, which may take both {tech}[universe parameters] and ordinary parameters.
Inductive types may have any number of constructors; these constructors introduce new values whose types are headed by the inductive type's type constructor.

Based on the type constructor and the constructors for an inductive type, Lean derives an {deftech}_eliminator_ {index}[eliminator].
Logically, eliminators represent induction principles or elimination rules; computationally, they represent primitive recursive computations.
The termination of recursive functions is justified by translating them into uses of the eliminators, so Lean's kernel only needs to perform type checking of eliminator applications, rather than including a separate termination analysis.
Lean additionally produces a number of helper constructions based on the eliminator, which are used elsewhere in the system.

_Structures_ are a special case of inductive types that have exactly one constructor.
When a structure is declared, Lean additionally generates helpers that enable additional language features to be used with the new structure.

This section describes the specific details of the syntax used to specify both inductive types and structures, the new constants and definitions in the environment that result from inductive type declarations, and the run-time representation of inductive types' values in compiled code.

# Inductive Type Declarations

:::syntax command
```grammar
$_:declModifiers
inductive $d:declId $_ where
  $[| $_ $c:ident $_]*
$[with $_:computedField*]?
$[deriving $[$_ $[with $_]?],*]?
```

Declares a new inductive type.
:::



:::TODO
 * Constructors are namespaced
 * Computed fields
 * Deriving (just xref)
 * Interaction with `variable`
 * Parameters vs indices
   * Universes
 * Positivity
 * Mutual Inductive Types
:::

# Structure Declarations

::: TODO
Topics:
 * Projections
 * Inheritance
 * Structure update
 * `where`-syntax
:::

# Logical Model

::: TODO
 * The new constants are just new, not encoded
 * Recursors
 * SizeOf
 * Additional constructions (below, etc)
 * All this for mutual inductives as well
:::

# Run-Time Representation

::: TODO
Basically as in current docs, but add details about compilation of recursive functions (not through eliminators)
:::
