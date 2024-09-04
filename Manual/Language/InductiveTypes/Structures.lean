import VersoManual

import Manual.Meta

open Verso.Genre Manual

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

#doc (Manual) "Structure Declarations" =>

:::syntax command
```grammar
$_:declModifiers
structure $d:declId $_:bracketedBinder*
    $[extends $_,*]? $[: $_]? where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$_ $[with $_]?],*]?
```

Declares a new structure type.
:::

{deftech}[Structures] are non-recursive inductive types that have only a single constructor and no indices.
In exchange for these restrictions, Lean generates code for structures that offers a number of conveniences: accessor functions are generated for each field, an additional constructor syntax based on field names rather than positional arguments is available, a similar syntax may be used to replace the values of certain named fields, and structures may extend other structures.
Structures do not add any expressive power to Lean; all of their features are implemented in terms of code generation.

```lean (show := false)
-- Test claim about non-recursive above
/-- error: unknown identifier 'RecStruct' -/
#guard_msgs in
structure RecStruct where
  next : Option RecStruct
```

# Structure Parameters

Just like ordinary inductive type declarations, the header of the structure declaration contains a signature that may specify both parameters and a resulting universe.
Structures may not define {tech}[indexed families].

# Fields

Each field of a structure declaration corresponds to a parameter of the constructor.
Auto-implicit arguments are inserted in each field separately, even if their names coincide, and the fields become constructor parameters that quantify over types.

:::: example "Auto-implicit parameters in structure fields"

The structure {lean}`MyStructure` contains a field whose type is an auto-implicit parameter:

```lean
structure MyStructure where
  field1 : α
  field2 : α
```
The type constructor {name}`MyStructure` takes two universe parameters:
```signature
MyStructure.{u, v} : Type (max u v)
```
The resulting type is in `Type` rather than `Sort` because the constructor fields quantify over types in `Sort`. In particular, both fields in its constructor {name}`MyStructure.mk` take an implicit type parameter:
```signature
MyStructure.mk.{u, v}
  (field1 : {α : Sort u} → α)
  (field2 : {α : Sort v} → α)
  : MyStructure.{u,v}
```

::::


For each field, a {deftech}[projection function] is generated that extracts the field's value from the underlying datatype's constructor.
This function is in the structure's name's namespace.
Structure field projections are handled specially by the elaborator (as described in the {ref "structure-inheritance"}[section on structure inheritance]), which performs extra steps beyond looking up a namespace.
When field types depend on prior fields, the types of the dependent projection functions are written in terms of earlier projections, rather than explicit pattern matching.


:::: example "Dependent projection types"

The structure {lean}`ArraySized` contains a field whose type depends on both a structure parameter and an earlier field:
```lean
structure ArraySized (α : Type u) (length : Nat)  where
  array : Array α
  size_eq_length : array.size = length
```

The signature of the projection function {name ArraySized.size_eq_length}`size_eq_length` takes the structure type's parameter as an implicit parameter and refers to the earlier field using the corresponding projection:
```signature
ArraySized.size_eq_length.{u}
  {α : Type u} {length : Nat}
  (self : ArraySized α length)
  : self.array.size = length
```

::::

Structure fields may have default values, specified with `:=`.
These values are used if no explicit value is provided.


::: example "Default values"

An adjacency list representation of a graph can be represented as an array of lists of {lean}`Nat`.
The size of the array indicates the number of vertices, and the outgoing edges from each vertex are stored in the array at the vertex's index.
Because the default value {lean}`#[]` is provided for the field {name Graph.adjacency}`adjacency`, the empty graph {lean}`Graph.empty` can be constructed without providing any field values.
```lean
structure Graph where
  adjacency : Array (List Nat) := #[]

def Graph.empty : Graph := {}
```
:::


Structure fields may additionally be accessed via their index, using dot notation.
Fields are numbered beginning with `1`.


# Structure Constructors

Structure constructors may be explicitly named by providing the constructor name and `::` prior to the fields.
If no name is explicitly provided, then the constructor is named `mk` in the structure type's namespace.
{ref "declaration-modifiers"}[Declaration modifiers] may additionally be provided along with an explicit constructor name.

::: example "Non-default constructor name"
The structure  {lean}`Palindrome` contains a string and a proof that the string is the same when reversed:

```lean
structure Palindrome where
  ofString ::
  text : String
  is_palindrome : text.data.reverse = text.data
```

Its constructor is named {name}`Palindrome.ofString`, rather than `Palindrome.mk`.

:::

::: example "Modifiers on structure constructor"
The structure {lean}`NatStringBimap` maintains a finite bijection between natural numbers and strings.
It consists of a pair of maps, such that the keys each occur as values exactly once in the other map.
Because the constructor is private, code outside the defining module can't construct new instances and must use the provided API, which maintains the invariants of the datatype.
Additionally, providing the default constructor name explicitly is an opportunity to attach a {tech}[documentation comment] to the constructor.

```lean
structure NatStringBimap where
  /--
  Build a finite bijection between some
  natural numbers and strings
  -/
  private mk ::
  natToString : Std.HashMap Nat String
  stringToNat : Std.HashMap String Nat

def NatStringBimap.empty : NatStringBimap := ⟨{}, {}⟩

def NatStringBimap.insert
    (nat : Nat) (string : String)
    (map : NatStringBimap) :
    Option NatStringBimap :=
  if map.natToString.contains nat ||
      map.stringToNat.contains string then
    none
  else
    some (NatStringBimap.mk (map.natToString.insert nat string) (map.stringToNat.insert string nat))
```
:::

Because structures are represented by single-constructor inductive types, their constructors can be invoked or matched against using {tech}[anonymous constructor syntax].
Additionally, structures may be constructed or matched against using the names of the fields together with values for them.

:::syntax term

```grammar
{ $_,*
  $[: $ty:term]? }
```

Constructs a value of a constructor type given values for named fields.
Field specifiers may take two forms:
```grammar (of := Lean.Parser.Term.structInstField)
$x := $y
```

```grammar (of := Lean.Parser.Term.structInstFieldAbbrev)
$f:ident
```

A {syntaxKind}`structInstLVal` is a field name (an identifier), a field index (a natural number), or a term in square brackets, followed by a sequence of zero or more subfields.
Subfields are either a field name or index preceded by a dot, or a term in square brackets.

This syntax is elaborated to applications of structure constructors.
The values provided for fields are by name, and they may be provided in any order.
The values provided for subfields are used to initialize fields of constructors of structures that are themselves found in fields.
Terms in square brackets are not allowed when constructing a structure; they are used in structure updates.

Field specifiers that do not contain `:=` are field abbreviations.
In this context, the identifier `f` is an abbreviation for `f := f`; that is, the value of `f` in the current scope is used to initialize the field `f`.

Every field that does not have a default value must be provided.
If a tactic is specified as the default argument, then it is run at elaboration time to construct the argument's value.

In a pattern context, field names are mapped to patterns that match the corresponding projection, and field abbreviations bind a pattern variable that is the field's name.
Default arguments are still present in patterns; if a pattern does not specify a value for a field with a default value, then the pattern only matches the default.

The optional type annotation allows the structure type to be specified in contexts where it is not otherwise determined.
:::

:::example "Patterns and default values"
The structure {name}`AugmentedIntList` contains a list together with some extra information, which is empty if omitted:
```lean
structure AugmentedIntList where
  list : List Int
  augmentation : String := ""
```

When testing whether the list is empty, the function {name AugmentedIntList.isEmpty}`isEmpty` is also testing whether the {name AugmentedIntList.augmentation}`augmentation` field is empty, because the omitted field's default value is also used in pattern contexts:
```lean (name := isEmptyDefaults)
def AugmentedIntList.isEmpty : AugmentedIntList → Bool
  | {list := []} => true
  | _ => false

#eval {list := [], augmentation := "extra" : AugmentedIntList}.isEmpty
```
```leanOutput isEmptyDefaults
false
```
:::


:::syntax term
```grammar
{$e:term with
  $_,*
  $[: $ty:term]?}
```
Updates a value of a constructor type.
The term that precedes the {keywordOf Lean.Parser.Term.structInst}`with` clause is expected to have a structure type; it is the value that is being updated.
A new instance of the structure is created in which every field not specified is copied from the value that is being updated, and the specified fields are replaced with their new values.
When updating a structure, array values may also be replaced by including the index to be updated in square brackets.
This updating does not require that the index expression be in bounds for the array, and out-of-bounds updates are discarded.
:::

::::example "Updating arrays"
:::keepEnv
Updating structures may use array indices as well as projection names.
Updates at indices that are out of bounds are ignored:

```lean name:=arrayUpdate
structure AugmentedIntArray where
  array : Array Int
  augmentation : String := ""
deriving Repr

def one : AugmentedIntArray := {array := #[1]}
def two : AugmentedIntArray := {one with array := #[1, 2]}
def two' : AugmentedIntArray := {two with array[0] := 2}
def two'' : AugmentedIntArray := {two with array[99] := 3}
#eval (one, two, two', two'')
```
```leanOutput arrayUpdate
({ array := #[1], augmentation := "" },
 { array := #[1, 2], augmentation := "" },
 { array := #[2, 2], augmentation := "" },
 { array := #[1, 2], augmentation := "" })
```
:::
::::

Values of structure types may also be declared using {keywordOf Lean.Parser.Command.declaration (parser:=declValEqns)}`where`, followed by definitions for each field.
This may only be used as part of a definition, not in an expression context.

::::example "`where` for structures"
:::keepEnv
The product type in Lean is a structure named {name}`Prod`.
Products can be defined using their projections:
```lean
def location : Float × Float where
  fst := 22.807
  snd := -13.923
```
:::
::::

# Structure Inheritance
%%%
tag := "structure-inheritance"
%%%

Structures may be declared as extending other structures using the optional {keywordOf Lean.Parser.Command.declaration (parser:=«structure»)}`extends` clause.
The resulting structure type has all of the fields of all of the parent structure types.
If the parent structure types have overlapping field names, then all overlapping field names must have the same type.
If the overlapping fields have different default values, then the default value from the last parent structure that includes the field is used.
New default values in the child structure take precedence over default values from the parent structures.

```lean (show := false) (keep := false)
-- If the overlapping fields have different default values, then the default value from the last parent structure that includes the field is used.
structure Q where
  x : Nat := 0
deriving Repr
structure Q' where
  x : Nat := 3
deriving Repr
structure Q'' extends Q, Q'
deriving Repr
structure Q''' extends Q', Q
deriving Repr

/-- info: 3 -/
#guard_msgs in
#eval ({} : Q'').x
/-- info: 0 -/
#guard_msgs in
#eval ({} : Q''').x
```

When the new structure extends existing structures, the new structure's constructor takes the existing structure's information as additional arguments.
Typically, this is in the form of a constructor parameter for each parent structure type.
If the parents' fields overlap, however, then the subset of non-overlapping fields from one or more of the parents is included instead to prevent duplicating field information.


There is no subtyping relation between a parent structure type and its children.
Even if structure `B` extends structure `A`, a function expecting an `A` will not accept a `B`.
However, conversion functions are generated that convert a structure into each of its parents.
These conversion functions are in the child structure's namespace, and their name is the parent structure's name preceded by `to`.

::: example "Structure type inheritance with overlapping fields"
In this example, a {lean}`Textbook` is a {lean}`Book` that is also an {lean}`AcademicWork`:

```lean
structure Book where
  title : String
  author : String

structure AcademicWork where
  author : String
  discipline : String

structure Textbook extends Book, AcademicWork

#check Textbook.toBook
```

Because the field `author` occurs in both {lean}`Book` and {lean}`AcademicWork`, the constructor {name}`Textbook.mk` does not take both parents as arguments.
Its signature is:
```signature
Textbook.mk (toBook : Book) (discipline : String) : Textbook
```

The conversion functions are:
```signature
Textbook.toBook (self : Textbook) : Book
```
```signature
Textbook.toAcademicWork (self : Textbook) : AcademicWork
```

The latter combines the `author` field of the included {lean}`Book` with the unbundled `Discipline` field, and is equivalent to:
```lean
def toAcademicWork (self : Textbook) : AcademicWork :=
  let .mk book discipline := self
  let .mk _title author := book
  .mk author discipline
```
```lean (show := false)
-- check claim of equivalence
example : toAcademicWork = Textbook.toAcademicWork := by
  funext b
  cases b
  dsimp [toAcademicWork]
```

:::

The resulting structure's projections can be used as if its fields are simply the union of the parents' fields.
The Lean elaborator automatically generates an appropriate accessor when it encounters a projection.
Likewise, the field-based initialization and structure update notations hide the details of the encoding of inheritance.
The encoding is, however, visible when using the constructor's name, when using {tech}[anonymous constructor syntax], or when referring to fields by their index rather than their name.

:::: example "Field indices and structure inheritance"

```lean
structure Pair (α : Type u) where
  fst : α
  snd : α
deriving Repr

structure Triple (α : Type u) extends Pair α where
  thd : α
deriving Repr

def coords : Triple Nat := {fst := 17, snd := 2, thd := 95}
```

Evaluating the first field index of {name}`coords` yields the underlying {name}`Pair`, rather than the contents of the field `fst`:
```lean name:=coords1
#eval coords.1
```
```leanOutput coords1
{ fst := 17, snd := 2 }
```

The elaborator translates {lean}`coords.fst` into {lean}`coords.toPair.fst`.

````lean (show := false) (keep := false)
example (t : Triple α) : t.fst = t.toPair.fst := rfl
````
::::

:::: example "No structure subtyping"
:::keepEnv
Given these definitions of even numbers, even prime numbers, and a concrete even prime:
```lean
structure EvenNumber where
  val : Nat
  isEven : 2 ∣ val := by decide

structure EvenPrime extends EvenNumber where
  notOne : val ≠ 1 := by decide
  isPrime : ∀ n, n ≤ val → n ∣ val  → n = 1 ∨ n = val

def two : EvenPrime where
  val := 2
  isPrime := by
    intros
    dsimp only at *
    repeat' (cases ‹Nat.le _ _›)
    all_goals omega

def printEven (num : EvenNumber) : IO Unit :=
  IO.print num.val
```
it is a type error to apply {name}`printEven` directly to {name}`two`:
```lean (error := true) (name := printTwo)
#check printEven two
```
```leanOutput printTwo
application type mismatch
  printEven two
argument
  two
has type
  EvenPrime : Type
but is expected to have type
  EvenNumber : Type
```
because values of type {name}`EvenPrime` are not also values of type {name}`EvenNumber`.
:::
::::


```lean (show := false) (keep := false)
structure A where
  x : Nat
  y : Int
structure A' where
  x : Int
structure B where
  foo : Nat
structure C extends A where
  z : String
/-- info: C.mk (toA : A) (z : String) : C -/
#guard_msgs in
#check C.mk

def someC : C where
  x := 1
  y := 2
  z := ""

/--
error: type mismatch
  someC
has type
  C : Type
but is expected to have type
  A : Type
-/
#guard_msgs in
#check (someC : A)

structure D extends A, B where
  z : String
/-- info: D.mk (toA : A) (toB : B) (z : String) : D -/
#guard_msgs in
#check D.mk
structure E extends A, B where
  x := 44
  z : String
/-- info: E.mk (toA : A) (toB : B) (z : String) : E -/
#guard_msgs in
#check E.mk
/--
error: parent field type mismatch, field 'x' from parent 'A'' has type
  Int : Type
but is expected to have type
  Nat : Type
-/
#guard_msgs in
structure F extends A, A' where



```
