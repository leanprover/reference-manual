import Lean

open Lean Meta Elab Command Term in
/--
Registers an error explanation.

Note that the provided name is not relativized to the current namespace.
-/
elab docStx:docComment cmd:"reregister_error_explanation " nm:ident t:term : command => withRef cmd do
  let tp := Lean.mkConst ``ErrorExplanation.Metadata []
  let metadata ← runTermElabM <| fun _ => unsafe do
    let e ← elabTerm t tp
    if e.hasSyntheticSorry then throwAbortTerm
    evalExpr ErrorExplanation.Metadata tp e
  let name := nm.getId
  if name.isAnonymous then throwErrorAt nm "Invalid name for error explanation: '{nm}'"
  validateDocComment docStx
  let doc ← getDocStringText docStx
  unless errorExplanationExt.getState (← getEnv) |>.contains name do
    throwError m!"Cannot update explanation: No error explanation exists for '{name}'"
  modifyEnv (errorExplanationExt.addEntry · (name, { metadata, doc, declLoc? := none }))

/--
This error occurs when a parameter of an inductive type is not uniform in an inductive declaration. The parameters of an inductive type (i.e., those that appear before the colon following the `inductive` keyword) must be identical in all occurrences of the type being defined in its constructors' types. If a parameter of an inductive type must vary between constructors, make the parameter an index by moving it to the right of the colon. See the manual section on [Inductive Types](lean-manual://section/inductive-types) for additional details.

This error also occurs if the type constructor being defined is only partially applied to its parameters: for instance, if the type constructor itself is being passed as the argument to a function. In such a construction, all arguments omitted from the partial application must be indices, not parameters.

Note that auto-implicit inlay hints always appear left of the colon in an inductive declaration (i.e., as parameters), even when they are actually indices. This means that double-clicking on an inlay hint to insert such parameters may result in this error. If it does, change the inserted parameters to indices.

Here's a block of code in the description:

```lean
def foo := 42
```
Notice that `foo` has type `Nat`.

# Examples

## Vector length index as a parameter

```lean broken
inductive Vec (α : Type) (n : Nat) : Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```
```output broken
Mismatched inductive type parameter in
  Vec α 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter 'n' must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
```lean fixed
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```

The length argument `n` of type `Nat` of the `Vec` type constructor is declared as a parameter, but other values for this argument appear in the `nil` and `cons` constructors (namely, `0` and `n + 1`). An error therefore appears at the first occurrence of such an argument. To correct this, `n` cannot be a parameter of the inductive declaration and must instead be an index, as in the corrected example. On the other hand, `α` remains unchanged throughout all occurrences of `Vec` in the declaration and so is a valid parameter.
We can write `def x := Nat` to define `x` to be equal to `Nat`, or `let x := Nat; x`.
-/
reregister_error_explanation Lean.InductiveParamMismatch {
  summary := "Invalid parameter in an occurrence of an inductive type in one of its constructors."
  sinceVersion := "4.0.0"
}

/--
This error occurs when the type of a binder in a declaration or local binding is not fully
specified and cannot be inferred by Lean. Generally, this can be resolved by providing more
information to help Lean determine the type of the binder, either by explicitly annotating its type
or by providing additional type information at sites where it is used.

Note that if an explicit resulting type is specified—even if it contains holes—Lean will not use
information from the definition body to infer parameter types. Thus, it may be necessary to
explicitly annotate the types of variables whose types are otherwise inferable—and whose inferred
types may even be correctly displayed in the Infoview—without the resulting-type annotation. In
`theorem` declarations, the definition body is never used to infer the types of binders, so any
binders whose types cannot be inferred from the resulting type of the theorem must include a type
annotation.

This error may also arise when identifiers that were intended to be definition names are
inadvertently written in binder position instead. In these cases, the excess identifiers are instead
elaborated as binders with unspecified type. This frequently occurs when attempting to define
multiple constants of the same type at the same time using a syntactic construction that does not
support this. Situations where this may happen include:
* Attempting to name an example by writing an identifier after the `example` keyword;
* Attempting to define multiple constants with the same type and (if applicable) value by listing
  them sequentially after `def`, `opaque`, or another declaration keyword;
* Attempting to define multiple fields of a structure of the same type by sequentially listing their
  names on the same line of a structure declaration; and
* Omitting vertical bars between inductive constructor names.

The first three cases are demonstrated in examples below.

# Examples

## Binder type requires new type variable

```lean broken
def identity x :=
  x
```
```output
failed to infer binder type
```
```lean fixed
def identity (x : α) :=
  x
```

Unlike some other programming languages, Lean will not automatically generate fresh type variables
to replace metavariables arising during type inference. Instead, the type `α` of `x` must be
specified. Note that if automatic implicit parameter insertion is enabled (as it is by default), the
binder for `α` itself need not be provided; Lean will insert an implicit binder for this parameter
automatically.

## Uninferred binder type due to resulting type annotation

```lean broken
def plusTwo x : Nat :=
  x + 2
```
```output
failed to infer binder type

Note: When the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
```
```lean fixed
def plusTwo (x : Nat) : Nat :=
  x + 2
```

Even though `x` is inferred to have type `Nat` in the body of `plusTwo`, this information is not
available when elaborating the type of the definition because the resulting type `Nat` has been
explicitly specified. Using only the information in the header, the type of `x` cannot be
determined, resulting in the shown error.


## Attempting to name an example declaration
```lean broken
example trivial_proof : True :=
  trivial
```
```output
failed to infer binder type

Note: When the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
```
```lean fixed
example : True :=
  trivial
```
Examples cannot be named, and an identifier written where a name would appear in other declaration
forms is instead elaborated as a binder, whose type cannot be inferred. If a declaration must be
named, it should be defined using a declaration form that support naming, such as  `def` or
`theorem`.

## Attempting to define multiple constants in one declaration

```lean broken
opaque m n : Nat
```
```output
failed to infer binder type

Note: Recall that you cannot declare multiple constants in a single declaration. The identifier(s) `n` are being interpreted as parameters `(n : _)`.
```
```lean fixed
opaque m : Nat
opaque n : Nat
```

A constant declaration defines only one constant: it is not possible to list identifiers after
`opaque` or `def` to define them all to have the same type (and, in the latter case, value). Such a
declaration is instead elaborated as defining a single constant with parameters given by the
subsequent identifiers, whose types are unspecified and cannot be inferred. The only way to define
multiple global constants using these constructs is to declare each separately.

## Attempting to define multiple structure fields on the same line

```lean broken
structure Person where
  givenName familyName : String
  age : Nat
```
```output
failed to infer binder type
```
```lean fixed (title := "Fixed (separate lines)")
structure Person where
  givenName : String
  familyName : String
  age : Nat
```
```lean fixed (title := "Fixed (parenthesized)")
structure Person where
  (givenName familyName : String)
  age : Nat
```

If multiple identifiers are listed on the same line of a structure declaration without enclosing
parentheses, the first is taken to be the name of the field and all subsequent ones are elaborated
as binders. To prevent this behavior, either list each field on a separate line, or enclose the line
specifying multiple field names in parentheses.
-/
reregister_error_explanation Lean.InferBinderTypeFailed {
  summary := "The type of a binder could not be inferred."
  sinceVersion := "4.21.0"
}

/--
This error occurs when the type of a definition is not fully specified and the elaborator is unable
to infer the type from the available information. If the definition contains parameters, this error
refers only to the return type following the colon (the error
[`Lean.BinderTypeInferenceFailed`](lean-manual://errorExplanation/Lean.BinderTypeInferenceFailed)
appears if the type of a parameter cannot be inferred).

To resolve this error, provide additional type information in the definition. The simplest way to do
this is to provide an explicit return type after the colon in a definition header, or fill in holes
or implicit arguments if one is already present. Alternatively, adding further type information to
the body of the definition—such as by specifying implicit type arguments or giving explicit types to
`let` binders—may allow Lean to infer the type of the definition.

Note that if the resulting type of a definition is provided in the definition header—even if the
type contains holes—Lean will not use information from the definition body when inferring the
definition's type. To specify the resulting type without this behavior, use the `show` syntax
demonstrated in the example below. Additionally, it is always necessary to fully specify the type of
a `theorem` definition: the `theorem` declaration syntax requires a type annotation, and the
elaborator will never attempt to use the theorem body to infer the proposition being proved.

# Examples

## Specifying a polymorphic type parameter

```lean broken
def emptyNats :=
  []
```
```output
failed to infer definition type
```

```lean fixed (title := "Fixed (type annotation)")
def emptyNats : List Nat :=
  []
```
```lean fixed (title := "Fixed (implicit argument)")
def emptyNats :=
  List.nil (α := Nat)
```

Here, Lean is unable to infer the value of the parameter `α` of the `List` type constructor, which
also prevents it from inferring the type of the definition. Two fixes are possible: specifying the
expected type of the definition allows Lean to infer the appropriate implicit argument to the
`List.nil` constructor; alternatively, making this implicit argument explicit in the function body
provides sufficient information for Lean to infer the definition's type.

## Partial resulting type annotation prevents type inference

```lean broken
def greet : IO _ := do
  IO.println "Hello"
```
```output
don't know how to synthesize placeholder
context:
⊢ Type


Note: When the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
```
```lean fixed (title := "Fixed (type omitted)")
def greet := do
  IO.println "Hello"
```
```lean fixed (title := "Fixed ('show' syntax)")
def greet := show IO _ from do
  IO.println "Hello"
```
Because the nonfunctional example specifies an explicit resulting type (even though it has
holes), Lean does not attempt to use the body of the definition during type inference. As a result,
Lean is unable to synthesize the appropriate argument to `IO`. However, the type of the definition
is fully inferrable from its body; therefore, removing the type annotation entirely allows the
correct type to be inferred.
-/
reregister_error_explanation Lean.InferDefTypeFailed {
  summary := "The type of a definition was not fully provided and could not be inferred."
  sinceVersion := "4.21.0"
}
