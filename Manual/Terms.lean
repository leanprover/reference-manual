/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

#doc (Manual) "Terms" =>
%%%
tag := "terms"
%%%

::: planned 66
This chapter will describe Lean's term language, including the following features:
 * Name resolution, including variable occurrences, `open` declarations and terms
 * `fun`, with and without pattern matching
 * Literals (some via cross-references to the appropriate types, e.g. {name}`String`)
:::

{deftech}_Terms_ are the principal means of writing mathematics and programs in Lean.
The {tech}[elaborator] translates them to Lean's minimal core language, which is then checked by the kernel and compiled for execution.
The syntax of terms is {ref "syntax-ext"}[arbitrarily extensible]; this chapter documents the term syntax that Lean provides out-of-the-box.

# Identifiers

:::syntax term (title := "Identifiers")
```
$x:ident
```
:::

An identifier term is a reference to a name.{margin}[The specific lexical syntax of identifiers is described {ref "keywords-and-identifiers"}[in the section on Lean's concrete syntax].]
Identifiers also occur in contexts where they bind names, such as {keywordOf Lean.Parser.Term.let}`let` and {keywordOf Lean.Parser.Term.fun}`fun`; however, these binding occurrences are not complete terms in and of them selves.
The mapping from identifiers to names is not trivial: at any point in a {tech}[module], some number of {tech}[namespaces] will be open, there may be {tech}[section variables], and there may be local bindings.
Furthermore, identifiers may contain multiple dot-separated atomic identifiers; the dot both separates namespaces from their contents and variables from fields or functions that use {tech}[field notation].
This creates ambiguity, because an identifier `A.B.C.D.e.f` could refer to any of the following:

 * A name `f` in the namespace `A.B.C.D.e` (for instance, a function defined in `e`'s {keywordOf Lean.Parser.Command.declaration}`where` block).
 * An application of `T.f` to `A.B.C.D.e` if `A.B.C.D.e` has type `T`
 * A projection of field `f` from a structure named `A.B.C.D.e`
 * A series of field projections `B.C.D.e` from structure value `A`, followed by an application of `f` using field notation
 * If namespace `Q` is opened, it could be a reference to any of the above with a `Q` prefix, such as a name `f` in the namespace `Q.A.B.C.D.e`

This list is not exhaustive.
Given an identifier, the elaborator must discover which name or names an identifier refers to, and whether any of the trailing components are fields or functions applied via field notation.
This is called {deftech key:="resolve"}_resolving_ the name.

Some declarations in the global environment are lazily created the first time they are referenced.
Resolving an identifier in a way that both creates one of these declarations and results in a reference to it is called {deftech}_realizing_ the name.
The rules for resolving and realizing a name are the same, so even though this section refers only to resolving names, it applies to both.

Name resolution is affected by the following:
 * {tech key:="pre-resolved identifier"}[Pre-resolved names] attached to the identifier
 * The {tech}[macro scopes] attached to the identifier
 * The local bindings in scope, including auxiliary definitions created as part of the elaboration of {keywordOf Lean.Parser.Term.letrec}`let rec`.
 * Aliases created with {keywordOf Lean.Parser.Command.export}`export` in modules transitively imported by the current module
 * The current {tech}[section scope], in particular the current namespace, opened namespaces, and section variables


Any prefix of an identifier can resolve to a set of names.
The suffix that was not included in the resolution process is then treated as field projections or field notation.
Resolutions of longer prefixes take precedence over resolutions of shorter prefixes; in other words, as few components as of the identifier as possible are treated as field notation.
An identifier prefix may refer to any of the following, with earlier items taking precedence over later ones:
 1. A locally-bound variable whose name is identical to the identifier prefix, including macro scopes, with closer local bindings taking precedence over outer local bindings.
 2. A local auxiliary definition whose name is identical to the identifier prefix
 3. A {tech}[section variable] whose name is identical to the identifier prefix
 3. A global name that is identical to a prefix of the {tech}[current namespace] appended to the identifier prefix, or for which an alias exists in a prefix of the current namespace, with longer prefixes of the current namespace taking precedence over shorter ones
 4. A global name that has been brought into scope via {keywordOf Lean.Parser.Command.open}`open` commands that is identical to the identifier prefix


If an identifier resolves to multiple names, then the elaborator attempts to use all of them.
If exactly one of them succeeds, then it is used as the meaning of the identifier.
It is an error if more than one succeed or if all fail.

::::keepEnv
:::example "Local Names Take Precedence"
Local bindings take precedence over global bindings:
```lean (name := localOverGlobal)
def x := "global"

#eval
  let x := "local"
  x
```
```leanOutput localOverGlobal
"local"
```
The innermost local binding of a name takes precedence over others:
```lean (name := innermostLocal)
#eval
  let x := "outer"
  let x := "inner"
  x
```
```leanOutput innermostLocal
"inner"
```
:::
::::

::::keepEnv
:::example "Longer Prefixes of Current Namespace Take Precedence"
The  namespaces `A`, `B`, and `C` are nested, and `A` and `C` each contain a definition of `x`.
```lean (name := NS)
namespace A
def x := "A.x"
namespace B
namespace C
def x := "A.B.C.x"
```

When the current namespace is `A.B.C`, {lean}`x` resolves to {lean}`A.B.C.x`.
```lean (name := NSC)
#eval x
```
```leanOutput NSC
"A.B.C.x"
```
When the current namespace is `A.B`, {lean}`x` resolves to {lean}`A.x`.
```lean (name := NSB)
end C
#eval x
```
```leanOutput NSB
"A.x"
```
:::
::::

::::keepEnv
:::example "Longer Identifier Prefixes Take Precedence"
When an identifier could refer to different projections from names, the one with the longest name takes precedence:
```lean
structure A where
  y : String
deriving Repr

structure B where
  y : A
deriving Repr

def y : B := ⟨⟨"shorter"⟩⟩
def y.y : A := ⟨"longer"⟩
```
Given the above declarations, {lean}`y.y.y` could in principle refer either to the {name A.y}`y` field of the {name B.y}`y` field of {name}`y`, or to the {name A.y}`y` field of {name}`y.y`.
It refers to the {name A.y}`y` field of {name}`y.y`, because the name {name}`y.y` is a longer prefix of `y.y.y` than the name {name}`y`:
```lean (name := yyy)
#eval y.y.y
```
```leanOutput yyy
"longer"
```
:::
::::

::::keepEnv
:::example "Current Namespace Contents Take Precedence Over Opened Namespaces"
When an identifier could refer either to a name defined in a prefix of the current namespace or to an opened namespace, the former takes precedence.
```lean
namespace A
def x := "A.x"
end A

namespace B
def x := "B.x"
namespace C
open A
#eval x
```
Even though `A` was opened more recently than the declaration of {name}`B.x`, the identifier `x` resolves to {name}`B.x` rather than {name}`A.x` because `B` is a prefix of the current namespace `B.C`.
```lean (name := nestedVsOpen)
#eval x
```
```leanOutput nestedVsOpen
"B.x"
```
:::
::::

::::keepEnv
:::example "Ambiguous Identifiers"
In this example, `x` could refer either to {name}`A.x` or {name}`B.x`, and neither takes precedence.
Because both have the same type, it is an error.
```lean (name := ambi)
def A.x := "A.x"
def B.x := "B.x"
open A
open B
#eval x
```
```leanOutput ambi (whitespace := lax)
ambiguous, possible interpretations
  B.x : String

  A.x : String
```
```lean (show := false)
```
:::
::::
::::keepEnv
:::example "Disambiguation via Typing"
When they have different types, the types are used to disambiguate:
```lean (name := ambiNo)
def C.x := "C.x"
def D.x := 3
open C
open D
#eval (x : String)
```
```leanOutput ambiNo
"C.x"
```
:::
::::


## Leading `.`

When an identifier beings with a dot (`.`), the type that the elaborator expects for the expression is used to resolve it, rather than the current namespace and set of open namespaces.
{tech}[Generalized field notation] is related: leading dot notation uses the expect type of the identifier to resolve it to a name, while field notation uses the inferred type of the term immediately prior to the dot.

Identifiers with a leading `.` are to be looked up in the {deftech}_expected type's namespace_.
If the type expected for a term is a constant applied to zero or more arguments, then its namespace is the constant's name.
If the type is not an application of a constant (e.g., a function, a metavariable, or a universe) then it doesn't have a namespace.

If the name is not found in the expected type's namespace, but the constant can be unfolded to yield another constant, then its namespace is consulted.
This process is repeated until something other than an application of a constant is encountered, or until the constant can't be unfolded.

::::keepEnv
:::example "Leading `.`"
The expected type for {name List.replicate}`.replicate` is `List Unit`.
This type's namespace is `List`, so {name List.replicate}`.replicate` resolves to {name List.replicate}`List.replicate`.
```lean (name := dotRep)
#eval show List Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
:::

:::example "Leading `.` and Unfolding Definitions"
The expected type for {name List.replicate}`.replicate` is `MyList Unit`.
This type's namespace is `MyList`, but there is no definition `MyList.replicate`.
Unfolding {lean}`MyList Unit` yields {lean}`List Unit`, so {name List.replicate}`.replicate` resolves to {name List.replicate}`List.replicate`.
```lean (name := dotRep)
def MyList α := List α
#eval show MyList Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
:::
::::

# Function Types

Lean's function types describe more than just the function's domain and range.
They also provide instructions for elaborating application sites by indicating that some parameters are to be discovered automatically via unification or {ref "instance-synth"}[type class synthesis], that others are optional with default values, and that yet others should be synthesized using a custom tactic script.
Furthermore, their syntax contains support for abbreviating {tech key:="currying"}[curried] functions.

:::syntax term title:="Function types"
Dependent function types include an explicit name:
```grammar
($x:ident : $t) → $t2
```

Non-dependent function types do not:
```grammar
$t1:term → $t2
```
:::

:::syntax term title:="Curried Function Types"
Dependent function types may include multiple parameters that have the same type in a single set of parentheses:
```grammar
($x:ident* : $t) → $t
```
This is equivalent to repeating the type annotation for each parameter name in a nested function type.
:::

:::syntax term title:="Implicit, Optional, and Auto Parameters"
Function types can describe functions that take implicit, instance implicit, optional, and automatic parameters.
All but instance implicit parameters require one or more names.
```grammar
($x:ident* : $t := $e) → $t
```
```grammar
($x:ident* : $t := by $tacs) → $t
```
```grammar
{$x:ident* : $t} → $t
```
```grammar
[$t] → $t
```
```grammar
[$x:ident : $t] → $t
```
```grammar
⦃$x:ident* : $t⦄ → $t
```

:::

:::example "Multiple Parameters, Same Type"
The type of {name}`Nat.add` can be written in the following ways:

 * {lean}`Nat → Nat → Nat`

 * {lean}`(a : Nat) → (b : Nat) → Nat`

 * {lean}`(a b : Nat) → Nat`

The last two types allow the function to be used with {tech}[named arguments]; aside from this, all three are equivalent.
:::

# Functions

%%%
tag := "function-terms"
%%%


Terms with function types can be created via abstractions, introduced with the {keywordOf Lean.Parser.Term.fun}`fun` keyword.{margin}[In various communities, function abstractions are also known as _lambdas_, due to Alonzo Church's notation for them, or _anonymous functions_ because they don't need to be defined with a name in the global environment.]
While abstractions in the core type theory only allow a single variable to be bound, function terms are quite flexible in the high-level Lean syntax.

:::syntax term title:="Function Abstraction"
The most basic function abstraction introduces a variable to stand for the function's parameter:

```grammar
fun $x:ident => $t
```

At elaboration time, Lean must be able to determine the function's domain.
A type ascription is one way to provide this information:

```grammar
fun $x:ident : term => $t
```
:::

Function definitions defined with keywords such as {keywordOf Lean.Parser.Command.declaration parser:=Lean.Parser.Command.definition}`def` desugar to {keywordOf Lean.Parser.Term.fun}`fun`.
Inductive type declarations, on the other hand, introduce new values with function types (constructors and type constructors) that cannot themselves be implemented using just {keywordOf Lean.Parser.Term.fun}`fun`.

:::syntax term title:="Curried Functions"


Multiple parameter names are accepted after after {keywordOf Lean.Parser.Term.fun}`fun`:
```grammar
fun $x:ident $x:ident* => $t
```

```grammar
fun $x:ident $x:ident* : $t:term => $t
```

Different type annotations for multiple parameters requires parentheses:

```grammar
free{"fun " "(" (ident)* ": " term")" " =>" term}
```

These are equivalent to writing nested {keywordOf Lean.Parser.Term.fun}`fun` terms.
:::

The {keywordOf Lean.Parser.Term.fun}`=>` may be replaced by {keywordOf Lean.Parser.Term.fun}`↦` in all of the syntax described in this section.

Function abstractions may also use pattern matching syntax as part of their parameter specification, avoiding the need to introduce a local variable that is immediately destructured.
This syntax is described in the {ref "pattern-fun"}[section on pattern matching].

## Implicit Functions
%%%
tag := "implicit-functions"
%%%


Lean supports implicit parameters to functions.
This means that Lean itself can supply arguments to functions, rather than requiring users to supply all needed arguments.
Implicit parameters come in three varieties:

  : Ordinary implicit parameters

    Ordinary {deftech}[implicit] parameters are function parameters that Lean should determine values for via unification.
    In other words, each call site should have exactly one potential argument value that would cause the function call as a whole to be well-typed.
    The Lean elaborator attempts to find values for all implicit arguments at each occurrence of a function.
    Ordinary implicit parameters are written in curly braces (`{` and `}`).

  : Strict implicit parameters

    {deftech}_Strict implicit_ parameters are identical to ordinary implicit parameters, except Lean will only attempt to find argument values when subsequent explicit arguments are provided at a call site.
    Strict implicit parameters are written in double curly braces (`⦃` and `⦄`, or `{{` and `}}`).

  : Instance implicit parameters

    Arguments for {deftech}_instance implicit_ parameters are found via {ref "instance-synth"}[type class synthesis].
    Instance implicit parameters are written in square brackets (`[` and `]`), and in most cases omit the parameter name because instances synthesized as parameters to functions are already available in the functions' bodies, even without being named explicitly.

::::keepEnv
:::example "Ordinary vs Strict Implicit Parameters"
The difference between the functions {lean}`f` and {lean}`g` is that `α` is strictly implicit in {lean}`f`:
```lean
def f ⦃α : Type⦄ : α → α := fun x => x
def g {α : Type} : α → α := fun x => x
```

These functions are elaborated identically when applied to concrete arguments:
```lean
example : f 2 = g 2 := rfl
```

However, when the explicit argument is not provided, uses of {lean}`f` do not require the implicit `α` to be solved:
```lean
example := f
```
However, uses of `g` do require it to be solved, and fail to elaborate if there is insufficient information available:
```lean (error := true) (name := noAlpha)
example := g
```
```leanOutput noAlpha
don't know how to synthesize implicit argument 'α'
  @g ?m.6
context:
⊢ Type
```
:::
::::


:::syntax term title := "Functions with Varying Binders"
The most general syntax for {keywordOf Lean.Parser.Term.fun}`fun` accepts a sequence of binders:
```grammar
fun $p:funBinder $p:funBinder* => $t
```
:::


:::syntax Lean.Parser.Term.funBinder title:="Function Binders"
Function binders may be identifiers:
```grammar
$x:ident
```
sequences of identifiers with a type ascription:
```grammar
($x:ident $y:ident* : $t)
```
implicit parameters, with or without a type ascription:
```grammar
{$x:ident*}
```
```grammar
{$x:ident* : $t}
```
instance implicits, anonymous or named:
```grammar
[$t]
```
```grammar
[$x:ident : $t]
```
or strict implicit parameters, with or without a type ascription:
```grammar
⦃$t⦄
```
```grammar
⦃$x:ident* : $t⦄
```
:::


Lean's core language does not distinguish between implicit, instance, and explicit parameters: the various kinds of function and function type are definitionally equal.
The differences can be observed only during elaboration.

```lean (show := false)
-- Evidence of claims in prior paragraph
example : ({x : Nat} → Nat) = (Nat → Nat) := rfl
example : (fun {x} => 2 : {x : Nat} → Nat) = (fun x => 2 : Nat → Nat) := rfl
example : ([x : Repr Nat] → Nat) = (Repr Nat → Nat) := rfl
example : (⦃x : Nat⦄ → Nat) = (Nat → Nat) := rfl
```


If the expected type of a function includes implicit parameters, but its binders do not, then the resulting function may end up with more parameters than the binders indicated in the code.
This is because the implicit parameters are added automatically.

:::example "Implicit Parameters from Types"
The identity function can be written with a single explicit parameter.
As long as its type is known, the implicit type parameter is added automatically.
```lean (name := funImplAdd)
#check (fun x => x : {α : Type} → α → α)
```
```leanOutput funImplAdd
fun {α} x => x : {α : Type} → α → α
```

The following are all equivalent:
```lean (name := funImplThere)
#check (fun {α} x => x : {α : Type} → α → α)
```
```leanOutput funImplThere
fun {α} x => x : {α : Type} → α → α
```

```lean (name := funImplAnn)
#check (fun {α} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn
fun {α} x => x : {α : Type} → α → α
```

```lean (name := funImplAnn2)
#check (fun {α : Type} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn2
fun {α} x => x : {α : Type} → α → α
```

:::

# Function Application

Ordinarily, function application is written using juxtaposition: the argument is placed after the function, with at least one space between them.
In Lean's type theory, all functions take exactly one argument and produce exactly one value.
All function applications combine a single function with a single argument.
Multiple arguments are represented via currying.

The high-level term language treats a function together with one or more arguments as a single unit, and supports additional features such as implicit, optional, and by-name arguments along with ordinary positional arguments.
The elaborator converts these to the simpler model of the core type theory.

:::freeSyntax term
A function application consists of a term followed by one or more arguments, or by zero or more arguments and a final {deftech}[ellipsis].
```grammar
$e:term $e:argument+
***************
$e:term $e:argument* ".."
```
:::

{TODO}[Annotate with syntax kinds for incoming hyperlinks during traversal pass]
:::freeSyntax Lean.Parser.Term.argument (title := "Arguments")
Function arguments are either terms or {deftech}[named arguments].
```grammar
$e:term
***********
"("$x:ident ":=" $e:term")"
```
:::

The function's core-language type determines the placement of the arguments in the final expression.
Function types include names for their expected parameters.
In Lean's core language, non-dependent function types are encoded as dependent function types in which the parameter name does not occur in the body.
Furthermore, they are chosen internally such that they cannot be written as the name of a named argument; this is important to prevent accidental capture.

Each parameter expected by the function has a name.
Recurring over the function's argument types, arguments are selected from the sequence of arguments as follows:
 * If the parameter's name matches the name provided for a named argument, then that argument is selected.
 * If the parameter is {tech}[implicit], a fresh metavariable is created with the parameter's type and selected.
 * If the parameter is {tech}[instance implicit], a fresh instance metavariable is created with the parameter's type and inserted. Instance metavariables are scheduled for later synthesis.
 * If the parameter is a {tech}[strict implicit] parameter and there are any named or positional arguments that have not yet been selected, a fresh metavariable is created with the parameter's type and selected.
 * If the parameter is explicit, then the next positional argument is selected and elaborated. If there are no positional arguments:
   * If the parameter is declared as an {tech}[optional parameter], then its default value is selected as the argument.
   * If the parameter is an {tech}[automatic parameter] then its associated tactic script is executed to construct the argument.
   * If the parameter is neither optional nor automatic, and no ellipsis is present, then a fresh variable is selected as the argument. If there is an ellipsis, a fresh metavariable is selected as if the argument were implicit.

As a special case, when the function application occurs in a {ref "pattern-matching"}[pattern] and there is an ellipsis, optional and automatic arguments become universal patterns (`_`) instead of being inserted.

It is an error if the type is not a function type and arguments remain.
After all arguments have been inserted and there is an ellipsis, then the missing arguments are all set to fresh metavariables, just as if they were implicit arguments.
If any fresh variables were created for missing explicit positional arguments, the entire application is wrapped in a {keywordOf Lean.Parser.Term.fun}`fun` term that binds them.
Finally, instance synthesis is invoked and as many metavariables as possible are solved:
 1. A type is inferred for the entire function application. This may cause some metavariables to be solved due to unification that occurs during type inference.
 2. The instance metavariables are synthesized. {tech}[Default instances] are only used if the inferred type is a metavariable that is the output parameter of one of the instances.
 3. If there is an expected type, it is unified with the inferred type; however, errors resulting from this unification are discarded. If the expected and inferred types can be equal, unification can solve leftover implicit argument metavariables. If they can't be equal, an error is not thrown because a surrounding elaborator may be able to insert {tech}[coercions] or {tech key:="lift"}[monad lifts].


::::keepEnv
:::example "Named Arguments"
The {keywordOf Lean.Parser.Command.check}`#check` command can be used to inspect the arguments that were inserted for a function call.

The function {name}`sum3` takes three explicit {lean}`Nat` parameters, named `x`, `y`, and `z`.
```lean
def sum3 (x y z : Nat) : Nat := x + y + z
```

All three arguments can be provided positionally.
```lean (name := sum31)
#check sum3 1 3 8
```
```leanOutput sum31
sum3 1 3 8 : Nat
```

They can also be provided by name.
```lean (name := sum32)
#check sum3 (x := 1) (y := 3) (z := 8)
```
```leanOutput sum32
sum3 1 3 8 : Nat
```

When arguments are provided by name, it can be in any order.
```lean (name := sum33)
#check sum3 (y := 3) (z := 8) (x := 1)
```
```leanOutput sum33
sum3 1 3 8 : Nat
```

Named and positional arguments may be freely intermixed.
```lean (name := sum34)
#check sum3 1 (z := 8) (y := 3)
```
```leanOutput sum34
sum3 1 3 8 : Nat
```

Named and positional arguments may be freely intermixed.
If an argument is provided by name, it is used, even if it occurs after a positional argument that could have been used.
```lean (name := sum342)
#check sum3 1 (x := 8) (y := 3)
```
```leanOutput sum342
sum3 8 3 1 : Nat
```

If a named argument is to be inserted after arguments that aren't provided, a function is created in which the provided argument is filled out.
```lean (name := sum35)
#check sum3 (z := 8)
```
```leanOutput sum35
fun x y => sum3 x y 8 : Nat → Nat → Nat
```

Behind the scenes, the names of the arguments are preserved in the function type.
This means that the remaining arguments can again be passed by name.
```lean (name := sum36)
#check (sum3 (z := 8)) (y := 1)
```
```leanOutput sum36
fun x => (fun x y => sum3 x y 8) x 1 : Nat → Nat
```

```lean (show := false)
-- This is not shown in the manual pending #6373
-- https://github.com/leanprover/lean4/issues/6373
-- When the issue is fixed, this code will stop working and the text can be updated.

/--
info: let x := 15;
fun x y => sum3 x y x : Nat → Nat → Nat
-/
#guard_msgs in
#check let x := 15; sum3 (z := x)
```

:::
::::


Optional and automatic parameters are not part of Lean's core type theory.
They are encoded using the {name}`optParam` and {name}`autoParam` {tech}[gadgets].

{docstring optParam}

{docstring autoParam}

## Generalized Field Notation

The {ref "structure-fields"}[section on structure fields] describes the notation for projecting a field from a term whose type is a structure.
Generalized field notation consists of a term followed by a dot (`.`) and an identifier, not separated by spaces.

:::syntax term (title := "Field Notation")
```grammar
$e:term.$f:ident
```
:::

If a term's type is a constant applied to zero or more arguments, then {deftech}[field notation] can be used to apply a function to it, regardless of whether the term is a structure or type class instance that has fields.
The use of field notation to apply other functions is called {deftech}_generalized field notation_.

The identifier after the dot is looked up in the namespace of the term's type, which is the constant's name.
If the type is not an application of a constant (e.g., a function, a metavariable, or a universe) then it doesn't have a namespace and generalized field notation cannot be used.
If the field is not found, but the constant can be unfolded to yield a further type which is a constant or application of a constant, then the process is repeated with the new constant.

When a function is found, the term before the dot becomes an argument to the function.
Specifically, it becomes the first explicit argument that would not be a type error.
Aside from that, the application is elaborated as usual.

::::keepEnv
```lean (show := false)
section
variable (name : Username)
```
:::example "Generalized Field Notation"
The type {lean}`Username` is a constant, so functions in the {name}`Username` namespace can be applied to terms with type {lean}`Username` with generalized field notation.
```lean
def Username := String
```

One such function is {name}`Username.validate`, which checks that a username contains no leading whitespace and that only a small set of acceptable characters are used.
In its definition, generalized field notation is used to call the functions {lean}`String.isPrefixOf`, {lean}`String.any`, {lean}`Char.isAlpha`, and {lean}`Char.isDigit`.
In the case of {lean}`String.isPrefixOf`, which takes two {lean}`String` arguments, {lean}`" "` is used as the first  because it's the term before the dot.
{lean}`String.any` can be called on {lean}`name` using generalized field notation even though it has type {lean}`Username` because `Username.any` is not defined and {lean}`Username` unfolds to {lean}`String`.

```lean
def Username.validate (name : Username) : Except String Unit := do
  if " ".isPrefixOf name then
    throw "Unexpected leading whitespace"
  if name.any notOk then
    throw "Unexpected character"
  return ()
where
  notOk (c : Char) : Bool :=
    !c.isAlpha &&
    !c.isDigit &&
    !c ∈ ['_', ' ']

def root : Username := "root"
```

However, {lean}`Username.validate` can't be called on {lean}`"root"` using field notation, because {lean}`String` does not unfold to {lean}`Username`.
```lean (error := true) (name := notString)
#eval "root".validate
```
```leanOutput notString
invalid field 'validate', the environment does not contain 'String.validate'
  "root"
has type
  String
```

{lean}`root`, on the other hand, has type {lean}`Username`:
```lean (name := isUsername)
#eval root.validate
```
```leanOutput isUsername
Except.ok ()
```
:::
```lean (show := false)
end
```
::::

{optionDocs pp.fieldNotation}

:::syntax attr (title := "Controlling Field Notation")
The {attr}`pp_nodot` attribute causes Lean's pretty printer to not use field notation when printing a function.
```grammar
pp_nodot
```
:::

::::keepEnv
:::example "Turning Off Field Notation"
{lean}`Nat.half` is printed using field notation by default.
```lean
def Nat.half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => n.half + 1
```
```lean (name := succ1)
#check Nat.half Nat.zero
```
```leanOutput succ1
Nat.zero.half : Nat
```
Adding {attr}`pp_nodot` to {name}`Nat.half` causes ordinary function application syntax to be used instead when displaying the term.
```lean (name := succ2)
attribute [pp_nodot] Nat.half

#check Nat.half Nat.zero
```
```leanOutput succ2
Nat.half Nat.zero : Nat
```
:::
::::

## Pipeline Syntax

Pipeline syntax provides alternative ways to write function applications.
Repeated pipelines use parsing precedence instead of nested parentheses to nest applications of functions to positional arguments.

:::syntax term (title := "Pipelines")
Right pipe notation applies the term to the right of the pipe to the one on its left.
```grammar
e |> e
```
Left pipe notation applies the term on the left of the pipe to the one on its right.
```grammar
e <| e
```
:::

The intuition behind right pipeline notation is that the values on the left are being fed to the first function, its results are fed to the second one, and so forth.
In left pipeline notation, values on the right are fed leftwards.

:::example "Right pipeline notation"
Right pipelines can be used to call a series of functions on a term.
For readers, they tend to emphasize the data that's being transformed.
```lean (name := rightPipe)
#eval "Hello!" |> String.toList |> List.reverse |> List.head!
```
```leanOutput rightPipe
'!'
```
:::

:::example "Left pipeline notation"
Left pipelines can be used to call a series of functions on a term.
They tend to emphasize the functions over the data.
```lean (name := lPipe)
#eval List.head! <| List.reverse <| String.toList <| "Hello!"
```
```leanOutput lPipe
'!'
```
:::

:::syntax term (title := "Pipeline Fields")
There is a version of pipeline notation that's used for {tech}[generalized field notation].
```grammar
$e |>.$_:ident
```
```grammar
$e |>.$_:fieldIdx
```
:::

::::keepEnv
```lean (show := false)
section
universe u
axiom T : Nat → Type u
variable {e : T 3} {arg : Char}
axiom T.f : {n : Nat} → Char → T n → String
```

{lean}`e |>.f arg` is an alternative syntax for {lean}`(e).f arg`.


:::example "Pipeline Fields"

Some functions are inconvenient to use with pipelines because their argument order is not conducive.
For example, {name}`Array.push` takes an array as its first argument, not a {lean}`Nat`, leading to this error:
```lean (name := arrPush)
#eval #[1, 2, 3] |> Array.push 4
```
```leanOutput arrPush
failed to synthesize
  OfNat (Array ?m.4) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  Array ?m.4
due to the absence of the instance above
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

Using pipeline field notation causes the array to be inserted at the first type-correct position:
```lean (name := arrPush2)
#eval #[1, 2, 3] |>.push 4
```
```leanOutput arrPush2
#[1, 2, 3, 4]
```

This process can be iterated:
```lean (name := arrPush3)
#eval #[1, 2, 3] |>.push 4 |>.reverse |>.push 0 |>.reverse
```
```leanOutput arrPush3
#[0, 1, 2, 3, 4]
```
:::


```lean (show := false)
end
```
::::

# Literals

There are two kinds of numeric literal: natural number literals and {deftech}[scientific literals].
Both are overloaded via {tech key:="type class"}[type classes].

## Natural Numbers

```lean (show := false)
section
variable {n : Nat}
```

When Lean encounters a natural number literal {lean}`n`, it interprets it via the overloaded method {lean}`OfNat.ofNat n`.
A {tech}[default instance] of {lean}`OfNat Nat n` ensures that the type {lean}`Nat` can be inferred when no other type information is present.

{docstring OfNat}

```lean (show := false)
end
```

:::example "Custom Natural Number Literals"
The structure {lean}`NatInterval` represents an interval of natural numbers.
```lean
structure NatInterval where
  low : Nat
  high : Nat
  low_le_high : low ≤ high

instance : Add NatInterval where
  add
    | ⟨lo1, hi1, le1⟩, ⟨lo2, hi2, le2⟩ => ⟨lo1 + lo2, hi1 + hi2, by omega⟩
```

An {name}`OfNat` instance allows natural number literals to be used to represent intervals:
```lean
instance : OfNat NatInterval n where
  ofNat := ⟨n, n, by omega⟩
```
```lean (name := eval8Interval)
#eval (8 : NatInterval)
```
```leanOutput eval8Interval
{ low := 8, high := 8, low_le_high := _ }
```
:::

There are no separate integer literals.
Terms such as {lean}`-5` consist of a prefix negation (which can be overloaded via the {name}`Neg` type class) applied to a natural number literal.

## Scientific Numbers

Scientific number literals consist of a sequence of digits followed by an optional period and decimal part and an optional exponent.
If no period or exponent is present, then the term is instead a natural number literal.
Scientific numbers are overloaded via the {name}`OfScientific` type class.

{docstring OfScientific}

There is an {lean}`OfScientific` instance for {name}`Float`, but no separate floating-point literals.

## Strings

String literals are described in the {ref "string-syntax"}[chapter on strings.]

## Lists and Arrays

List and array literals contain comma-separated sequences of elements inside of brackets, with arrays prefixed by a hash mark (`#`).
Array literals are interpreted as list literals wrapped in a call to a conversion.
For performance reasons, very large list and array literals are converted to sequences of local definitions, rather than just iterated applications of the list constructor.

:::syntax term (title := "List Literals")
```grammar
[$_,*]
```
:::

:::syntax term (title := "Array Literals")
```grammar
#[$_,*]
```
:::

:::example "Long List Literals"
This list contains 32 elements.
The generated code is an iterated application of {name}`List.cons`:
```lean (name := almostLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1]
```
```leanOutput almostLong
[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List Nat
```

With 33 elements, the list literal becomes a sequence of local definitions:
```lean (name := indeedLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1]
```
```leanOutput indeedLong
let y :=
  let y :=
    let y := [1, 1, 1, 1, 1];
    1 :: 1 :: 1 :: 1 :: y;
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y :=
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y := 1 :: 1 :: 1 :: 1 :: y;
1 :: 1 :: 1 :: 1 :: y : List Nat
```

:::

# Structures and Constructors

{ref "anonymous-constructor-syntax"}[Anonymous constructors] and {ref "structure-constructors"}[structure instance syntax] are described in their respective sections.

# Conditionals
%%%
tag := "if-then-else"
%%%

The conditional expression is used to check whether a proposition is true or false.{margin}[Despite their syntactic similarity, the {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if` used {ref "tactic-language-branching"}[in the tactic language] and the {keywordOf Lean.Parser.Term.doIf}`if` used {ref "tactic-language-branching"}[in `do`-notation] are separate syntactic forms, documented in their own sections.]
This requires that the proposition has a {name}`Decidable` instance, because it's not possible to check whether _arbitrary_ propositions are true or false.
There is also a {tech}[coercion] from {name}`Bool` to {lean}`Prop` that results in a decidable proposition (namely, that the {name}`Bool` in question is equal to {name}`true`), described in the {ref "decidable-propositions"}[section on decidability].

There are two versions of the conditional expression: one simply performs a case distinction, while the other additionally adds an assumption about the proposition's truth or falsity to the local context.
This allows run-time checks to generate compile-time evidence that can be used to statically rule out errors.

:::syntax term (title := "Conditionals")
Without a name annotation, the conditional expression expresses only control flow.
```grammar
if $e then
  $e
else
  $e
```

With the name annotation, the branches of the {keywordOf termDepIfThenElse}`if` have access to a local assumption that the proposition is respectively true or false.
```grammar
if h : $e then
  $e
else
  $e
```
:::


::::keepEnv
:::example "Checking Array Bounds"

Array indexing requires evidence that the index in question is within the bounds of the array, so {name}`getThird` does not elaborate.

```lean (error := true) (keep := false) (name := getThird1)
def getThird (xs : Array α) : α := xs[2]
```
```leanOutput getThird1
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```

Relaxing the return type to {name}`Option` and adding a bounds check results the same error.
This is because the proof that the index is in bounds was not added to the local context.
```lean (error := true) (keep := false) (name := getThird2)
def getThird (xs : Array α) : Option α :=
  if xs.size ≥ 3 then none
  else xs[2]
```
```leanOutput getThird2
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```

Naming the proof `h` is sufficient to enable the tactics that perform bounds checking to succeed, even though it does not occur explicitly in the text of the program.
```lean
def getThird (xs : Array α) : Option α :=
  if h : xs.size ≥ 3 then none
  else xs[2]
```

:::
::::

There is also a pattern-matching version of {keywordOf termIfLet}`if`.
If the pattern matches, then it takes the first branch, binding the pattern variables.
If the pattern does not match, then it takes the second branch.

:::syntax term (title := "Pattern-Matching Conditionals")
```grammar
if let $p := $e then
  $e
else
  $e
```
:::


If a {name}`Bool`-only conditional statement is ever needed, the {keywordOf boolIfThenElse}`bif` variant can be used.
:::syntax term (title := "Boolean-Only Conditional")
```grammar
bif $e then
  $e
else
  $e
```
:::


# Pattern Matching
%%%
tag := "pattern-matching"
%%%


{deftech}_Pattern matching_ is a way to recognize and destructure values using a syntax of {deftech}_patterns_ that are a subset of the terms.
A pattern that recognizes and destructures a value is similar to the syntax that would be used to construct the value.
One or more {deftech}_match discriminants_ are simultaneously compared to a series of {deftech}_match alternatives_.
Discriminants may be named.
Each alternative contains one or more comma-separated sequences of patterns; all pattern sequences must contain the same number of patterns as there are discriminants.
When a pattern sequence matches all of the discriminants, the term following the corresponding {keywordOf Lean.Parser.Term.match}`=>` is evaluated in an environment extended with values for each {tech}[pattern variable] as well as an equality hypothesis for each named discriminant.
This term is called the {deftech}_right-hand side_ of the match alternative.

:::syntax term (title := "Pattern Matching")
```grammar
match
    $[(generalizing := $e)]?
    $[(motive := $e)]?
    $[$d:matchDiscr],*
  with
$[| $[$e,*]|* => $e]*
```
:::

:::syntax matchDiscr (title := "Match Discriminants") (open := false)
```grammar
$e:term
```
```grammar
$h:ident : $e:term
```
:::

Pattern matching expressions may alternatively use {tech}[quasiquotations] as patterns, matching the corresponding {name}`Lean.Syntax` values and treating the contents of {tech}[antiquotations] as ordinary patterns.
Quotation patterns are compiled differently than other patterns, so if one pattern in a {keywordOf Lean.Parser.Term.match}`match` is syntax, then all of them must be.
Quotation patterns are described in {ref "quote-patterns"}[the section on quotations].

Patterns are a subset of the terms.
They consist of the following:

: Catch-All Patterns

  The hole syntax {lean}`_` is a pattern that matches any value and binds no pattern variables.
  Catch-all patterns are not entirely equivalent to unused pattern variables.
  They can be used in positions where the pattern's typing would otherwise require a more specific {tech}[inaccessible pattern], while variables cannot be used in these positions.

: Identifiers

  If an identifier is not bound in the current scope and is not applied to arguments, then it represents a pattern variable.
  {deftech}_Pattern variables_ match any value, and the values thus matched are bound to the pattern variable in the local environment in which the {tech}[right-hand side] is evaluated.
  If the identifier is bound, it is a pattern if it is bound to the {tech}[constructor] of an {tech}[inductive type] or if its definition has the {attr}`match_pattern` attribute.

: Applications

  Function applications are patterns if the function being applied is an identifier that is bound to a constructor or that has the {attr}`match_pattern` attribute and if all arguments are also patterns.
  If the identifier is a constructor, the pattern matches values built with that constructor if the argument patterns match the constructor's arguments.
  If it is a function with the {attr}`match_pattern` attribute, then the function application is unfolded and the resulting term's {tech}[normal form] is used as the pattern.
  Default arguments are inserted as usual, and their normal forms are used as patterns.
  {tech key:="ellipsis"}[Ellipses], however, result in all further arguments being treated as universal patterns, even those with associated default values or tactics.

: Literals

  {ref "char-syntax"}[Character literals] and {ref "string-syntax"}[string literals] are patterns that match the corresponding character or string.
  {ref "raw-string-literals"}[Raw string literals] are allowed as patterns, but {ref "string-interpolation"}[interpolated strings] are not.
  {ref "nat-syntax"}[Natural number literals] in patterns are interpreted by synthesizing the corresponding {name}`OfNat` instance and reducing the resulting term to {tech}[normal form], which must be a pattern.
  Similarly, {tech}[scientific literals] are interpreted via the corresponding {name}`OfScientific` instance.
  While {lean}`Float` has such an instance, {lean}`Float`s cannot be used as patterns because the instance relies on an opaque function that can't be reduced to a valid pattern.

: Structure Instances

  {tech}[Structure instances] may be used as patterns.
  They are interpreted as the corresponding structure constructor.

: Quoted names

  Quoted names, such as {lean}`` `x `` and {lean}``` ``plus ```, match the corresponding {name}`Lean.Name` value.

: Macros

  Macros in patterns are expanded.
  They are patterns if the resulting expansions are patterns.

: Inaccessible patterns

  {deftech}[Inaccessible patterns] are patterns that are forced to have a particular value by later typing constraints.
  Any term may be used as an inaccessible term.
  Inaccessible terms are parenthesized, with a preceding period (`.`).

:::syntax term (title := "Inaccessible Patterns")
```grammar
.($e)
```
:::

:::example "Inaccessible Patterns"
A number's _parity_ is whether it's even or odd:
```lean
inductive Parity : Nat → Type where
  | even (h : Nat) : Parity (h + h)
  | odd (h : Nat) : Parity ((h + h) + 1)

def Nat.parity (n : Nat) : Parity n :=
  match n with
  | 0 => .even 0
  | n' + 1 =>
    match n'.parity with
    | .even h => .odd h
    | .odd h =>
      have eq : (h + 1) + (h + 1) = (h + h + 1 + 1) :=
        by omega
      eq ▸ .even (h + 1)
```

Because a value of type {lean}`Parity` contains half of a number (rounded down) as part of its representation of evenness or oddness, division by two can be implemented (in an unconventional manner) by finding a parity and then extracting the number.
```lean
def half (n : Nat) : Nat :=
  match n, n.parity with
  | .(h + h),     .even h => h
  | .(h + h + 1), .odd h  => h
```
Because the index structure of {name}`Parity.even` and {name}`Parity.odd` force the number to have a certain form that is not otherwise a valid pattern, patterns that match on it must use inaccessible patterns for the number being divided.
:::

Patterns may additionally be named.
{deftech}[Named patterns] associate a name with a pattern; in subsequent patterns and on the right-hand side of the match alternative, the name refers to the part of the value that was matched by the given pattern.
Named patterns are written with an `@` between the name and the pattern.
Just like discriminants, named patterns may also be provided with names for equality assumptions.

:::syntax term (title := "Named Patterns")
```grammar
$x:ident@$e
```
```grammar
$x:ident@$h:ident:$e
```
:::


```lean (show := false) (keep := false)
-- Check claims about patterns

-- Literals
/-- error: invalid pattern, constructor or constant marked with '[match_pattern]' expected -/
#guard_msgs in
def foo (x : String) : String :=
  match x with
  | "abc" => ""
  | r#"hey"# => ""
  | s!"a{x}y" => _
  | _ => default

structure Blah where
  n : Nat
deriving Inhabited

instance : OfNat Blah n where
  ofNat := ⟨n + 1⟩

/--
error: missing cases:
(Blah.mk (Nat.succ (Nat.succ _)))
(Blah.mk Nat.zero)
-/
#guard_msgs in
def abc (n : Blah) : Bool :=
  match n with
  | 0 => true

partial instance : OfNat Blah n where
  ofNat :=
    let rec f (x : Nat) : Blah :=
      match x with
      | 0 => f 99
      | n + 1 => f n
    f n

-- This shows that the partial instance was not unfolded
/--
error: dependent elimination failed, type mismatch when solving alternative with type
  motive (instOfNatBlah_1.f 0)
but expected
  motive n✝
-/
#guard_msgs in
def defg (n : Blah) : Bool :=
  match n with
  | 0 => true

/--
error: dependent elimination failed, type mismatch when solving alternative with type
  motive (Float.ofScientific 25 true 1)
but expected
  motive x✝
-/
#guard_msgs in
def twoPointFive? : Float → Option Float
  | 2.5 => some 2.5
  | _ => none

/--
info: @Neg.neg.{0} Float instNegFloat (@OfScientific.ofScientific.{0} Float instOfScientificFloat 320 Bool.true 1) : Float
-/
#guard_msgs in
set_option pp.all true in
#check -32.0

structure OnlyThreeOrFive where
  val : Nat
  val2 := false
  ok : val = 3 ∨ val = 5 := by rfl


-- Default args are synthesized in patterns too!
/--
error: tactic 'rfl' failed, the left-hand side
  n = 3
is not definitionally equal to the right-hand side
  n = 5
x✝ : OnlyThreeOrFive
n : Nat
⊢ n = 3 ∨ n = 5
-/
#guard_msgs in
def ggg : OnlyThreeOrFive → Nat
  | {val := n} => n

/--
error: missing cases:
(OnlyThreeOrFive.mk _ true _)
-/
#guard_msgs in
def hhh : OnlyThreeOrFive → Nat
  | {val := n, ok := p} => n

-- Ellipses don't synth default args in patterns
def ggg' : OnlyThreeOrFive → Nat
  | .mk n .. => n

-- Ellipses do synth default args via tactics, but not exprs, otherwise
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: tactic 'rfl' failed, the left-hand side
  3 = 3
is not definitionally equal to the right-hand side
  3 = 5
⊢ 3 = 3 ∨ 3 = 5
---
info: { val := 3, val2 := ?m.1487, ok := ⋯ } : OnlyThreeOrFive
-/
#guard_msgs in
#check OnlyThreeOrFive.mk 3 ..

/-- info: { val := 3, val2 := ?_, ok := ⋯ } : OnlyThreeOrFive -/
#guard_msgs in
set_option pp.mvars.anonymous false in
#check OnlyThreeOrFive.mk 3 (ok := .inl rfl) ..

/--
info: fun y =>
  match
    let_fun this := ⟨y * 3, ⋯⟩;
    this with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), ⋯ => () : Nat → Unit
-/
#guard_msgs in
#check fun (y : Nat) => match show {n : Nat// n = y * 3} from ⟨y*3, rfl⟩ with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), rfl => ()

```

## Types

Each discriminant must be well typed.
Because patterns are a subset of terms, their types can also be checked.
Each pattern that matches a given discriminant must have the same type as the corresponding discriminant.

The {tech}[right-hand side] of each match alternative should have the same type as the overall {keywordOf Lean.Parser.Term.match}`match` term.
To support dependent types, matching a discriminant against a pattern refines the types that are expected within the scope of the pattern.
In both subsequent patterns in the same match alternative and the right-hand side's type, occurrences of the discriminant are replaced by the pattern that it was matched against.


::::keepEnv
```lean (show := false)
variable {α : Type u}
```

:::example "Type Refinement"
This {tech}[indexed family] describes mostly-balanced trees, with the depth encoded in the type.
```lean
inductive BalancedTree (α : Type u) : Nat → Type u where
  | empty : BalancedTree α 0
  | branch (left : BalancedTree α n) (val : α) (right : BalancedTree α n) : BalancedTree α (n + 1)
  | lbranch (left : BalancedTree α (n + 1)) (val : α) (right : BalancedTree α n) : BalancedTree α (n + 2)
  | rbranch (left : BalancedTree α n) (val : α) (right : BalancedTree α (n + 1)) : BalancedTree α (n + 2)
```

To begin the implementation of a function to construct a perfectly balanced tree with some initial element and a given depth, a {tech}[hole] can be used for the definition.
```lean (keep := false) (name := fill1) (error := true)
def BalancedTree.filledWith (x : α) (depth : Nat) : BalancedTree α depth := _
```
The error message demonstrates that the tree should have the indicated depth.
```leanOutput fill1
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α depth
```

Matching on the expected depth and inserting holes results in an error message for each hole.
These messages demonstrate that the expected type has been refined, with `depth` replaced by the matched values.
```lean (error := true) (name := fill2)
def BalancedTree.filledWith (x : α) (depth : Nat) : BalancedTree α depth :=
  match depth with
  | 0 => _
  | n + 1 => _
```
The first hole yields the following message:
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α 0
```
The second hole yields the following message:
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth n : Nat
⊢ BalancedTree α (n + 1)
```

Matching on the depth of a tree and the tree itself leads to a refinement of the tree's type according to the depth's pattern.
This means that certain combinations are not well-typed, such as {lean}`0` and {name BalancedTree.branch}`branch`, because refining the second discriminant's type yields {lean}`BalancedTree α 0` which does not match the constructor's type.
````lean (name := patfail) (error := true)
def BalancedTree.isPerfectlyBalanced (n : Nat) (t : BalancedTree α n) : Bool :=
  match n, t with
  | 0, .empty => true
  | 0, .branch left val right => isPerfectlyBalanced left && isPerfectlyBalanced right
  | _, _ => false
````
```leanOutput patfail
type mismatch
  left.branch val right
has type
  BalancedTree ?m.53 (?m.50 + 1) : Type ?u.46
but is expected to have type
  BalancedTree α 0 : Type u
```
:::
::::

### Pattern Equality Proofs

When a discriminant is named, {keywordOf Lean.Parser.Term.match}`match` generates a proof that the pattern and discriminant are equal, binding it to the provided name in the {tech}[right-hand side].
This is useful to bridge the gap between dependent pattern matching on indexed families and APIs that expect explicit propositional arguments, and it can help tactics that make use of assumptions to succeed.

:::example "Pattern Equality Proofs"
The function {lean}`last?`, which either throws an exception or returns the last element of its argument, uses the standard library function {lean}`List.getLast`.
This function expects a proof that the list in question is nonempty.
Naming the match on `xs` ensures that there's an assumption in scope that states that `xs` is equal to `_ :: _`, which {tactic}`simp_all` uses to discharge the goal.
```lean
def last? (xs : List α) : Except String α :=
  match h : xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```

Without the name, {tactic}`simp_all` is unable to find the contradiction.
```lean (error := true) (name := namedHyp)
def last?' (xs : List α) : Except String α :=
  match xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```
```leanOutput namedHyp
simp_all made no progress
```
:::

### Explicit Motives

Pattern matching is not a built-in primitive of Lean.
Instead, it is translated to applications of {tech}[recursors] via {tech}[auxiliary matching functions].
Both require a {tech}_motive_ that explains the relationship between the discriminant and the resulting type.
Generally, the {keywordOf Lean.Parser.Term.match}`match` elaborator is capable of synthesizing an appropriate motive, and the refinement of types that occurs during pattern matching is a result of the motive that was selected.
In some specialized circumstances, a different motive may be needed and may be provided explicitly using the `(motive := …)` syntax of {keywordOf Lean.Parser.Term.match}`match`.
This motive should be a function type that expects at least as many parameters as there are discriminants.
The type that results from applying a function with this type to the discriminants in order is the type of the entire {keywordOf Lean.Parser.Term.match}`match` term, and the type that results from applying a function with this type to all patterns in each alternative is the type of that alternative's {tech}[right-hand side].

:::example "Matching with an Explicit Motive"
An explicit motive can be used to provide type information that is otherwise unavailable from the surrounding context.
Attempting to match on a number and a proof that it is in fact {lean}`5` is an error, because there's no reason to connect the number to the proof:
```lean (error := true) (name := noMotive)
#eval
  match 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput noMotive
invalid match-expression, pattern contains metavariables
  Eq.refl ?m.73
```
An explicit motive explains the relationship between the discriminants:
```lean (name := withMotive)
#eval
  match (motive := (n : Nat) → n = 5 → String) 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput withMotive
"ok"
```
:::

### Discriminant Refinement

When matching on an indexed family, the indices must also be discriminants.
Otherwise, the pattern would not be well typed: it is a type error if an index is just a variable but the type of a constructor requires a more specific value.
However, a process called {deftech}[discriminant refinement] automatically adds indices as additional discriminants.

::::keepEnv
:::example "Discriminant Refinement"
In the definition of {lean}`f`, the equality proof is the only discriminant.
However, equality is an indexed family, and the match is only valid when `n` is an additional discriminant.
```lean
def f (n : Nat) (p : n = 3) : String :=
  match p with
  | rfl => "ok"
```
Using {keywordOf Lean.Parser.Command.print}`#print` demonstrates that the additional discriminant was added automatically.
```lean (name := fDef)
#print f
```
```leanOutput fDef
def f : (n : Nat) → n = 3 → String :=
fun n p =>
  match 3, p with
  | .(n), ⋯ => "ok"
```
:::
::::

### Generalization
%%%
tag := "match-generalization"
%%%

The pattern match elaborator automatically determines the motive by finding occurrences of the discriminants in the expected type, generalizing them in the types of subsequent discriminants so that the appropriate pattern can be substituted.
Additionally, occurrences of the discriminants in the types of variables in the context are generalized and substituted by default.
This latter behavior can be turned off by passing the `(generalizing := false)` flag to {keywordOf Lean.Parser.Term.match}`match`.

:::::keepEnv
::::example "Matching, With and Without Generalization"
```lean (show := false)
variable {α : Type u} (b : Bool) (ifTrue : b = true → α) (ifFalse : b = false → α)
```
In this definition of {lean}`boolCases`, the assumption {lean}`b` is generalized in the type of `h` and then replaced with the actual pattern.
This means that {lean}`ifTrue` and {lean}`ifFalse` have the types {lean}`true = true → α` and {lean}`false = false → α` in their respective cases, but `h`'s type mentions the original discriminant.

```lean (error := true) (name := boolCases1) (keep := false)
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
The error for the first case is typical of both:
```leanOutput boolCases1
application type mismatch
  ifTrue h
argument
  h
has type
  b = true : Prop
but is expected to have type
  true = true : Prop
```
Turning off generalization allows type checking to succeed, because {lean}`b` remains in the types of {lean}`ifTrue` and {lean}`ifFalse`.
```lean
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match (generalizing := false) h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
In the generalized version, {name}`rfl` could have been used as the proof arguments as an alternative.
::::
:::::

## Custom Pattern Functions
%%%
tag := "match_pattern-functions"
%%%

```lean (show := false)
section
variable {n : Nat}
```

In patterns, defined constants with the {attr}`match_pattern` attribute are unfolded and normalized rather than rejected.
This allows a more convenient syntax to be used for many patterns.
In the standard library, {name}`Nat.add`, {name}`HAdd.hAdd`, {name}`Add.add`, and {name}`Neg.neg` all have this attribute, which allows patterns like {lean}`n + 1` instead of {lean}`Nat.succ n`.
Similarly, {name}`Unit` and {name}`Unit.unit` are definitions that set the respective {tech}[universe parameters] of {name}`PUnit` and {name}`PUnit.unit` to 0; the {attr}`match_pattern` attribute on {name}`Unit.unit` allows it to be used in patterns, where it expands to {lean}`PUnit.unit.{0}`.

:::syntax attr (title := "Attribute for Match Patterns")
The {attr}`match_pattern` attribute indicates that a definition should be unfolded, rather than rejected, in a pattern.
```grammar
match_pattern
```
:::

::::keepEnv
```lean (show := false)
section
variable {k : Nat}
```
:::example "Match Patterns Follow Reduction"
The following function can't be compiled:
```lean (error := true) (name := nonPat)
def nonzero (n : Nat) : Bool :=
  match n with
  | 0 => false
  | 1 + k => true
```
The error message on the pattern `1 + _` is:
```leanOutput nonPat
invalid patterns, `k` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching
  .(Nat.add 1 k)
```

This is because {name}`Nat.add` is defined by recursion on its second parameter, equivalently to:
```lean
def add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```

No {tech}[ι-reduction] is possible, because the value being matched is a variable, not a constructor.
{lean}`1 + k` gets stuck as {lean}`Nat.add 1 k`, which is not a valid pattern.

In the case of {lean}`k + 1`, that is, {lean}`Nat.add k (.succ .zero)`, the second pattern matches, so it reduces to {lean}`Nat.succ (Nat.add k .zero)`.
The second pattern now matches, yielding {lean}`Nat.succ k`, which is a valid pattern.
:::
````lean (show := false)
end
````

::::


```lean (show := false)
end
```


## Pattern Matching Functions
%%%
tag := "pattern-fun"
%%%

:::syntax term
Functions may be specified via pattern matching by writing a sequence of patterns after {keywordOf Lean.Parser.Term.fun}`fun`, each preceded by a vertical bar (`|`).
```grammar
fun
  $[| $pat,* => $term]*
```
This desugars to a function that immediately pattern-matches on its arguments.
:::

::::keepEnv
:::example "Pattern-Matching Functions"
{lean}`isZero` is defined using a pattern-matching function abstraction, while {lean}`isZero'` is defined using a pattern match expression:
```lean
def isZero : Nat → Bool :=
  fun
    | 0 => true
    | _ => false

def isZero' : Nat → Bool :=
  fun n =>
    match n with
    | 0 => true
    | _ => false
```
Because the former is syntactic sugar for the latter, they are definitionally equal:
```lean
example : isZero = isZero' := rfl
```
The desugaring is visible in the output of {keywordOf Lean.Parser.Command.print}`#print`:
```lean (name := isZero)
#print isZero
```
outputs
```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
while
```lean (name := isZero')
#print isZero'
```
outputs
```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
:::
::::

## Other Pattern Matching Operators

In addition to {keywordOf Lean.Parser.Term.match}`match` and {keywordOf termIfLet}`if let`, there are a few other operators that perform pattern matching.

:::syntax term
The {keywordOf Lean.«term_Matches_|»}`matches` operator returns {lean}`true` if the term on the left matches the pattern on the right.
```grammar
$e matches $e
```
:::

When branching on the result of {keywordOf Lean.«term_Matches_|»}`matches`, it's usually better to use {keywordOf termIfLet}`if let`, which can bind pattern variables in addition to checking whether a pattern matches.

```lean (show := false)
/--
info: match 4 with
| n.succ => true
| x => false : Bool
-/
#guard_msgs in
#check 4 matches (n + 1)
```

If there are no constructor patterns that could match a discriminant or sequence of discriminants, then the code in question is unreachable, as there must be a false assumption in the local context.
The {keywordOf Lean.Parser.Term.nomatch}`nomatch` expression is a match with zero cases that can have any type whatsoever, so long as there are no possible cases that could match the discriminants.

:::syntax term (title := "Caseless Pattern Matches")
```grammar
nomatch $e,*
```
:::

::::keepEnv
:::example "Inconsistent Indices"
There are no constructor patterns that can match both proofs in this example:
```lean
example (p1 : x = "Hello") (p2 : x = "world") : False :=
  nomatch p1, p2
```

This is because they separately refine the value of `x` to unequal strings.
Thus, the {keywordOf Lean.Parser.Term.nomatch}`nomatch` operator allows the example's body to prove {lean}`False` (or any other proposition or type).
:::
::::

When the expected type is a function type, {keywordOf Lean.Parser.Term.nofun}`nofun` is shorthand for a function that takes as many parameters as the type indicates in which the body is {keywordOf Lean.Parser.Term.nomatch}`nomatch` applied to all of the parameters.
:::syntax term (title := "Caseless Functions")
```grammar
nofun
```
:::

::::keepEnv
:::example "Impossible Functions"
Instead of introducing arguments for both equality proofs and then using both in a {keywordOf Lean.Parser.Term.nomatch}`nomatch`, it is possible to use {keywordOf Lean.Parser.Term.nofun}`nofun`.
```lean
example : x = "Hello" → x = "world" → False := nofun
```
:::
::::

## Elaborating Pattern Matching
%%%
tag := "pattern-match-elaboration"
%%%

:::planned 209
Specify the elaboration of pattern matching to {deftech}[auxiliary match functions].
:::

# Holes

A {deftech}_hole_ or {deftech}_placeholder term_ is a term that indicates the absence of instructions to the elaborator.{index}[placeholder term]{index subterm:="placeholder"}[term]
In terms, holes can be automatically filled when the surrounding context would only allow one type-correct term to be written where the hole is.
Otherwise, a hole is an error.
In patterns, holes represent universal patterns that can match anything.


:::syntax term (title := "Holes")
Holes are written with underscores.
```grammar
_
```
:::

::::keepEnv
:::example "Filling Holes with Unification"
The function {lean}`the` can be used similarly to {keywordOf Lean.Parser.Term.show}`show` or a {tech}[type ascription].
```lean
def the (α : Sort u) (x : α) : α := x
```
If the second parameter's type can be inferred, then the first parameter can be a hole.
Both of these commands are equivalent:
```lean
#check the String "Hello!"

#check the _ "Hello"
```
:::
::::


When writing proofs, it can be convenient to explicitly introduce unknown values.
This is done via {deftech}_synthetic holes_, which are never solved by unification and may occur in multiple positions.
They are primarily useful in tactic proofs, and are described in {ref "metavariables-in-proofs"}[the section on metavariables in proofs].

:::syntax term (title := "Synthetic Holes")
```grammar
?$x:ident
```
```grammar
?_
```
:::

# Type Ascription

{deftech}_Type ascriptions_ explicitly annotate terms with their types.
They are a way to provide Lean with the expected type for a term.
This type must be definitionally equal to the type that is expected based on the term's context.
Type ascriptions are useful for more than just documenting a program:
 * There may not be sufficient information in the program text to derive a type for a term. Ascriptions are one way to provide the type.
 * An inferred type may not be the one that was desired for a term.
 * The expected type of a term is used to drive the insertion of {tech}[coercions], and ascriptions are one way to control where coercions are inserted.

:::syntax term (title := "Postfix Type Ascriptions")
Type ascriptions must be surrounded by parentheses.
They indicate that the first term's type is the second term.
```grammar
($_ : $_)
```
:::


In cases where the term that requires a type ascription is long, such as a tactic proof or a {keywordOf Lean.Parser.Term.do}`do` block, the postfix type ascription with its mandatory parentheses can be difficult to read.
Additionally, for both proofs and {keywordOf Lean.Parser.Term.do}`do` blocks, the term's type is essential to its interpretation.
In these cases, the prefix versions can be easier to read.
:::syntax term (title := "Prefix Type Ascriptions")
```grammar
show $_ from $_
```
When the term in the body of {keywordOf Lean.Parser.Term.show}`show` is a proof, the keyword {keywordOf Lean.Parser.Term.show}`from` may be omitted.
```grammar
show $_ by $_
```
:::

:::example "Ascribing Statements to Proofs"
This example is unable to execute the tactic proof because the desired proposition is not known.
As part of running the earlier tactics, the proposition is automatically refined to be one that the tactics could prove.
However, their default cases fill it out incorrectly, leading to a proof that fails.
```lean (name := byBusted) (error := true)
example (n : Nat) := by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
```leanOutput byBusted
tactic 'rewrite' failed, equality or iff proof expected
  HEq 0 n'
n' : Nat
ih : HEq 0 n'
⊢ HEq 0 n'.succ
```

A prefix type ascription with {keywordOf Lean.Parser.Term.show}`show` can be used to provide the proposition being proved.
This can be useful in syntactic contexts where adding it as a local definition would be inconvenient.
```lean
example (n : Nat) := show 0 + n = n by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
:::

:::example "Ascribing Types to {keywordOf Lean.Parser.Term.do}`do` Blocks"
This example lacks sufficient type information to synthesize the {name}`Pure` instance.
```lean (name := doBusted) (error := true)
example := do
  return 5
```
```leanOutput doBusted
typeclass instance problem is stuck, it is often due to metavariables
  Pure ?m.75
```

A prefix type ascription with {keywordOf Lean.Parser.Term.show}`show`, together with a {tech}[hole], can be used to indicate the monad.
The {tech key:="default instance"}[default] {lean}`OfNat _ 5` instance provides enough type information to fill the hole with {lean}`Nat`.
```lean
example := show StateM String _ from do
  return 5
```
:::

# Quotation and Antiquotation

Quotation terms are described in the {ref "quotation"}[section on quotation].

# `do`-Notation

{keywordOf Lean.Parser.Term.do}`do`-notation is described {ref "do-notation"}[in the chapter on monads.]

# Proofs

The syntax for invoking tactics ({keywordOf Lean.Parser.Term.byTactic}`by`) is described in {ref "by"}[the section on proofs].
