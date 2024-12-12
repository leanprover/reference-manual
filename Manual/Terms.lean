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

#doc (Manual) "Terms" =>
%%%
tag := "terms"
%%%

::: planned 66
This chapter will describe Lean's term language, including the following features:
 * Name resolution, including variable occurrences, `open` declarations and terms
 * Function application, including implicit, instance, and named arguments
 * Leading `.`-notation and accessor notation
 * `fun`, with and without pattern matching
 * Literals (some via cross-references to the appropriate types, e.g. {name}`String`)
 * Conditionals and their relationship to {name}`Decidable`
 * Pattern matching, including `match`, `let`, `if let`, `matches`, `nomatch`, `nofun`
 * Do-notation, including `let mut`, `for`, `while`, `repeat`, `break`, `return`
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

As terms, an identifier is a reference to a name.
The mapping from identifiers to names is not trivial: at any point in a {tech}[module], some number of {tech}[namespaces] will be open, there may be {tech}[section variables], and there may be local bindings.
Furthermore, identifiers may contain multiple dot-separated atomic identifiers; the dot both separates namespaces from their contents and variables from fields or functions that use {tech}[accessor notation].
An identifier `A.B.C.D.e.f` could refer to any of the following:

 * A name `f` in the namespace `A.B.C.D.e` (for instance, a function defined in `e`'s {keywordOf Lean.Parser.Command.declaration}`where` block).
 * An application of `T.f` to `A.B.C.D.e` if `A.B.C.D.e` has type `T`
 * A projection of field `f` from a structure named `A.B.C.D.e`
 * A series of field projections `B.C.D.e` from structure value `A`, followed by an application of `f` using accessor notation
 * If namespace `Q` is opened, it could be a reference to any of the above with a `Q` prefix, such as a name `f` in the namespace `Q.A.B.C.D.e`

This list is not exhaustive.
Given an identifier, the elaborator must discover which name or names an identifier refers to, and whether any of the trailing components are fields or accessors.
This is called {deftech}_resolving_ the name.
In addition, some declarations in the global environment are lazily created the first time they are referenced.
Resolving an identifier in a way that both creates one of these declarations and results in a reference to it is called {deftech}_realizing_ the name.
The rules for resolving and realizing a name are the same, so even though this section refers only to resolving names, it applies to both.

Name resolution is affected by the following:
 * {tech}[Preresolved names] attached to the identifier
 * The {tech}[macro scopes] attached to the identifier
 * The local bindings in scope, including auxiliary definitions created as part of the elaboration of {keywordOf Lean.Parser.Term.letrec}`let rec`.
 * Aliases created with {keywordOf Lean.Parser.Command.export}`export` in modules transitively imported by the current module
 * The current {tech}[section scope], in particular the current namespace, opened namespaces, and section variables


Any prefix of an identifier can resolve to a set of names.
The suffix that was not included in the resolution process is then treated as field projections or accessor notation.
Resolutions of longer prefixes take precedence over resolutions of shorter prefixes.
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

## Accessor Notation

:::TODO
Write me!
:::

## Leading `.`

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

# Function Application

Ordinarily, function application is written using juxtaposition: the argument is placed after the function, with at least one space between them.
In Lean's type theory, all functions take exactly one argument and produce exactly one value.
All function applications combine a single function with a single argument.
Multiple arguments are represented via currying.

The high-level term language treats a function together with one or more arguments as a single unit, and supports additional features such as implicit, optional, and by-name arguments along with ordinary positional arguments.
The elaborator converts these to the simpler model of the core type theory.

:::freeSyntax term
A function application consists of a term followed by one or more arguments, or by zero or more arguments and a final ellipsis.
```grammar
$e:term $e:argument+
***************
$e:term $e:argument* ".."
```
:::

{TODO}[Annotate with syntax kinds for incoming hyperlinks during traversal pass]
:::freeSyntax Lean.Parser.Term.argument (title := "Arguments")
Function arguments are either terms, named arguments, or ellipses.
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
 * If the parameter is {tech}[strictly implicit] and there are any named or positional arguments that have not yet been selected, a fresh metavariable is created with the parameter's type and selected.
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
 3. If there is an expected type, it is unified with the inferred type; however, errors resulting from this unification are discarded. If the expected and inferred types can be equal, unification can solve leftover implicit argument metavariables. If they can't be equal, an error is not thrown because a surrounding elaborator may be able to insert {tech}[coercions] or {tech}[monad lifts].


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


# Functions

* `fun` (move the content here?)

# Literals

 * Strings (xref)
 * Numbers (Nat, negative, scientific, floats)
 * Lists
 * Arrays

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


# Conditionals
%%%
tag := "if-then-else"
%%%

* xref to `if` in `do` and as a tactic
* `if let`

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

:::syntax term (title := "Pattern Matching Conditionals")
```grammar
if let $p := $e then
  $e
else
  $e
```
:::


:::TODO

Should we document bif?

:::

# Pattern Matching

* `match`, with and without name
* Simultaneous matching vs tuple matching
* Dependent matching and inaccessible patterns
* Specialization of terms from context
* xref `if let`, `fun`

{deftech}_Pattern matching_ is a way to recognize and destructure values using a syntax of {deftech}_patterns_ that are a subset of the terms.
A pattern that recognizes and destructures a value is similar to the syntax that would be used to construct the value.
One or more {deftech}_match discriminants_ are simultaneously compared to a series of {deftech}_match alternatives_.
Discriminants may be named.
Each alternative contains one or more comma-separated sequences of patterns; all pattern sequences must contain the same number of patterns as there are discriminants.
When a pattern sequence matches all of the discriminants, the term following the corresponding {keywordOf Lean.Parser.Term.match}`=>` is evaluated in an environment extended with values for each {tech}[pattern variable] as well as an equality hypothesis for each named discriminant.
This term is called the {deftech}_right-hand side_ of the match alternative.

:::syntax term (title := "Pattern Matching")
```grammar
match $[(generalizing := $e)]? $[(motive := $e)]? $[$d:matchDiscr],* with
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
  They can be used in positions where the pattern's typing would otherwise require a more specific {tech}[inaccessible term], while variables cannot be used in these positions.

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
  Similarly, {TODO}[xref] scientific literals are interpreted via the corresponding {name}`OfScientific` instance.
  While {lean}`Float` has such an instance, {lean}`Float`s cannot be used as patterns because the instance relies on an opaque function that can't be reduced to a valid pattern.

: Structure Instances

  {tech}[Structure instances] may be used as patterns.
  They are interpreted as the corresponding structure constructor.

: Quoted names

  Quoted names, such as {lean}`` `x `` and {lean}``` ``plus ```, match the corresponding {name}`Lean.Name` value.

: Macros

  Macros in patterns are expanded.
  They are patterns if the resulting expansions are patterns.

: Inaccessible Terms

  {deftech}[Inaccessible terms] are terms that are forced to have a particular value by later typing constraints.
  Any term may be used as an inaccessible term.
  Inaccessible terms are written with a preceding period (`.`).

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


# Holes

A {deftech}_hole_ or {deftech}_placeholder term_ is a term that indicates the absence of instructions to the elaborator.{index}[placeholder term]{index subterm:="placeholder"}[term]
In terms, holes can be automatically filled when the surrounding context would only allow one type-correct term to be written where the hole is.
Otherwise, a hole is an error.
In patterns, holes represent universal patterns that can match anything.

::::keepEnv
:::example "Filling Holes with Unification"
The function {lean}`the` can be used similarly to {keywordOf Lean.Parser.Term.show}`show` or a type ascription.
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

:::syntax term (title := "Holes")
Holes are written with underscores.
```grammar
_
```
:::

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

Type ascriptions are a way to provide Lean with the expected type for a term.
This type must be definitionally equal to the type that is expected based on the term's context.
Type ascriptions are useful for more than just documenting a program:
 * There may not be sufficient information in the program text to derive a type for a term. Ascriptions are one way to provide the type.
 * An inferred type may not be the one that was desired for a term.
 * The expected type of a term is used to drive the insertion of {tech}[coercions], and ascriptions are one way to control where coercions are inserted.

:::syntax term
Type ascriptions must be surrounded by parentheses.
They indicate that the first term's type is the second term.
```grammar
($_ : $_)
```
:::

:::syntax term
```grammar
show $_ from $_
```
```grammar
show $_ by $_
```

:::

# Quotation and Antiquotation

Quotation terms are described in the {ref "quotation"}[section on quotation].

# Proofs

The syntax for invoking tactics ({keywordOf Lean.Parser.Term.byTactic}`by`) is described in {ref "by"}[the section on proofs].
