/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.RecursiveDefs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option maxRecDepth 1500

#doc (Manual) "Definitions" =>
%%%
tag := "definitions"
%%%


The following commands in Lean are definition-like: {TODO}[Render commands as their name (a la tactic index)]
 * {keyword}`def`
 * {keyword}`abbrev`
 * {keyword}`example`
 * {keyword}`theorem`
 * {keyword}`opaque`

All of these commands cause Lean to {tech key:="elaborator"}[elaborate] a term based on a {tech}[signature].
With the exception of {keywordOf Lean.Parser.Command.example}`example`, which discards the result, the resulting expression in Lean's core language is saved for future use in the environment.
The {keywordOf Lean.Parser.Command.declaration}`instance` command is described in the {ref "instance-declarations"}[section on instance declarations].


# Modifiers
%%%
tag := "declaration-modifiers"
%%%

Declarations accept a consistent set of {deftech}_modifiers_, all of which are optional.
Modifiers change some aspect of the declaration's interpretation; for example, they can add documentation or change its scope.
The order of modifiers is fixed, but not every kind of declaration accepts every kind of modifier.

:::syntax declModifiers (open := false) (alias:=Lean.Parser.Command.declModifiers) (title := "Declaration Modifiers")
Modifiers consist of the following, in order, all of which are optional:
 1. a documentation comment,
 2. a list of {tech}[attributes],
 3. namespace control, specifying whether the resulting name is {tech}[private] or {tech}[protected],
 4. the {keyword}`noncomputable` keyword, which exempts a definition from compilation,
 5. the {keyword}`unsafe` keyword, and
 6. a recursion modifier {keyword}`partial` or {keyword}`nonrec`, which disable termination proofs or disallow recursion entirely.
```grammar
$[$_:docComment]?
$[$_:attributes]?
$[$_]?
$[noncomputable]?
$[unsafe]?
$[$_]?
```
:::

{deftech}_Documentation comments_ are used to provide in-source API documentation for the declaration that they modify.
Documentation comments are not, in fact comments: it is a syntax error to put a documentation comment in a position where it is not processed as documentation.
They also occur in positions where some kind of text is required, but string escaping would be onerous, such as the desired messages on the {keywordOf Lean.guardMsgsCmd}`#guard_msgs` command.

:::syntax docComment (open:=false) (title := "Documentation Comments")

Documentation comments are like ordinary block comments, but they begin with the sequence `/--` rather than `/-`; just like ordinary comments, they are terminated with `-/`.

```grammar
/--
...
-/
```
:::

Attributes are an extensible collection of modifiers that associate additional information with declarations.
They are described in a {ref "attributes"}[dedicated section].

If a declaration is marked {deftech key:="private"}[{keyword}`private`], then it is not accessible outside the module in which it is defined.
If it is {keyword}`protected`, then opening its namespace does not bring it into scope.

Functions marked {keyword}`noncomputable` are not compiled and cannot be executed.
Functions must be noncomputable if they use noncomputable reasoning principles such as the axiom of choice or excluded middle to produce data that is relevant to the answer that they return, or if they use features of Lean that are exempted from code generation for efficiency reasons, such as {tech}[recursors].
Noncomputable functions are very useful for specification and reasoning, even if they cannot be compiled and executed.

The {keyword}`unsafe` marker exempts a definition from kernel checking and enables it to access features that may undermine Lean's guarantees.
It should be used with great care, and only with a thorough understanding of Lean's internals.


# Headers and Signatures
%%%
tag := "signature-syntax"
%%%

The {deftech}[_header_] of a definition or declaration consists of the constant being declared or defined, if relevant, together with its signature.
The {deftech}_signature_ of a constant specifies how it can be used.
The information present in the signature is more than just the type, including information such as {tech key:="universe parameter"}[universe level parameters] and the default values of its optional parameters.
In Lean, signatures are written in a consistent format in different kinds of declarations.

## Declaration Names

Most headers begin with a {deftech}_declaration name_, which is followed by the signature proper: its parameters and the resulting type.
A declaration name is a name that may optionally include universe parameters.

:::syntax declId (open := false) (title := "Declaration Names")
Declaration names without universe parameters consist of an identifier:
```grammar
$_:ident
```

Declaration names with universe parameters consist of an identifier followed by a period and one or more universe parameter names in braces:
```grammar
$_.{$_, $_,*}
```
These universe parameter names are binding occurrences.
:::

Examples do not include declaration names, and names are optional for instance declarations.

## Parameters and Types
%%%
tag := "parameter-syntax"
%%%

After the name, if present, is the header's signature.
The signature specifies the declaration's parameters and type.

:::syntax declSig (open := false) (title := "Declaration Signatures")
A signature consists of zero or more parameters, followed by a colon and a type.

```grammar
$_* : $_
```
:::

:::syntax optDeclSig (open := false) (title := "Optional Signatures")
Signatures are often optional.
In these cases, parameters may be supplied even if the type is omitted.
```grammar
$_* $[: $_]?
```
:::


Parameters may have three forms:
 * An identifier, which names a parameter but does not provide a type.
   These parameters' types must be inferred during elaboration.
 * An underscore (`_`), which indicates a parameter that is not accessible by name in the local scope.
   These parameters' types must also inferred during elaboration.
 * A bracketed binder, which may specify every aspect of one or more parameters, including their names, their types, default values, and whether they are explicit, implicit, strictly implicit, or instance-implicit.

## Bracketed Parameter Bindings
%%%
tag := "bracketed-parameter-syntax"
%%%


Parameters other than identifiers or underscores are collectively referred to as {deftech}_bracketed binders_ because every syntactic form for specifying them has some kind of brackets, braces, or parentheses.
All bracketed binders specify the type of a parameter, and most include parameter names.
The name is optional for instance implicit parameters.
Using an underscore (`_`) instead of a parameter name indicates an anonymous parameter.


:::syntax bracketedBinder (open := false) (title := "Explicit Parameters")
Parenthesized parameters indicate explicit parameters.
If more than one identifier or underscore is provided, then all of them become parameters with the same type.
```grammar
($x $x* : $t)
```
:::

:::syntax bracketedBinder (title := "Optional and Automatic Parameters")
Parenthesized parameters with a `:=` assign default values to parameters.
Parameters with default values are called {deftech}_optional parameters_.
At a call site, if the parameter is not provided, then the provided term is used to fill it in.
Prior parameters in the signature are in scope for the default value, and their values at the call site are substituted into the default value term.

If a {ref "tactics"}[tactic script] is provided, then the tactics are executed at the call site to synthesize a parameter value; parameters that are filled in via tactics are called {deftech}_automatic parameters_.
```grammar
($x $x* : $t := $e)
```
:::

:::syntax bracketedBinder (title := "Implicit Parameters")
Parameters in curly braces indicate {tech}[implicit] parameters.
Unless provided by name at a call site, these parameters are expected to be synthesized via unification at call sites.
Implicit parameters are synthesized at all call sites.
```grammar
{$x $x* : $t}
```
:::

:::syntax bracketedBinder (title := "Strict Implicit Parameters")
Parameters in double curly braces indicate {tech}[strict implicit] parameters.
`⦃ … ⦄` and `{{ … }}` are equivalent.
Like implicit parameters, these parameters are expected to be synthesized via unification at call sites when they are not provided by name.
Strict implicit parameters are only synthesized at call sites when subsequent parameters in the signature are also provided.

```grammar
⦃$x $x* : $t⦄
```
```grammar
{{$x $x* : $t}}
```

:::

:::syntax bracketedBinder (title := "Instance Implicit Parameters")
Parameters in square brackets indicate {tech}[instance implicit] parameters, which are synthesized at call sites using {tech key:="synthesis"}[instance synthesis].
```grammar
[$[$x :]? $t]
```
:::

The parameters are always in scope in the signature's type, which occurs after the colon.
They are also in scope in the declaration's body, while names bound in the type itself are only in scope in the type.
Thus, parameter names are used twice:
 * As names in the declaration's function type, bound as part of a {tech key:="dependent"}[dependent function type].
 * As names in the declaration's body.
   In function definitions, they are bound by a {keywordOf Lean.Parser.Term.fun}`fun`.

:::example "Parameter Scope"
The signature of {lean}`add` contains one parameter, `n`.
Additionally, the signature's type is {lean}`(k : Nat) → Nat`, which is a function type that includes `k`.
The parameter `n` is in scope in the function's body, but `k` is not.

```lean
def add (n : Nat) : (k : Nat) → Nat
  | 0 => n
  | k' + 1 => 1 + add n k'
```

Like {lean}`add`, the signature of {lean}`mustBeEqual` contains one parameter, `n`.
It is in scope both in the type, where it occurs in a proposition, and in the body, where it occurs as part of the message.
```lean
def mustBeEqual (n : Nat) : (k : Nat) → n = k → String :=
  fun _ =>
    fun
    | rfl => s!"Equal - both are {n}!"

```
:::

The section on {ref "function-application"}[function application] describes the interpretation of {tech key:="optional parameter"}[optional], {tech key:="automatic parameter"}[automatic], {tech}[implicit], and {tech}[instance implicit] parameters in detail.

## Automatic Implicit Parameters
%%%
tag := "automatic-implicit-parameters"
%%%


By default, otherwise-unbound names that occur in signatures are converted into implicit parameters when possible
These parameters are called {deftech}_automatic implicit parameters_.
This is possible when they are not in the function position of an application and when there is sufficient information available in the signature to infer their type and any ordering constraints on them.
This process is iterated: if the inferred type for the freshly-inserted implicit parameter has dependencies that are not uniquely determined, then these dependencies are replaced with further implicit parameters.

Implicit parameters that don't correspond to names written in signatures are assigned names akin to those of {tech}[inaccessible] hypotheses in proofs, which cannot be referred to.
They show up in signatures with a trailing dagger (`'✝'`).
This prevents an arbitrary choice of name by Lean from becoming part of the API by being usable as a {tech}[named argument].

::::leanSection
```lean show:=false
variable {α : Type u} {β : Type v}
```
:::example "Automatic Implicit Parameters"

In this definition of {lean}`map`, {lean}`α` and {lean}`β` are not explicitly bound.
Rather than this being an error, they are converted into implicit parameters.
Because they must be types, but nothing constrains their universes, the universe parameters `u` and `v` are also inserted.
```lean
def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

The full signature of {lean}`map` is:
```signature
map.{u, v} {α : Type u} {β : Type v}
  (f : α → β) (xs : List α) :
  List β
```
:::
::::

::::example "No Automatic Implicit Parameters"

:::leanSection
```lean show:=false
universe u v
variable {α : Type u} {β : Type v}
```

In this definition, {lean}`α` and {lean}`β` are not explicitly bound.
Because {option}`autoImplicit` is disabled, this is an error:
:::

:::keepEnv
```lean (error := true) (name := noAuto)
set_option autoImplicit false

def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

```leanOutput noAuto
unknown identifier 'α'
```
```leanOutput noAuto
unknown identifier 'β'
```
:::


The full signature allows the definition to be accepted:
```lean (keep := false)
set_option autoImplicit false

def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

Universe parameters are inserted automatically for parameters without explicit type annotations.
The type parameters' universes can be inferred, and the appropriate universe parameters inserted, even when {option}`autoImplicit` is disabled:
```lean (keep := false)
set_option autoImplicit false

def map {α β} (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

::::



:::::example "Iterated Automatic Implicit Parameters"

:::leanSection
```lean (show := false)
variable (i : Fin n)
```
Given a number bounded by {lean}`n`, represented by the type `Fin n`, an {lean}`AtLeast i` is a natural number paired with a proof that it is at least as large as as `i`.
:::
```lean
structure AtLeast (i : Fin n) where
  val : Nat
  val_gt_i : val ≥ i.val
```

These numbers can be added:
```lean
def AtLeast.add (x y : AtLeast i) : AtLeast i :=
  AtLeast.mk (x.val + y.val) <| by
    cases x
    cases y
    dsimp only
    omega
```

::::paragraph
:::leanSection
```lean (show := false)
variable (i : Fin n)
```
The signature of {lean}`AtLeast.add` requires multiple rounds of automatic implicit parameter insertion.
First, {lean}`i` is inserted; but its type depends on the upper bound {lean}`n` of {lean}`Fin n`.
In the second round, {lean}`n` is inserted, using a machine-chosen name.
Because {lean}`n`'s type is {lean}`Nat`, which has no dependencies, the process terminates.
The final signature can be seen with {keywordOf Lean.Parser.Command.check}`#check`:
:::
```lean (name := checkAdd)
#check AtLeast.add
```
```leanOutput checkAdd
AtLeast.add {n✝ : Nat} {i : Fin n✝} (x y : AtLeast i) : AtLeast i
```
::::

:::::

Automatic implicit parameter insertion takes place after the insertion of parameters due to {tech}[section variables].
Parameters that correspond to section variables have the same name as the corresponding variable, even when they do not correspond to a name written directly in the signature, and disabling automatic implicit parameters has no effect the parameters that correspond to section variables.
However, when automatic implicit parameters are enabled, section variable declarations that contain otherwise-unbound variables receive additional section variables that follow the same rules as those for implicit parameters.

Automatic implicit parameters insertion is controlled by two options.
By default, automatic implicit parameter insertion is _relaxed_, which means that any unbound identifier may be a candidate for automatic insertion.
Setting the option {option}`relaxedAutoImplicit` to {lean}`false` disables relaxed mode and causes only identifiers that consist of a single character followed by zero or more digits to be considered for automatic insertion.

{optionDocs relaxedAutoImplicit}

{optionDocs autoImplicit}


::::example "Relaxed vs Non-Relaxed Automatic Implicit Parameters"

Misspelled identifiers or missing imports can end up as unwanted implicit parameters, as in this example:
```lean
inductive Answer where
  | yes
  | maybe
  | no
```
:::keepEnv
```lean  (name := asnwer) (error := true)
def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
The resulting error message states that the argument's type is not a constant, so dot notation cannot be used in the pattern:
```leanOutput asnwer
Invalid dotted identifier notation: The expected type of `.yes`
  Asnwer
is not of the form `C ...` or `... → C ...` where C is a constant
```
This is because the signature is:
```signature
select.{u_1, u_2}
  {α : Type u_1}
  {Asnwer : Sort u_2}
  (choices : α × α × α) :
  Asnwer → α
```
:::

Disabling relaxed automatic implicit parameters makes the error more clear, while still allowing the type to be inserted automatically:
:::keepEnv
```lean  (name := asnwer2) (error := true)
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput asnwer2
unknown identifier 'Asnwer'
```
:::

Correcting the error allows the definition to be accepted.
:::keepEnv
```lean
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
:::

Turning off automatic implicit parameters entirely leads to the definition being rejected:
:::keepEnv
```lean (error := true) (name := noauto)
set_option autoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput noauto
unknown identifier 'α'
```
:::
::::

# Definitions

Definitions add a new constant to the global environment as a name that stands for a term.
As part of the kernel's definitional equality, this new constant may be replaced via {tech key:="δ"}[δ-reduction] with the term that it stands for.
In the elaborator, this replacement is governed by the constant's {tech}[reducibility].
The new constant may be {tech key:="universe polymorphism"}[universe polymorphic], in which case occurrences may instantiate it with different universe level parameters.

Function definitions may be recursive.
To preserve the consistency of Lean's type theory as a logic, recursive functions must either be opaque to the kernel (e.g. by {ref "partial-functions"}[declaring them {keyword}`partial`]) or proven to terminate with one of the strategies described in {ref "recursive-definitions"}[the section on recursive definitions].

The headers and bodies of definitions are elaborated together.
If the header is incompletely specified (e.g. a parameter's type or the codomain is missing), then the body may provide sufficient information for the elaborator to reconstruct the missing parts.
However, {tech}[instance implicit] parameters must be specified in the header or as {tech}[section variables].

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.definition (title := "Definitions")
Definitions that use `:=` associate the term on the right-hand side with the constant's name.
The term is wrapped in a {keywordOf Lean.Parser.Term.fun}`fun` for each parameter, and the type is found by binding the parameters in a function type.
Definitions with {keyword}`def` are {tech}[semireducible].

```grammar
$_:declModifiers
def $_ $_ := $_
```

Definitions may use pattern matching.
These definitions are desugared to uses of {keywordOf Lean.Parser.Term.match}`match`.

```grammar
$_:declModifiers
def $_ $_
  $[| $_ => $_]*
```

Values of structure types, or functions that return them, may be defined by providing values for their fields, following {keyword}`where`:

```grammar
$_:declModifiers
def $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.abbrev (title := "Abbreviations")
Abbreviations are identical to definitions with {keyword}`def`, except they are {tech}[reducible].

```grammar
$_:declModifiers
abbrev $_ $_ := $_
```

```grammar
$_:declModifiers
abbrev $_ $_
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
abbrev $_ $_ where
  $_*
```
:::


{deftech}_Opaque constants_ are defined constants that are not subject to {tech key:="δ"}[δ-reduction] in the kernel.
They are useful for specifying the existence of some function.
Unlike {tech}[axioms], opaque declarations can only be used for types that are inhabited, so they do not risk introducing inconsistency.
Also unlike axioms, the inhabitant of the type is used in compiled code.
The {attr}`implemented_by` attribute can be used to instruct the compiler to emit a call to some other function as the compilation of an opaque constant.

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.opaque (title := "Opaque Constants")
Opaque definitions with right-hand sides are elaborated like other definitions.
This demonstrates that the type is inhabited; the inhabitant plays no further role.
```grammar
$_:declModifiers
opaque $_ $_ := $_
```

Opaque constants may also be specified without right-hand sides.
The elaborator fills in the right-hand side by synthesizing an instance of {name}`Inhabited`, or {name}`Nonempty` if that fails.
```grammar
$_:declModifiers
opaque $_ $_
```
:::

# Theorems

:::paragraph
Because {tech}[propositions] are types whose inhabitants count as proofs, {deftech}[theorems] and definitions are technically very similar.
However, because their use cases are quite different, they differ in many details:

* The theorem statement must be a proposition.
  The types of definitions may inhabit any {tech}[universe].
* A theorem's header (that is, the theorem statement) is completely elaborated before the body is elaborated.
  Section variables only become parameters to the theorem if they (or their dependents) are mentioned in the header.
  This prevents changes to a proof from unintentionally changing the the theorem statement.
* Theorems are {tech}[irreducible] by default.
  Because all proofs of the same proposition are {tech key:="definitional equality"}[definitionally equal], there few reasons to unfold a theorem.
:::

Theorems may be recursive, subject to the same conditions as {ref "recursive-definitions"}[recursive function definitions].
However, it is more common to use tactics such as {tactic}`induction` or {tactic}`fun_induction` instead.

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.theorem (title := "Theorems")
The syntax of theorems is like that of definitions, except the codomain (that is, the theorem statement) in the signature is mandatory.
```grammar
$_:declModifiers
theorem $_ $_ := $_
```

```grammar
$_:declModifiers
theorem $_ $_
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
theorem $_ $_ where
  $_*
```
:::



# Example Declarations

An {deftech}[example] is an anonymous definition that is elaborated and then discarded.
Examples are useful for incremental testing during development and to make it easier to understand a file.

:::syntax Lean.Parser.Command.declaration alias:=Lean.Parser.Command.example (title := "Examples")
```grammar
$_:declModifiers
example $_:optDeclSig := $_
```

```grammar
$_:declModifiers
example $_:optDeclSig
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
example $_:optDeclSig where
  $_*
```
:::



{include 0 Manual.RecursiveDefs}
