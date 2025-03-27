/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Language.Files
import Manual.Language.Namespaces
import Manual.Coercions


import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

#doc (Manual) "Source Files" =>

{include 0 Manual.Language.Files}


# Module Contents

As described {ref "module-structure"}[in the section on the syntax of files], a Lean module consists of a header followed by a sequence of commands.

## Commands and Declarations

After the header, every top-level phrase of a Lean module is a command.
Commands may add new types, define new constants, or query Lean for information.
Commands may even {ref "language-extension"}[change the syntax used to parse subsequent commands].

::: planned 100
 * Describe the various families of available commands (definition-like, `#eval`-like, etc).
 * Refer to specific chapters that describe major commands, such as `inductive`.
:::

### Definition-Like Commands

::: planned 101
 * Precise descriptions of these commands and their syntax
 * Comparison of each kind of definition-like command to the others
:::

The following commands in Lean are definition-like: {TODO}[Render commands as their name (a la tactic index)]
 * {syntaxKind}`def`
 * {syntaxKind}`abbrev`
 * {syntaxKind}`example`
 * {syntaxKind}`theorem`

All of these commands cause Lean to {tech key:="elaborator"}[elaborate] a term based on a signature.
With the exception of {syntaxKind}`example`, which discards the result, the resulting expression in Lean's core language is saved for future use in the environment.
The {keywordOf Lean.Parser.Command.declaration}`instance` command is described in the {ref "instance-declarations"}[section on instance declarations].

:::syntax Lean.Parser.Command.declaration (title := "Definitions with Modifiers")
```grammar
$_:declModifiers
$_:definition
```
:::

:::syntax Lean.Parser.Command.definition (title := "Definitions")
```grammar
def $_ $_ := $_
```

```grammar
def $_ $_
  $[| $_ => $_]*
```

```grammar
def $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.theorem (title := "Theorems")
```grammar
theorem $_ $_ := $_
```

```grammar
theorem $_ $_
  $[| $_ => $_]*
```

```grammar
theorem $_ $_ where
  $_*
```
:::

:::syntax Lean.Parser.Command.abbrev (title := "Abbreviations")
```grammar
abbrev $_ $_ := $_
```

```grammar
abbrev $_ $_
  $[| $_ => $_]*
```

```grammar
abbrev $_ $_ where
  $_*
```
:::



:::syntax Lean.Parser.Command.example (title := "Examples")
```grammar
example $_ $_ := $_
```

```grammar
example $_ $_
  $[| $_ => $_]*
```

```grammar
example $_ $_ where
  $_*
```
:::

{deftech}_Opaque constants_ are defined constants that cannot be reduced to their definition.

:::syntax Lean.Parser.Command.opaque (title := "Opaque Constants")
```grammar
opaque $_ $_
```
:::

:::syntax Lean.Parser.Command.axiom (title := "Axioms")
```grammar
axiom $_ $_
```
:::


### Modifiers
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

### Headers and Signatures
%%%
tag := "signature-syntax"
%%%

The {deftech}[_header_] of a definition or declaration consists of the constant being declared or defined, if relevant, together with its signature.
The {deftech}_signature_ of a constant specifies how it can be used.
The information present in the signature is more than just the type, including information such as {tech key:="universe parameter"}[universe level parameters] and the default values of its optional parameters.
In Lean, signatures are written in a consistent format in different kinds of declarations.

#### Declaration Names

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

#### Parameters and Types
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

Parameters may have three forms:
 * An identifier, which names a parameter but does not provide a type.
   These parameters' types must be inferred during elaboration.
 * An underscore (`_`), which indicates a parameter that is not accessible by name in the local scope.
   These parameters' types must also inferred during elaboration.
 * A bracketed binder, which may specify every aspect of one or more parameters, including their names, their types, default values, and whether they are explicit, implicit, strictly implicit, or instance-implicit.

#### Bracketed Parameter Bindings
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
  | k' + 1 => add n k'
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

#### Automatic Implicit Parameters
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
````lean (show := false)
variable (i : Fin n)
````
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
````lean (show := false)
variable (i : Fin n)
````
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
invalid dotted identifier notation, expected type is not of the form (... → C ...) where C is a constant
  Asnwer
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
````leanOutput noauto
unknown identifier 'α'
````
:::
::::

{include 2 Manual.Language.Namespaces}


## Section Scopes
%%%
tag := "scopes"
%%%

Many commands have an effect for the current {deftech}[_section scope_] (sometimes just called "scope" when clear).
Every Lean module has a section scope.
Nested scopes are created via the {keywordOf Lean.Parser.Command.namespace}`namespace` and {keywordOf Lean.Parser.Command.section}`section` commands, as well as the {keywordOf Lean.Parser.Command.in}`in` command combinator.

The following data are tracked in section scopes:

: The Current Namespace

  The {deftech}_current namespace_ is the namespace into which new declarations will be defined.
  Additionally, {tech (key:="resolve")}[name resolution] includes all prefixes of the current namespace in the scope for global names.

: Opened Namespaces

  When a namespace is {deftech}_opened_, its names become available without an explicit prefix in the current scope.
  Additionally, scoped attributes and {ref "syntax-rules"}[scoped syntax extensions] in namespaces that have been opened are active in the current section scope.

: Options

  Compiler options are reverted to their original values at the end of the scope in which they were modified.

: Section Variables

  {tech}[Section variables] are names (or {tech}[instance implicit] parameters) that are automatically added as parameters to definitions.
  They are also added as universally-quantified assumptions to theorems when they occur in the theorem's statement.


### Controlling Section Scopes
%%%
tag := "scope-commands"
%%%

The {keywordOf Lean.Parser.Command.section}`section` command creates a new section scope, but does not modify the current namespace, opened namespaces, or section variables.
Changes made to the section scope are reverted when the section ends.
Sections may optionally be named; the {keywordOf Lean.Parser.Command.end}`end` command that closes a named section must use the same name.
If section names have multiple components (that is, if they contain `.`-separated names), then multiple nested sections are introduced.
Section names have no other effect, and are a readability aid.

:::syntax command (title := "Sections")
The {keywordOf Lean.Parser.Command.section}`section` command creates a section scope that lasts either until an `end` command or the end of the file.
```grammar
section $[$id:ident]?
```
:::

:::example "Named Section"

The name {name Greetings.english}`english` is defined in the `Greetings` namespace.

```lean
def Greetings.english := "Hello"
```

Outside its namespace, it cannot be evaluated.

```lean (error := true) (name := english1)
#eval english
```
```leanOutput english1
unknown identifier 'english'
```

Opening a section allows modifications to the global scope to be contained.
This section is named `Greetings`.
```lean
section Greetings
```

Even though the section name matches the definition's namespace, the name is not in scope because section names are purely for readability and ease of refactoring.

```lean (error := true)  (name := english2)
#eval english
```
```leanOutput english2
unknown identifier 'english'
```

Opening the namespace `Greetings` brings {name}`Greetings.english` as {name Greetings.english}`english`:


```lean  (name := english3)
open Greetings

#eval english
```
```leanOutput english3
"Hello"
```

The section's name must be used to close it.

```lean (error := true) (name := english4) (keep := false)
end
```
```leanOutput english4
invalid 'end', name is missing (expected Greetings)
```

```lean
end Greetings
```

When the section is closed, the effects of the {keywordOf Lean.Parser.Command.open}`open` command are reverted.
```lean (error := true)  (name := english5)
#eval english
```
```leanOutput english5
unknown identifier 'english'
```
:::

The {keywordOf Lean.Parser.Command.namespace}`namespace` command creates a new section scope.
Within this section scope, the current namespace is the name provided in the command, interpreted relative to the current namespace in the surrounding section scope.
Like sections, changes made to the section scope are reverted when the namespace's scope ends.

To close a namespace, the {keywordOf Lean.Parser.Command.end}`end` command requires a suffix of the current namespace, which is removed.
All section scopes introduced by the {keywordOf Lean.Parser.Command.namespace}`namespace` command that introduced part of that suffix are closed.

:::syntax command (title := "Namespace Declarations")
The `namespace` command modifies the current namespace by appending the provided identifier.

creates a section scope that lasts either until an {keywordOf Lean.Parser.Command.end}`end` command or the end of the file.
```grammar
namespace $id:ident
```
:::


:::syntax command (title := "Section and Namespace Terminators")
Without an identifier, {keywordOf Lean.Parser.Command.end}`end` closes the most recently opened section, which must be anonymous.
```grammar
end
```

With an identifier, it closes the most recently opened section section or namespace.
If it is a section, the identifier be a suffix of the concatenated names of the sections opened since the most recent {keywordOf Lean.Parser.Command.namespace}`namespace` command.
If it is a namespace, then the identifier must be a suffix of the current namespace's extensions since the most recent {keywordOf Lean.Parser.Command.section}`section` that is still open; afterwards, the current namespace will have had this suffix removed.
```grammar
end $id:ident
```
:::

The {keywordOf Lean.Parser.Command.mutual}`end` that closes a {keywordOf Lean.Parser.Command.mutual}`mutual` block is part of the syntax of {keywordOf Lean.Parser.Command.mutual}`mutual`, rather than the {keywordOf Lean.Parser.Command.end}`end` command.

:::example "Nesting Namespaces and Sections"
Namespaces and sections may be nested.
A single {keywordOf Lean.Parser.Command.end}`end` command may close one or more namespaces or one or more sections, but not a mix of the two.

After setting the current namespace to `A.B.C` with two separate commands, `B.C` may be removed with a single {keywordOf Lean.Parser.Command.end}`end`:
```lean
namespace A.B
namespace C
end B.C
```
At this point, the current namespace is `A`.

Next, an anonymous section and the namespace `D.E` are opened:
```lean
section
namespace D.E
```
At this point, the current namespace is `A.D.E`.
An {keywordOf Lean.Parser.Command.end}`end` command cannot close all three due to the intervening section:
```lean (error := true) (name := endADE) (keep := false)
end A.D.E
```
```leanOutput endADE
invalid 'end', name mismatch (expected «».D.E)
```
Instead, namespaces and sections must be ended separately.
```lean
end D.E
end
end A
```
:::

Rather than opening a section for a single command, the {keywordOf Lean.Parser.Command.in}`in` combinator can be used to create single-command section scope.
The {keywordOf Lean.Parser.Command.in}`in` combinator is right-associative, allowing multiple scope modifications to be stacked.

:::syntax command (title := "Local Section Scopes")
The `in` command combinator introduces a section scope for a single command.
```grammar
$c:command in
$c:command
```
:::

:::example "Using {keywordOf Lean.Parser.Command.in}`in` for Local Scopes"
The contents of a namespace can be made available for a single command using {keywordOf Lean.Parser.Command.in}`in`.
```lean
def Dessert.cupcake := "delicious"

open Dessert in
#eval cupcake
```

After the single command, the effects of {keywordOf Lean.Parser.Command.open}`open` are reverted.

```lean (error := true) (name := noCake)
#eval cupcake
```
```leanOutput noCake
unknown identifier 'cupcake'
```
:::

### Section Variables
%%%
tag := "section-variables"
%%%

{deftech}_Section variables_ are parameters that are automatically added to declarations that mention them.
This occurs whether or not the option {option}`autoImplicit` is {lean}`true`.
Section variables may be implicit, strict implicit, or explicit; instance implicit section variables are treated specially.

When the name of a section variable is encountered in a non-theorem declaration, it is added as a parameter.
Any instance implicit section variables that mention the variable are also added.
If any of the variables that were added depend on other variables, then those variables are added as well; this process is iterated until no more dependencies remain.
All section variables are added in the order in which they are declared, before all other parameters.
Section variables are added only when they occur in the _statement_ of a theorem.
Otherwise, modifying the proof of a theorem could change its statement if the proof term made use of a section variable.

Variables are declared using the {keywordOf Lean.Parser.Command.variable}`variable` command.


:::syntax command (title := "Variable Declarations")
```grammar
variable $b:bracketedBinder $b:bracketedBinder*
```
:::

The bracketed binders allowed after `variable` match the {ref "bracketed-parameter-syntax"}[syntax used in definition headers].

:::example "Section Variables"
In this section, automatic implicit parameters are disabled, but a number of section variables are defined.

```lean
section
set_option autoImplicit false
universe u
variable {α : Type u} (xs : List α) [Zero α] [Add α]
```

Because automatic implicit parameters are disabled, the following definition fails:
```lean (error := true) (name := secvars) (keep := false)
def addAll (lst : List β) : β :=
  lst.foldr (init := 0) (· + ·)
```
```leanOutput secvars
unknown identifier 'β'
```

On the other hand, not even {lean}`xs` needs to be written directly in the definition:

```lean
def addAll :=
  xs.foldr (init := 0) (· + ·)
```

:::

To add a section variable to a theorem even if it is not explicitly mentioned in the statement, mark the variable with the {keywordOf Lean.Parser.Command.include}`include` command.
All variables marked for inclusion are added to all theorems.
The {keywordOf Lean.Parser.Command.omit}`omit` command removes the inclusion mark from a variable; it's typically a good idea to use it with {keywordOf Lean.Parser.Command.in}`in`.


```lean (show := false)
section
variable {p : Nat → Prop}
variable (pFifteen : p 15)
```
:::::example "Included and Omitted Section Variables"

This section's variables include a predicate as well as everything needed to prove that it holds universally, along with a useless extra assumption.

```lean
section
variable {p : Nat → Prop}
variable (pZero : p 0) (pStep : ∀ n, p n → p (n + 1))
variable (pFifteen : p 15)
```

However, only {lean}`p` is added to this theorem's assumptions, so it cannot be proved.
```lean (error := true) (keep := false)
theorem p_all : ∀ n, p n := by
  intro n
  induction n
```

The {keywordOf Lean.Parser.Command.include}`include` command causes the additional assumptions to be added unconditionally:
```lean (keep := false) (name := lint)
include pZero pStep pFifteen

theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```
Because the spurious assumption {lean}`pFifteen` was inserted, Lean issues a warning:
```leanOutput lint
automatically included section variable(s) unused in theorem 'p_all':
  pFifteen
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit pFifteen in theorem ...
note: this linter can be disabled with `set_option linter.unusedSectionVars false`
```

This can be avoided by using {keywordOf Lean.Parser.Command.omit}`omit`to remove {lean}`pFifteen`:
```lean (keep := false)
include pZero pStep pFifteen

omit pFifteen in
theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```

```lean
end
```

:::::
```lean (show := false)
end
```


# Axioms
%%%
tag := "axioms"
%%%

:::planned 78
Describe {deftech}_axioms_ in detail
:::

# Attributes
%%%
tag := "attributes"
%%%

{deftech}_Attributes_ are an extensible set of compile-time annotations on declarations.
They can be added as a {ref "declaration-modifiers"}[declaration modifier] or using the {keywordOf Lean.Parser.Command.attribute}`attribute` command.

Attributes can associate information with declarations in compile-time tables (including {tech}[custom simp sets], {tech}[macros], and {tech}[instances]), impose additional requirements on definitions (e.g. rejecting them if their type is not a type class), or generate additional code.
As with {tech}[macros] and custom {tech}[elaborators] for terms, commands, and tactics, the {tech}[syntax category] `attr` of attributes is designed to be extended, and there is a table that maps each extension to a compile-time program that interprets it.

Attributes are applied as {deftech}_attribute instances_ that pair a scope indicator with an attribute.
These may occur either in attributes as declaration modifiers or the stand-alone {keywordOf Lean.Parser.Command.attribute}`attribute` command.

:::syntax Lean.Parser.Term.attrInstance (title := "Attribute Instances")
```grammar
$_:attrKind $_:attr
```

An `attrKind` is the optional {ref "scoped-attributes"}[attribute scope] keywords {keyword}`local` or {keyword}`scoped`.
These control the visibility of the attribute's effects.
The attribute itself is anything from the extensible {tech}[syntax category] `attr`.
:::

The attribute system is very powerful: attributes can associate arbitrary information with declarations and generate any number of helpers.
This imposes some design trade-offs: storing this information takes space, and retrieving it takes time.
As a result, some attributes can only be applied to a declaration in the module where the declaration is defined.
This allows lookups to be much faster in large projects, because they don't need to examine data for all modules.
Each attribute determines how to store its own metadata and what the appropriate tradeoff between flexibility and performance is for a given use case.

## Attributes as Modifiers

Attributes can be added to declarations as a {ref "declaration-modifiers"}[declaration modifier].
They are placed between the documentation comment and the visibility modifiers.

:::syntax Lean.Parser.Term.attributes (open := false) (title := "Attributes")
```grammar
@[$_:attrInstance,*]
```
:::

## The {keyword}`attribute` Command

The {keywordOf Lean.Parser.Command.attribute}`attribute` command can be used to modify a declaration's attributes.
Some example uses include:
 * registering a pre-existing declaration as an {tech}[instance] in the local scope by adding {attr}`instance`,
 * marking a pre-existing theorem as a simp lemma or an extensionality lemma, using {attr}`simp` or {attr}`ext`, and
 * temporarily removing a simp lemma from the default {tech}[simp set].

:::syntax command (title := "Attribute Modification")
The {keywordOf Lean.Parser.Command.attribute}`attribute` command adds or removes attributes from an existing declaration.
The identifier is the name whose attributes are being modified.
```grammar
attribute [$_,*] $_
```
:::

In addition to attribute instances that add an attribute to an existing declaration, some attributes can be removed; this is called {deftech}_erasing_ the attribute.
Attributes can be erased by preceding their name with `-`.
Not all attributes support erasure, however.

:::syntax Lean.Parser.Command.eraseAttr (title := "Erasing Attributes")
Attributes are erased by preceding their name with a `-`.

```grammar
-$_:ident
```
:::


## Scoped Attributes
%%%
tag := "scoped-attributes"
%%%

Many attributes can be applied in a particular scope.
This determines whether the attribute's effect is visible only in the current section scope, in namespaces that open the current namespace, or everywhere.
These scope indications are also used to control {ref "syntax-rules"}[syntax extensions] and {ref "instance-attribute"}[type class instances].
Each attribute is responsible for defining precisely what these terms mean for its particular effect.

:::syntax attrKind (open := false) (title := "Attribute Scopes") (alias := Lean.Parser.Term.attrKind)
Globally-scoped declarations (the default) are in effect whenever the {tech}[module] in which they're established is transitively imported.
They are indicated by the absence of another scope modifier.
```grammar
```

Locally-scoped declarations are in effect only for the extent of the {tech}[section scope] in which they are established.
```grammar
local
```

Scoped declarations are in effect whenever the {tech key:="current namespace"}[namespace] in which they are established is opened.
```grammar
scoped
```
:::

# Dynamic Typing
%%%
draft := true
%%%

{docstring TypeName}

{docstring Dynamic}

{docstring Dynamic.mk (allowMissing := true)}

{docstring Dynamic.get?}

{include 0 Manual.Coercions}
