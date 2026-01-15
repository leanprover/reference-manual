/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Source Files and Modules" =>
%%%
tag := "files"
htmlSplit := .never
%%%

The smallest unit of compilation in Lean is a single {deftech}[source file].
Source files may import other source files based on their file names.
In other words, the names and folder structures of files are significant in Lean code.

Each source file has an {deftech}_import name_ that is derived from a combination of its filename and the way in which Lean was invoked: Lean has set of a _root directories_ in which it expects to find code, and the source file's import name is the names of the directories from the root to the filename, with dots (`.`) interspersed and `.lean` removed.
For example, if Lean is invoked with `Projects/MyLib/src` as its root, the file `Projects/MyLib/src/Literature/Novel/SciFi.lean` could be imported as `Literature.Novel.SciFi`.

::: TODO
Describe case sensitivity/preservation for filenames here
:::

# Encoding and Representation
%%%
tag := "module-encoding"
%%%

Lean {deftech}[source files] are Unicode text files encoded in UTF-8. {TODO}[Figure out the status of BOM and Lean]
Lines may end either with newline characters (`"\n"`, Unicode `'LINE FEED (LF)' (U+000A)`) or with a form feed and newline sequence (`"\r\n"`, Unicode `'CARRIAGE RETURN (CR)' (U+000D)` followed by `'LINE FEED (LF)' (U+000A)`).
However, Lean normalizes line endings when parsing or comparing files, so all files are compared as if all their line endings are `"\n"`.
::: TODO
Marginal note: this is to make cached files and `#guard_msgs` and the like work even when git changes line endings. Also keeps offsets stored in parsed syntax objects consistent.
:::

# Concrete Syntax
%%%
tag := "module-syntax"
%%%


Lean's concrete syntax is {ref "language-extension"}[extensible].
In a language like Lean, it's not possible to completely describe the syntax once and for all, because libraries may define syntax in addition to new constants or {tech}[inductive types].
Rather than completely describing the language here, the overall framework is described, while the syntax of each language construct is documented in the section to which it belongs.

## Whitespace
%%%
tag := "whitespace"
%%%

Tokens in Lean may be separated by any number of {deftech}[_whitespace_] character sequences.
Whitespace may be a space (`" "`, Unicode `'SPACE (SP)' (U+0020)`), a valid newline sequence, or a comment. {TODO}[xref]
Neither tab characters nor carriage returns not followed by newlines are valid whitespace sequences.

## Comments
%%%
tag := "comments"
%%%


Comments are stretches of the file that, despite not being whitespace, are treated as such.
Lean has two syntaxes for comments:

: Line comments

  A `--` that does not occur as part of a token begins a _line comment_. All characters from the initial `-` to the newline are treated as whitespace.{index (subterm := "line")}[comment]

: Block comments

  A `/-` that does not occur as part of a token and is not immediately followed by a `-` character begins a _block comment_.{index (subterm := "block")}[comment]
  The block comment continues until a terminating `-/` is found.
  Block comments may be nested; a `-/` only terminates the comment if prior nested block comment openers `/-` have been terminated by a matching `-/`.

`/--` and `/-!` begin {deftech}_documentation_ {TODO}[xref] rather than comments, which are also terminated with `-/` and may contain nested block comments.
Even though documentation resembles comments, they are their own syntactic category; their valid placement is determined by Lean's grammar.



## Keywords and Identifiers
%%%
tag := "keywords-and-identifiers"
%%%


An {tech}[identifier] consists of one or more identifier components, separated by `'.'`.{index}[identifier]

{deftech}[Identifier components] consist of a letter or letter-like character or an underscore (`'_'`), followed by zero or more identifier continuation characters.
Letters are English letters, upper- or lowercase, and the letter-like characters include a range of non-English alphabetic scripts, including the Greek script which is widely used in Lean, the Coptic script, the members of the Unicode letter-like symbol block, which contains a number of double-struck characters (including `ℕ` and `ℤ`) and abbreviations, the Latin-1 supplemental letters (with the exception of `×` and `÷`), and the Latin Extended-A block.
Identifier continuation characters consist of letters, letter-like characters, underscores (`'_'`), exclamation marks (`!`), question marks (`?`), subscripts, and single quotes (`'`).
As an exception, underscore alone is not a valid identifier.

```lean -show
def validIdentifier (str : String) : IO String :=
  Lean.Parser.identFn.test str

/-- info: "Success! Final stack:\n  `ℕ\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"?\"" -/
#check_msgs in
#eval validIdentifier "?"

/-- info: "Success! Final stack:\n  `ℕ?\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ?"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"_\"" -/
#check_msgs in
#eval validIdentifier "_"

/-- info: "Success! Final stack:\n  `_3\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_3"

/-- info: "Success! Final stack:\n  `_.a\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_.a"

/-- info: "Success! Final stack:\n  `αποδεικνύοντας\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "αποδεικνύοντας"

/-- info: "Success! Final stack:\n  `κύκ\nRemaining:\n\"λος\"" -/
#check_msgs in
#eval validIdentifier "κύκλος"

/-- info: "Success! Final stack:\n  `øvelse\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "øvelse"

/-- info: "Success! Final stack:\n  `Übersetzung\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "Übersetzung"

/- Here's some things that probably should be identifiers but aren't at the time of writing -/

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"переклад\""
-/
#check_msgs in
#eval validIdentifier "переклад"

/-- info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"汉语\"" -/
#check_msgs in
#eval validIdentifier "汉语"


```

Identifiers components may also be surrounded by double {deftech}[guillemets] (`'«'` and `'»'`).
Such identifier components may contain any character at all aside from `'»'`, even `'«'`, `'.'`, and newlines.
The guillemets are not part of the resulting identifier component, so `«x»` and `x` denote the same identifier.
`«Nat.add»`, on the other hand, is an identifier with a single component, while `Nat.add` has two.




```lean -show
/-- info: "Success! Final stack:\n  `«\n  »\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«\n»"

/-- info: "Success! Final stack:\n  `««one line\n  and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "««one line\nand another»"

/-- info: "Success! Final stack:\n  `«one line\x00and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x00and another»"

/-- info: "Success! Final stack:\n  `«one line\x0band another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x0Band another»"
```

Some potential identifier components may be reserved keywords.
The specific set of reserved keywords depends on the set of active syntax extensions, which may depend on the set of imported files and the currently-opened {TODO}[xref/deftech for namespace] namespaces; it is impossible to enumerate for Lean as a whole.
These keywords must also be quoted with guillemets to be used as identifier components in most syntactic contexts.
Contexts in which keywords may be used as identifiers without guillemets, such as constructor names in inductive types, are {deftech}_raw identifier_ contexts.{index (subterm:="raw")}[identifier]

Identifiers that contain one or more `'.'` characters, and thus consist of more than one identifier component, are called {deftech}[hierarchical identifiers].
Hierarchical identifiers are used to represent both import names and names in a namespace.

# Structure
%%%
tag := "module-structure"
%%%


:::syntax Lean.Parser.Module.module -open (title := "Modules")
```grammar
$hdr:header $cmd:command*
```

A source file consists of a {deftech}_file header_ followed by a sequence of {deftech}_commands_.
:::

If a source file's header begins with {keywordOf Lean.Parser.Module.header}`module`, then it is referred to as a {tech}_module_.
Modules provide greater control over what information is exposed to clients.
Modules are an experimental feature in Lean.
To use modules, the {option}`experimental.module` must be set to {lean}`true` in the project's Lake configuration file.

{optionDocs experimental.module}

## Headers
%%%
tag := "module-headers"
%%%


Module headers list the modules that should be elaborated prior to the current module.
Their declarations are visible in the current module.

:::syntax Lean.Parser.Module.header -open (title := "Module Headers")
The module header consists of an optional {keywordOf Lean.Parser.Module.header}`module` keyword followed by a sequence of {deftech}[`import` statements]:
```grammar
$[module]?
$i:import*
```

The optional {keyword}`prelude` keyword should only be used in Lean's source code:
```grammar
$[module]?
prelude
$i:import*
```
:::

If present, the {keyword}`prelude` keyword indicates that the file is part of the implementation of the Lean {deftech}_prelude_, which is the code that is available without any explicit imports—it should not be used outside of Lean's implementation.

:::syntax Lean.Parser.Module.prelude -open (title := "Prelude Modules")
```grammar
prelude
```

:::

::::syntax Lean.Parser.Module.import (title := "Imports")
All {tech}[source files] may use plain imports:
```grammar
import $mod:ident
```

In source files that are not modules, this imports the specified Lean file.
Importing a file makes its contents available in the current source file, as well as those from source files transitively imported by its imports.

Source file names do not necessarily correspond to namespaces.
Source files may add names to any namespace, and importing a source file has no effect on the set of currently open namespaces.

The {tech}[import name] is translated to a filename by replacing dots (`'.'`) in its name with directory separators and appending `.lean` or `.olean`.
Lean searches its include path for the corresponding intermediate build product or importable module file.

{tech}[Modules] may use the following import syntax:
```grammar
$[public]? $[meta]? import $[all]? $mod:ident
```

:::paragraph
All imports to a module must themselves be modules.
The modifiers have the following meanings:

: {keyword}`public`

  The imported module's public scope is added to the current module's public scope and made available to the current module's importers.

: {keyword}`meta`

  The contents of the imported module are made available at the {tech}[meta phase] in the current module.

: {keyword}`all`

  The imported module's private scope is added to the current module's {tech}[private scope].
:::
::::

## Commands
%%%
tag := "commands"
%%%


{tech}[Commands] are top-level statements in Lean.
Some examples are inductive type declarations, theorems, function definitions, namespace modifiers like `open` or `variable`, and interactive queries such as `#check`.
The syntax of commands is user-extensible, and commands may even {ref "language-extension"}[add new syntax that is used to parse subsequent commands].
Specific Lean commands are documented in the corresponding chapters of this manual, rather than being listed here.

::: TODO
Make the index include links to all commands, then xref from here
:::

# Modules and Visibility
%%%
tag := "module-scopes"
%%%

:::paragraph
A {deftech}[module] is a source file that has opted in to a distinction between public and private information.
Lean ensures that private information can change without affecting clients that import only its public information.
This discipline brings a number of benefits:

: Much-improved average build times

  Changes to files that affect only non-exported information (e.g. proofs, comments, and docstrings) will not trigger rebuilds outside of these files.
  Even when dependent files have to be rebuilt, those files that cannot be affected (as determined by their {keywordOf Lean.Parser.Module.import}`import` annotations) can be skipped.

: Control over API evolution

  Library authors can trust that changes to non-exported information will not affect downstream users of their library.
  If only a function's signature is exposed, then downstream users cannot rely on definitional equalities that involve its unfolding; this means that the library's author is free to adopt a more efficient algorithm without unintentionally breaking client code.

: Avoiding accidental unfolding

  Limiting the scope in which definitions can be unfolded allows for avoiding both reductions that should be replaced by application of more specific theorems as well as unproductive reductions that were not in fact necessary.
  This improves the speed of proof elaboration.

: Smaller executables

  Separating compile-time and run-time code allows for more aggressive dead code elimination, guaranteeing that metaprograms such as tactics do not make it into the final binary.

: Reduced memory usage

  Excluding private information such as proofs from importing can improve Lean's memory use both while building and editing a project.
  Porting mathlib4 to the module system has shown savings close to 50% from this even before imports are further minimized.{TODO}[link and format of mathlib name consistent with rest of manual]
:::

:::paragraph
Modules contain two separate scopes: the {deftech}_public scope_ consists of information that is visible in modules that import a module, while the {deftech}_private scope_ consists of information that is generally visible only within the module.
Some examples of information that can be private or public include:

: Names

  Constants (such as definitions, inductive types, or constructors) may be private or public.
  A public constant's type may only refer to public names.

: Definitions

  A public definition may be {deftech}[exposed] or not.
  If a public definition is not exposed, then it cannot be unfolded in contexts that only have access to the public scope.
  Instead, clients must rely on the theorems about the definition that are provided in the public scope.
:::

Each declaration has default visibility rules.
Generally speaking, all names are private by default, unless defined in a {tech}[public section].
Even public names usually place the bodies of definitions in the private scope, and even proofs in exposed definitions are kept private.
The specific visibility rules for each declaration command are documented together with the declaration itself.

::::example "Private and Public Definitions"
:::leanModules +error
The module {module}`Greet.Create` defines a function {name}`greeting`.
Because there are no visibility modifiers, this function defaults to the {tech}[private scope]:
```leanModule (moduleName := Greet.Create)
module
def greeting (name : String) : String :=
  s!"Hello, {name}"
```
The definition of {name}`greeting` is not visible in the module {module}`Greet`, even though it imports {module}`Greet.Create`:
```leanModule (moduleName := Greet) (name := noRef)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2
```
```leanOutput noRef
Unknown identifier `greeting`
```
:::

:::leanModules
If {name}`greeting` is made public, then {name}`greetTwice` can refer to it:
```leanModule (moduleName := Greet.Create)
module
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
```leanModule (moduleName := Greet)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2
```
:::
::::

::::example "Exposed and Unexposed Definitions"
:::leanModules +error
The module {module}`Greet.Create` defines a public function {name}`greeting`.
```leanModule (moduleName := Greet.Create)
module
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
Although the definition of {name}`greeting` is visible in the module {module}`Greet`, it cannot be unfolded in a proof because the definition's body is in the {tech}[private scope] of {module}`Greet`:
```leanModule (moduleName := Greet) (name := nonExp)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2

theorem greetTwice_is_greet_twice {name1 name2 : String} :
    greetTwice name1 name2 = "Hello, " ++ name1 ++ "\n" ++ "Hello, " ++ name2 := by
  simp [greetTwice, greeting]
```
```leanOutput nonExp
Invalid simp theorem `greeting`: Expected a definition with an exposed body
```
:::

:::leanModules
Adding the {attrs}`@[expose]` attribute exposes the definition so that downstream modules can unfold {name}`greeting`:
```leanModule (moduleName := Greet.Create)
module
@[expose]
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
Now, the proof can proceed:
```leanModule (moduleName := Greet)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2

theorem greetTwice_is_greet_twice {name1 name2 : String} :
    greetTwice name1 name2 = "Hello, " ++ name1 ++ "\n" ++ "Hello, " ++ name2 := by
  simp [greetTwice, greeting, toString]
  grind [String.append_assoc]
```
:::
::::

:::::example "Proofs are Private"
::::leanModules
:::paragraph
In this module, the function {name}`incr` is public, but its implementation is not exposed:
```leanModule (moduleName := Main)
module

public def incr : Nat → Nat
  | 0 => 1
  | n + 1 => incr n + 1

public theorem incr_eq_plus1 : incr = (· + 1) := by
  funext n
  induction n <;> simp [incr, *]
```
:::

Nonetheless, the proof of the theorem {name}`incr_eq_plus1` can unfold its definition.
This is because proofs of theorems are in the private scope.
This is the case both for public and private theorems.
::::
:::::

The option {option}`backward.privateInPublic` can be used while transitioning from ordinary source files to modules.
When it is set to {lean}`true`, private definitions are exported, though their names are not accessible in importing modules.
However, references to them in the public part of their defining module are allowed.
Such references result in a warning unless the option {option}`backward.privateInPublic.warn` is set to {lean}`false`.
These warnings can be used to locate and eventually eliminate these references, allowing {option}`backward.privateInPublic` to be disabled.
Similarly, {option}`backward.proofsInPublic` causes proofs created with {keywordOf Lean.Parser.Term.by}`by` to be public, rather than private; this can enable {keywordOf Lean.Parser.Term.by}`by` to fill in metavariables in its expected type.
Most use cases for {option}`backward.proofsInPublic` also require that {option}`backward.privateInPublic` is enabled.

{optionDocs backward.privateInPublic}

{optionDocs backward.privateInPublic.warn}

{optionDocs backward.proofsInPublic}

::::example "Exporting Private Definitions"
:::leanModules
In the module {module}`L.Defs`, the public definition of {name}`f` refers to the private definition {name}`drop2` in its signature.
Because {option}`backward.privateInPublic` is {lean}`true`, this is allowed, resulting in a warning:
```leanModule (moduleName := L.Defs) (name := warnPub)
module

set_option backward.privateInPublic true

def drop2 (xs : List α) : List α := xs.drop 2

public def f (xs : List α) (transform : List α → List α:= drop2) : List α :=
  transform xs
```
```leanOutput warnPub
Private declaration `drop2` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled.

Disable `backward.privateInPublic.warn` to silence this warning.
```
When the module is imported, references to {name}`f` use {name}`drop2` as a default argument value; however, its name is inaccessible in the module {module}`L`:
```leanModule (moduleName :=  L) (name := withPrivateInTerm)
module
import L.Defs

def xs := [1, 2, 3]

set_option pp.explicit true in
#check f xs
```
```leanOutput withPrivateInTerm
@f Nat xs (@drop2✝ Nat) : List Nat
```
:::
::::

::::example "Proofs in Public"
:::leanModules
In the plain source file {module}`NotMod`, the definition of {name}`two` uses the content of the proof to fill out the numeric value in the definition by solving a {tech}`metavariable`:
```leanModule (moduleName := NotMod)
structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
:::
:::leanModules +error
Converting this file to a module results in an error, because the body of the definition is exposed in the public part but the proof is private and thus cannot change the public type:
```leanModule (moduleName := Mod) (name := proofMeta)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
```leanOutput proofMeta
tactic execution is stuck, goal contains metavariables
  ?m.3 + ?m.3 = ?m.5
```
:::
:::leanModules
Setting the option {option}`backward.proofsInPublic` causes the proof to be in the public part of the module so it can solve the metavariable:
```leanModule (moduleName := Mod)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

set_option backward.proofsInPublic true in
abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
:::

:::leanModules
However, it is typically better style to reformulate the definition so that the proof has a complete goal:
```leanModule (moduleName := Mod)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two : Half 4 := Half.mk 2 <| by
  rfl
```
:::
::::


The private scope of a module may be imported into another module using the {keywordOf Lean.Parser.Module.import}`all` modifier.
By default, this is only allowed if the imported module and the current module are from the same Lake {tech}[package], as its main purpose is to allow for separating definitions and proofs into separate modules for internal organization of a library.
The Lake package or library option {ref "Lake.PackageConfig allowImportAll" (domain := Manual.lakeTomlField)}`allowImportAll` can be set to allow other packages to access to the current package's private scopes via {keywordOf Lean.Parser.Module.import}`import all`.
The imported private scope includes private imports of the imported module, including nested {keywordOf Lean.Parser.Module.import}`import all`s.
As a consequence, the set of private scopes accessible to the current module is the transitive closure of {keywordOf Lean.Parser.Module.import}`import all` declarations.

The module system's {keywordOf Lean.Parser.Module.import}`import all` is more powerful than {keywordOf Lean.Parser.Module.import}`import` without the module system.
It makes imported private definitions accessible directly by name, as if they were defined in the current module.
A secondary use case for {keywordOf Lean.Parser.Module.import}`import all` is to access code in multiple modules within a library that should nonetheless not be provided to downstream consumers, as well as to allow tests to access information that is not part of the public API.

::::example "Importing Private Information"
:::leanModules (moduleRoot := Tree) +error
This library separates a module of definitions from a module of lemmas.
This is a common pattern in Lean code.
```leanModule (moduleName := Tree.Basic)
module

public inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

public def Tree.count : Tree α → Nat
  | .leaf => 0
  | .branch left _ right => left.count + 1 + right.count
```
However, because {name}`Tree.count` is not exposed, the proof in the lemma file cannot unfold it:
```leanModule (moduleName := Tree.Lemmas) (name := lemmasNoAll)
module
public import Tree.Basic
theorem Tree.count_leaf_eq_zero : count (.leaf : Tree α) = 0 := by
  simp [count]
```
```leanOutput lemmasNoAll
Invalid simp theorem `count`: Expected a definition with an exposed body
```
:::

:::leanModules (moduleRoot := Tree)
Importing the private scope from {module}`Tree.Basic` into the lemma module allows the definition to be unfolded in the proof.
```leanModule (moduleName := Tree.Basic)
module

public inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

public def Tree.count : Tree α → Nat
  | .leaf => 0
  | .branch left _ right => left.count + 1 + right.count
```
```leanModule (moduleName := Tree.Lemmas)
module
import all Tree.Basic
public import Tree.Basic
theorem Tree.count_leaf_eq_zero : count (.leaf : Tree α) = 0 := by
  simp [count]
```
:::
::::


## The Meta Phase
%%%
tag := "meta-phase"
%%%

Definitions in Lean result in both a representation in the type theory that is designed for formal reasoning and a compiled representation that is designed for execution.
This compiled representation is used to generate machine code, but it can also be executed directly using an interpreter.
The code runs during {tech}[elaboration], such as {ref "tactics"}[tactics] or {ref "macros"}[macros], is the compiled form of definitions.
If this compiled representation changes, then any code created by it may no longer be up to date, and it must be re-run.
Because the compiler performs non-trivial optimizations, changes to any definition in the transitive dependency chain of a function could in principle invalidate its compiled representation.
This means that metaprograms exported by modules induce a much stronger coupling than ordinary definitions.
Furthermore, metaprograms run _during_ the construction of ordinary terms; thus, they must be fully defined and compiled before use.
After all, a function definition without a body cannot be run.
The time at which metaprograms are run is referred to as the {deftech}_metaprogramming phase_, frequently just called the {deftech}_meta phase_.

Just as they distinguish between public and private information, modules additionally distinguish code that is available in the meta phase from ordinary code.
Any declaration used as an entry point to compile-time execution has to be tagged with the {keywordOf Lean.Parser.Module.import}`meta` modifier, which indicates that the declaration is available for use as a metaprogram.
This is automatically done in built-in metaprogramming syntax such as {keywordOf Lean.Parser.Command.syntax}`syntax`, {keywordOf Lean.Parser.Command.macro}`macro`, and {keywordOf Lean.Parser.Command.elab}`elab` but may need to be done explicitly when manually applying metaprogramming attributes such as {keyword}`app_delab` or when defining helper declarations.
A {keywordOf Parser.Command.declModifiers}`meta` definition may only access (and thus invoke) other {keywordOf Parser.Command.declModifiers}`meta` definitions in execution-relevant positions; a non-{keywordOf Parser.Command.declModifiers}`meta` definition likewise may only access other non-{keywordOf Parser.Command.declModifiers}`meta` definitions.

::::example "Meta Definitions"
:::leanModules +error
In this module, the helper function {name}`revArrays` reverses the order of the elements in each array literal in a term.
This is called by the macro {keyword}`rev!`.
```leanModule (moduleName := Main) (name := nonMeta)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

partial def revArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$((xs : Array Term).reverse),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM revArrays)⟩
    | _ => pure ⟨other⟩

macro "rev!" e:term : term => do
  revArrays e
```
The error message indicates that {name}`revArrays` cannot be used from the macro because it is not defined in the module's {tech}[metaprogramming phase]:
```leanOutput nonMeta
Invalid `meta` definition `_aux___macroRules_termRev!__1`, `revArrays` not marked `meta`
```
:::
:::leanModules
Marking {name}`revArrays` with the {keywordOf Lean.Parser.Command.declModifiers}`meta` modifier allows the macro definition to call it:
```leanModule (moduleName := Main) (name := withMeta)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta partial def revArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$((xs : Array Term).reverse),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM revArrays)⟩
    | _ => pure ⟨other⟩

macro "rev!" e:term : term => do
  revArrays e

#eval rev! #[1, 2, 3]
```
```leanOutput withMeta
#[3, 2, 1]
```
:::
::::

Libraries that were not originally part of the meta phase can be brought into it by importing a module with {keywordOf Parser.Module.import}`meta import`.
When a module is imported at the meta phase, all of its definitions are made available at that phase, whether or not they were marked {keywordOf Parser.Command.declModifiers}`meta`.
There is no meta-meta phase.
In addition to making the imported module's public contents available at the meta phase, {keywordOf Parser.Module.import}`meta import` indicates that the current module should be rebuilt if the compiled representation of the imported module changes, ensuring that modified metaprograms are re-run.
If a definition should be usable in both phases, then it must be defined in a separate module and imported at both phases.

::::example "Cross-Phase Code Reuse"
:::leanModules +error
In this module, the function {name}`toPalindrome` is defined in the meta phase, which allows it to be used in a macro but not in an ordinary definition:
```leanModule (moduleName := Phases) (name := bothPhases)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta def toPalindrome (xs : Array α) : Array α := xs ++ xs.reverse

meta partial def palArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$(toPalindrome (xs : Array Term)),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM palArrays)⟩
    | _ => pure ⟨other⟩

macro "pal!" e:term : term => do
  palArrays e

#check pal! (#[1, 2, 3] ++ [6, 7, 8])

public def colors := toPalindrome #["red", "green", "blue"]
```
```leanOutput bothPhases
Invalid definition `colors`, may not access declaration `toPalindrome` marked as `meta`
```
:::
:::leanModules
Moving {name}`toPalindrome` to its own module, {module}`Phases.Pal`, allows this module to be imported at both phases:
```leanModule (moduleName := Phases.Pal)
module

public def toPalindrome (xs : Array α) : Array α := xs ++ xs.reverse
```
```leanModule (moduleName := Phases) (name := bothPhases)
module

meta import Phases.Pal
import Phases.Pal

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta partial def palArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$(toPalindrome (xs : Array Term)),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM palArrays)⟩
    | _ => pure ⟨other⟩

local macro "pal!" e:term : term => do
  palArrays e

#check pal! (#[1, 2, 3] ++ [6, 7, 8])

public def colors := toPalindrome #["red", "green", "blue"]
```
If the macro {keyword}`pal!` were public (that is, if it was not declared with the {keyword}`local` modifier) then the {keywordOf Lean.Parser.Module.import}`meta import` of {module}`Phases.Pal` would need to be declared {keywordOf Lean.Parser.Module.import}`public` as well.
:::
::::

In addition, the import must be public if the imported definition may be executed at compile time outside the current module, i.e. if it is reachable from some public {keywordOf Parser.Command.declModifiers}`meta` definition in the current module.
Use {keywordOf Parser.Module.import}`public meta import`.
If the declaration is already declared {keywordOf Parser.Command.declModifiers}`meta`, then {keywordOf Parser.Module.import}`public import` is sufficient.

Unlike definitions, most metaprograms are public by default.
Thus, most {keywordOf Lean.Parser.Module.import}`meta import` are also {keywordOf Parser.Module.import}`public` in practice.
The exception is when a definition is imported solely for use in local metaprograms, such as those declared with {keywordOf Parser.Command.syntax}`local syntax`, {keywordOf Parser.Command.macro}`local macro`, or {keywordOf Parser.Command.elab}`local elab`.

As a guideline, it is usually preferable to keep the amount of {keywordOf Lean.Parser.Command.declModifiers}`meta` annotations as small as possible.
This avoids locking otherwise-reusable declarations into the {tech}[meta phase] and it helps the build system avoid more rebuilds.
Thus, when a metaprogram depends on other code that does not itself need to be marked {keywordOf Lean.Parser.Command.declModifiers}`meta`, this other code should be placed in a separate module and not marked {keywordOf Lean.Parser.Command.declModifiers}`meta`.
Only the final module that actually registers a metaprogram needs the helpers to be in the meta phase.
This module should use {keywordOf Lean.Parser.Module.import}`public meta import` to import those helpers and then define its metaprograms using built-in syntax like {keywordOf Parser.Command.elab}`elab`, using {keywordOf Lean.Parser.Command.declaration}`meta def`, or using {keywordOf Lean.Parser.Command.section}`meta section`.


# Elaborated Modules
%%%
tag := "module-contents"
%%%

When Lean elaborates a source file, the result is an {tech}[environment].
The environment includes the constants, {tech}[inductive types], {tech}[theorems], {tech (key := "type class")}[type classes], {tech}[instances], and everything else declared in the file, along with side tables that track data as diverse as {tech}[simp sets], namespace aliases, and {tech}[documentation comments].
If the file contains a module, then the environment additionally tracks which information is public and private, and the phase at which definitions are available.

As the source file is processed by Lean, commands add content to the environment.
After elaboration, the environment is serialized to a {deftech (key:="olean")}[`.olean` file], which contains both the environment and a compacted heap region with the run-time objects needed by the environment.
This means that an imported source file can be loaded without re-executing all of its commands.
Environments that result from elaborating modules are serialized into three {tech (key:="olean")}[`.olean` files], containing the private, public, and server information in the environment.
The server information consists of data such as API documentation and source positions of definitions that is only needed when using the Lean language server and does not need to be loaded along with the public information in other contexts.

# Module System Errors and Patterns

:::paragraph
The following list contains common errors one might encounter when using the module system and especially porting existing files to the module system:

: Unknown constant errors

  Check whether a private definition is being accessed in the {tech}[public scope].
  If so, the problem can be solved by making the current declaration private as well, or by placing the reference into the private scope using the {keywordOf Lean.Parser.Term.structInstFieldDef}`private` modifier on a field or {keywordOf Lean.Parser.Term.by}`by` for a proof.

: Definitional equality errors, especially after porting

  Failures of expected definitional equalities are usually due to a missing {attr}`expose` attribute on a definition or alternatively, if imported, an {keywordOf Lean.Parser.Module.import}`import all`.
  Prefer the former if anyone outside your library might feasibly require the same access.
  The error message should list non-exposed definitions that could not be unfolded.
  This may also appear as a kernel error when a tactic directly emits proof terms that reference specific declarations without going through the elaborator, such as for proof by reflection.
  In this case, there is no readily available trace for debugging; consider using {attrs}`@[expose]`‍` `{keywordOf Parser.Command.section}`section`s generously on the closure of relevant modules.

:::

## Recipe for Porting Existing Files

:::paragraph
To gain the benefits of the module system, source files must be made into modules.
Start by enabling the module system throughout all files with minimal breaking changes:
1. Prefix all files with {keywordOf Lean.Parser.Module.header}`module`.
2. Make all existing imports {keywordOf Lean.Parser.Command.declModifiers}`public` unless they will be used only in proofs.
 * Add {keywordOf Lean.Parser.Module.import}`import all` when errors that mention references to private data occur.
 * Add {keywordOf Lean.Parser.Module.import}`public meta import` when errors that mention “must be {keywordOf Lean.Parser.Module.import}`meta`” occur.
   The {keywordOf Lean.Parser.Module.import}`public` may be omitted when defining local-only metaprograms.
3. Prefix the remainder of the file with `@[expose] public section` or, for programming-focused files, with {keywordOf Lean.Parser.Command.section}`public section`.
   The latter should be used for programs that will be run but not reasoned about.
:::

After an initial build under the module system succeeds, the dependencies between modules can be iteratively minimized.
In particular, removing uses of {keywordOf Lean.Parser.Command.declModifiers}`public` and {attrs}`@[expose]` will help avoid unnecessary rebuilds.

# Packages, Libraries, and Targets
%%%
tag := "code-distribution"
%%%


Lean modules are organized into {deftech}_packages_, which are units of code distribution.
A {tech}[package] may contain multiple libraries or executables.

Code in a package that is intended for use by other Lean packages is organized into {deftech (key:="library")}[libraries].
Code that is intended to be compiled and run as independent programs is organized into {deftech (key:="executable")}[executables].
Packages, libraries, and executables are described in detail in the section on {ref "lake"}[Lake, the standard Lean build tool].
