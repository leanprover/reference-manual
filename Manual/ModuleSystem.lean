/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich
-/

import VersoManual
import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.typography.quotes true

#doc (Manual) "The Module System" =>
%%%
number := false
tag := "module-system"
%%%

The module system is an experimental feature that allows for more fine-grained control over what information is exported from, and imported into, Lean files.

The main benefits of doing so are:

: Average build times

  Changes to files that affect only non-exported information (e.g. proofs) will not trigger rebuilds outside of these files.
  Even when dependent files have to be rebuilt, those files that cannot be affected according to the {keywordOf Lean.Parser.Module.import}`import` annotations can be skipped.

: API evolution

  Library authors can trust that changes to non-exported information will not affect downstream users of their library.

: Avoiding accidental unfolding

  Limiting the scope in which definitions can be unfolded allows for avoiding both reductions that should be replaced by application of more specific theorems as well as unproductive reductions that were not in fact necessary.

: Smaller executables

  Separating compile-time and run-time code allows for more aggressive dead code elimination.

The module system is activated by prefixing a Lean file with the {keywordOf Lean.Parser.Module.header}`module` keyword.
{keywordOf Lean.Parser.Module.header}`module`s can only import other {keywordOf Lean.Parser.Module.header}`module`s so adoption has to be done top-down.
Non-{keywordOf Lean.Parser.Module.header}`module`s can import {keywordOf Lean.Parser.Module.header}`module`s and will ignore all module-system-specific annotations.

At the time of writing, the module system is considered experimental and additionally guarded by the {option}`experimental.module` option that has to be set to {lean}`true` in the project's Lake configuration file.
Of libraries shipped with Lean, only {module}`Init` is currently fully ported.
The language semantics described below are close to final, but not all benefits described above are implemented yet.

# Visibility

The main distinction the module system introduces is between the {deftech}_public scope_ that contains all information visible to other modules via {keywordOf Parser.Module.import}`import` and the {deftech}_private scope_ that is not imported by default.
Both declarations and imports themselves are scoped in this way.

The default scope is private.
The new modifier {keywordOf Lean.Parser.Module.import}`public` before a declaration or import puts it into the public scope instead.
No information from the private scope can be used in the public scope to ensure information in the latter still makes sense when only it is imported into other modules.

```leanModule +error (name := priva)
module

import all Lean.Elab

def priv : Nat := 0

public abbrev pub : Nat := priv
```
```leanOutput priva
Unknown identifier `priv`

Note: A private declaration `priv` (from the current module) exists but would need to be public to access here.
```

{keywordOf Lean.Parser.Command.section}`public section` can be used to switch the default scope for declarations, with {keywordOf Lean.Parser.Command.declModifiers}`private` locally negating it.
This is mostly intended to ease porting while avoiding merge conflicts.

Marking a declaration as public at minimum makes its “signature”, i.e. its name and type, visible.
Some specific declarations/terms may still put other parts in the private scope as follows:
* {keywordOf Parser.Term.by}`by` used in the public scope to prove a proposition puts the resulting proof in the private scope (by wrapping it in a public helper theorem).
* {keywordOf Parser.Command.declaration}`def` puts its body in the private scope by default. The defined constant cannot be unfolded when used in the public scope.
  This can be changed with the {attrs}`@[expose]` attribute.
  {attrs}`@[expose]`‍` `{keywordOf Lean.Parser.Command.section}`section` can be used to apply the attribute to all {keywordOf Lean.Parser.Command.declaration}`def`s in the section and can locally be negated by {attrs}`@[no_expose]`.
* {keywordOf Lean.Parser.Command.declaration}`theorem` and {keywordOf Lean.Parser.Command.declaration}`opaque` never expose their body.
  Consider using {attrs}`@[expose]`‍` `{keywordOf Parser.Command.declaration}`def` instead if exposition is absolutely necessary.
* {keywordOf Lean.Parser.Command.declaration}`abbrev` and {keywordOf Lean.Parser.Command.declaration}`instance` always expose their body.
  For {keywordOf Parser.Command.instance}`instance`, individual field values can be marked {keywordOf Lean.Parser.Term.structInstFieldDef}`private`, which can be useful for programming purposes.
  For proof fields, {keywordOf Parser.Term.by}`by` already does the trick.
  ```leanModule
  module

  def myInternalHelper (x : Nat) : String := s!"It is {x}!"

  public instance : ToString Nat where
    toString x := private myInternalHelper x
  ```

## Import Visibility

The basic form {import}`public import M` makes the public scope of {module}`M` available in the public scope of the current module. The private scope of {module}`M` is discarded.
Without {keywordOf Lean.Parser.Module.import}`public`, the public scope of {module}`M` is instead imported into the {tech}[private scope].
The import thus is irrelevant to downstream modules and ignored by them.

{import}`import all M` behaves like {import}`import M` but additionally imports the private scope of {module}`M` into the private scope of the current module.
This is only allowed if {module}`M` and the current module have the same module name root, as its main purpose is to allow for separating definitions and proofs into separate modules for internal organization of a library.
:::leanModules (moduleRoot := M)
```leanModule (moduleName := M.Defs)
-- Module M.Defs
module

public def f : Nat := 0
```
```leanModule (moduleName := M.Lemmas)
-- Module M.Lemmas
module

public import M.Defs
import all M.Defs

public theorem f_eq_zero : f = 0 := by
  -- may access body of `f` imported into the private scope
  rfl
```
:::
Note that the imported private scope includes private {keywordOf Lean.Parser.Module.import}`import`s of {module}`M`, including nested {keywordOf Lean.Parser.Module.import}`import all`s that then are interpreted likewise.
That is, the set of private scopes accessible to the current module is the transitive closure of {keywordOf Lean.Parser.Module.import}`import all` declarations.

The module system's {keywordOf Lean.Parser.Module.import}`import all` is more powerful than {keywordOf Lean.Parser.Module.import}`import` without the module system.
It makes imported private definitions accessible directly by name, as if they were defined in the current module.
Thus another use case of {keywordOf Lean.Parser.Module.import}`import all` is to make declarations available that need to be used in multiple modules but should not leak outside the current library.

# The `meta` Phase

When it comes to actual code execution, there is no point to a definition without a body.
Thus, in order to eagerly know what definitions _might_ be executed at compile time and so need to be available including their bodies (in some executable shape), any definition used as an entry point to compile-time execution has to be tagged with the new {keywordOf Lean.Parser.Module.import}`meta` modifier.
This is automatically done in built-in metaprogramming syntax such as {keywordOf Lean.Parser.Command.syntax}`syntax`, {keywordOf Lean.Parser.Command.macro}`macro`, and {keywordOf Lean.Parser.Command.elab}`elab` but may need to be done explicitly when manually applying metaprogramming attributes such as {keyword}`app_delab`.

A {keywordOf Parser.Command.declModifiers}`meta` definition may only access (and thus invoke) other {keywordOf Parser.Command.declModifiers}`meta` definitions; a non-{keywordOf Parser.Command.declModifiers}`meta` definition likewise may only access other non-{keywordOf Parser.Command.declModifiers}`meta` definitions.
For imported definitions, the {keywordOf Parser.Command.declModifiers}`meta` marker can be added after the fact using {keywordOf Parser.Module.import}`meta import`.
{keywordOf Parser.Module.import}`meta import`ing a definition already in the meta phase leaves it in that phase.
In addition, the import must be public if the imported definition may be compile-time executed outside the current module, i.e. if it is reachable from some public {keywordOf Parser.Command.declModifiers}`meta` definition in the current module: use {keywordOf Parser.Module.import}`public meta import` or, if already {keywordOf Parser.Command.declModifiers}`meta`, {keywordOf Parser.Module.import}`public import`.
This is usually the case, unless a definition was imported solely for use in local metaprograms such as {keywordOf Parser.Command.syntax}`local syntax`/{keywordOf Parser.Command.macro}`macro`/{keywordOf Parser.Command.elab}`elab`/....
```leanModule
module
import Lean
public import Lean.Elab.Command
meta import Std.Data.HashMap

local elab "my_elab" : command => do
  let m : Std.HashMap String Nat := {}
  Lean.logInfo m!"This should be empty: {m.keys}"
```

For convenience, {keywordOf Lean.Parser.Command.declModifiers}`meta` also implies {keywordOf Lean.Parser.Command.declModifiers}`partial`.
This can be overridden by giving an explicit {keywordOf Lean.Parser.Command.declaration}`termination_by` metric (such as one suggested by {keywordOf Lean.Parser.Command.declaration}`termination_by?`), which may be necessary when the type of the definition is not known to be {name}`Nonempty`.

As a guideline, it is usually preferable to keep the amount of {keywordOf Lean.Parser.Command.declModifiers}`meta` annotations as small as possible.
This avoids locking otherwise-reusable declarations into the meta phase and it helps the build system avoid more rebuilds.
Thus, when a metaprogram depends on other code that does not itself need to be marked {keywordOf Lean.Parser.Command.declModifiers}`meta`, this other code should be located in a separate module and not marked {keywordOf Lean.Parser.Command.declModifiers}`meta`.
Only the final module that actually registers a metaprogram needs the helpers as {keywordOf Lean.Parser.Module.import}`meta` definitions.
It should use {keywordOf Lean.Parser.Module.import}`public meta import` to import those helpers and then define its metaprograms using built-in syntax like {keywordOf Parser.Command.elab}`elab`, using {keywordOf Lean.Parser.Command.declaration}`meta def`, or using {keywordOf Lean.Parser.Command.section}`meta section`.

# Common Errors and Patterns

The following list contains common errors one might encounter when using the module system and especially porting existing files to the module system.

: Unknown constant

  Check whether you might be trying to access a private definition in the public scope.
  If so, you might want to make the current declaration private as well or otherwise enter the private scope such as through {keywordOf Lean.Parser.Term.structInstFieldDef}`private` on a field or {keywordOf Lean.Parser.Term.by}`by` for a proof.
  TODO: improve error message.

  If the message is prefixed with `(interpreter)`, this suggests a missing {keywordOf Lean.Parser.Module.import}`meta import`.
  The new import should be placed in the file defining the metaprogram depending on the missing constant, which is not necessarily the file triggering the error.
  Note that the language server always does {keywordOf Lean.Parser.Module.import}`meta import`s for the benefit of {keywordOf Lean.Parser.Command.eval}`#eval` etc., so the error might only occur in a cmdline build.
  TODO: better, static `meta` checking.

: Definitional equality errors, especially after porting

  You are likely missing an {attr}`expose` attribute on a definition or alternatively, if imported, an {keywordOf Lean.Parser.Module.import}`import all`.
  Prefer the former if anyone outside your library might feasible require the same access.
  {keywordOf Lean.reduceCmd}`#reduce` and/or {option}`trace.Meta.isDefEq` can help with finding the blocking definition.
  You might also see this as a kernel error when a tactic directly emits proof terms referencing specific declarations without going through the elaborator, such as for proof by reflection.
  In this case, there is no readily available trace for debugging; consider using {attrs}`@[expose]`‍` `{keywordOf Parser.Command.section}`section`s generously on the closure of relevant modules.

: “failed to compile 'partial' definition” on {keywordOf Lean.Parser.Command.declModifiers}`meta` definition

  This can happen when a definition with a type that is not known to be {name}`Nonempty` is marked {keywordOf Lean.Parser.Command.declModifiers}`meta` or moved into a {keywordOf Parser.Command.section}`meta section`, which both imply {keywordOf Lean.Parser.Command.declModifiers}`partial` without a termination metric.
  Use {keywordOf Parser.Command.declaration}`termination_by?` to make the previously implicitly inferred termination metric explicit, or provide a {name}`Nonempty` instance.

## Recipe for Porting Existing Files

Start by enabling the module system throughout all files with minimal breaking changes:
* Prefix all files with {keywordOf Lean.Parser.Module.header}`module`.
* Make all existing imports {keywordOf Lean.Parser.Command.declModifiers}`public` unless you know they will be used only in proofs.
  Add {keywordOf Lean.Parser.Module.import}`import all` when getting errors about references to private data.
  Add {keywordOf Lean.Parser.Module.import}`public meta import` when getting “must be {keywordOf Lean.Parser.Module.import}`meta`” errors ({keywordOf Lean.Parser.Module.import}`public` may be avoided when defining local-only metaprograms).
* Prefix the remainder of the file with `@[expose] public section` or, for programming-focused files, with {keywordOf Lean.Parser.Command.section}`public section`.

After getting an initial build under the module system to work, you can then work iteratively on minimizing uses of {keywordOf Lean.Parser.Command.declModifiers}`public` and {attrs}`@[expose]` where sensible.
